"""LTL laws from the catalogue of Warford, Vega, and Staley (ACM Computing
Surveys 53(3), 2020), as benchmark problems for the propose-check loop.

`laws.json` holds the statements in the catalogue's notation, keyed by the
catalogue number:  ◯ □ ◇ U ¬ ∧ ∨ ⇒ ≡ ⊤ ⊥, with `A ⟹ B` (every trace that
satisfies A satisfies B) and `A ≈ B` (both directions). Precedence, tightest
first: prefix ◯ □ ◇ ¬; U; ∧; ∨; ⇒; ≡; ≈; ⟹. U, ∧, ∨, ⇒, ≡ associate to the
right.

This module parses a statement and produces
  * the Lean goal, for arbitrary formulas `p q r : Formula AP`;
  * a Python evaluator, used to check every law on all small lasso traces
    before it enters the benchmark (a guard against transcription errors).
"""

import itertools
import json
import pathlib
import re

HERE = pathlib.Path(__file__).resolve().parent
BIN = {"U": (79, "R"), "∧": (80, "R"), "∨": (85, "R"), "⇒": (86, "R"),
       "≡": (89, "R"), "≈": (90, "N"), "⟹": (99, "R")}
PREFIX = {"¬", "◯", "□", "◇"}


def tokenize(s):
    toks = re.findall(r"[pqrs]|⊤|⊥|U|[¬◯□◇∧∨⇒≡≈⟹()]", s)
    if "".join(toks) != re.sub(r"\s+", "", s):
        raise ValueError(f"cannot tokenize {s!r}")
    return toks


def parse(s):
    toks = tokenize(s)
    pos = 0

    def atom():
        nonlocal pos
        t = toks[pos]
        pos += 1
        if t in PREFIX:
            return (t, atom())
        if t == "(":
            e = expr(1000)
            assert toks[pos] == ")"
            pos += 1
            return e
        assert t in "pqrs⊤⊥", t
        return (t,)

    def expr(maxlvl):
        nonlocal pos
        lhs = atom()
        while pos < len(toks) and toks[pos] in BIN:
            op = toks[pos]
            lvl, assoc = BIN[op]
            if lvl > maxlvl:
                break
            pos += 1
            rhs = expr(lvl if assoc == "R" else lvl - 1)
            lhs = (op, lhs, rhs)
        return lhs

    e = expr(1000)
    assert pos == len(toks), (s, toks[pos:])
    return e


def to_lean(e):
    op = e[0]
    if op in "pqrs":
        return op
    if op == "⊤":
        return "⊤ₗ"
    if op == "⊥":
        return "⊥ₗ"
    if op == "¬":
        return f"∼({to_lean(e[1])})"
    if op in "◯□◇":
        return {"◯": "𝐗", "□": "𝐆", "◇": "𝐅"}[op] + f" ({to_lean(e[1])})"
    a, b = to_lean(e[1]), to_lean(e[2])
    if op == "≡":
        return f"(({a} ⇒ {b}) ⋏ ({b} ⇒ {a}))"
    return f"({a} {dict(U='𝐔', **{'∧': '⋏', '∨': '⋎', '⇒': '⇒'})[op]} {b})"


def goal(e):
    """The Lean statement of a law `A ⟹ B` or `A ≈ B`."""
    op, a, b = e
    A, B = to_lean(a), to_lean(b)
    if op == "⟹":
        return f"[{A}] ⊢ [{B}]"
    assert op == "≈"
    return f"([{A}] ⊢ [{B}]) ∧ ([{B}] ⊢ [{A}])"


def variables(e):
    out = set()
    def go(x):
        if x[0] in "pqrs":
            out.add(x[0])
        for y in x[1:]:
            go(y)
    go(e)
    return sorted(out)


# ---- semantic check on lasso traces ----------------------------------------

def holds(e, tr, loop, i):
    n = len(tr)
    nxt = lambda j: j + 1 if j + 1 < n else loop
    def suffix(j):
        seen = []
        while j not in seen:
            seen.append(j)
            j = nxt(j)
        return seen
    op = e[0]
    if op in "pqrs":
        return op in tr[i]
    if op == "⊤":
        return True
    if op == "⊥":
        return False
    if op == "¬":
        return not holds(e[1], tr, loop, i)
    if op == "◯":
        return holds(e[1], tr, loop, nxt(i))
    if op == "□":
        return all(holds(e[1], tr, loop, j) for j in suffix(i))
    if op == "◇":
        return any(holds(e[1], tr, loop, j) for j in suffix(i))
    a, b = e[1], e[2]
    if op == "∧":
        return holds(a, tr, loop, i) and holds(b, tr, loop, i)
    if op == "∨":
        return holds(a, tr, loop, i) or holds(b, tr, loop, i)
    if op == "⇒":
        return (not holds(a, tr, loop, i)) or holds(b, tr, loop, i)
    if op == "≡":
        return holds(a, tr, loop, i) == holds(b, tr, loop, i)
    if op == "U":
        for j in suffix(i):
            if holds(b, tr, loop, j):
                return True
            if not holds(a, tr, loop, j):
                return False
        return False
    raise ValueError(op)


def valid_on_small_traces(e, atoms="pqr", maxlen=4):
    op, a, b = e
    vals = [frozenset(c) for k in range(len(atoms) + 1) for c in itertools.combinations(atoms, k)]
    for n in range(1, maxlen + 1):
        for tr in itertools.product(vals, repeat=n):
            for loop in range(n):
                for i in range(n):
                    x, y = holds(a, tr, loop, i), holds(b, tr, loop, i)
                    if (op == "⟹" and x and not y) or (op == "≈" and x != y):
                        return False
    return True


def load():
    return json.loads((HERE / "laws.json").read_text())
