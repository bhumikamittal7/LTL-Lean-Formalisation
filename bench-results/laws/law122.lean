import LTL

open LTL

-- LTL law 122: □ ((p ⇒ q) ∧ (q ⇒ ◇ r) ∧ (r ⇒ s)) ⟹ (p ⇒ ◇ s)
-- (the proposer's answer starts at line 9)

namespace Candidate
theorem cand_h1 {AP : Type} (p q r s : Formula AP) :
    [r] ⊢ [(𝐆 (((p ⇒ q) ⋏ ((q ⇒ 𝐅 (r)) ⋏ (r ⇒ s)))) ⇒ 𝐅 (s))] :=
  Derives.impR (A := 𝐆 (((p ⇒ q) ⋏ ((q ⇒ 𝐅 (r)) ⋏ (r ⇒ s))))) (B := 𝐅 (s)) (by simp) <|
  Derives.alwaysL (A := ((p ⇒ q) ⋏ ((q ⇒ 𝐅 (r)) ⋏ (r ⇒ s)))) (by simp) <|
  Derives.andL (A := (p ⇒ q)) (B := ((q ⇒ 𝐅 (r)) ⋏ (r ⇒ s))) (by simp) <|
  Derives.andL (A := (q ⇒ 𝐅 (r))) (B := (r ⇒ s)) (by simp) <|
  Derives.impL (A := r) (B := s) (by simp)
    (Derives.ax (A := r) (by simp) (by simp)) <|
  Derives.evR (A := s) (by simp)
    (Derives.ax (A := s) (by simp) (by simp))

theorem cand_h2 {AP : Type} (p q r s : Formula AP) :
    [𝐗 ((𝐆 (((p ⇒ q) ⋏ ((q ⇒ 𝐅 (r)) ⋏ (r ⇒ s)))) ⇒ 𝐅 (s)))] ⊢
      [(𝐆 (((p ⇒ q) ⋏ ((q ⇒ 𝐅 (r)) ⋏ (r ⇒ s)))) ⇒ 𝐅 (s))] :=
  Derives.impR (A := 𝐆 (((p ⇒ q) ⋏ ((q ⇒ 𝐅 (r)) ⋏ (r ⇒ s))))) (B := 𝐅 (s)) (by simp) <|
  Derives.alwaysL (A := ((p ⇒ q) ⋏ ((q ⇒ 𝐅 (r)) ⋏ (r ⇒ s)))) (by simp) <|
  Derives.evR (A := s) (by simp) <|
  Derives.step
    (Γ' := [(𝐆 (((p ⇒ q) ⋏ ((q ⇒ 𝐅 (r)) ⋏ (r ⇒ s)))) ⇒ 𝐅 (s)),
            𝐆 (((p ⇒ q) ⋏ ((q ⇒ 𝐅 (r)) ⋏ (r ⇒ s))))])
    (B := 𝐅 (s))
    (Derives.impL (A := 𝐆 (((p ⇒ q) ⋏ ((q ⇒ 𝐅 (r)) ⋏ (r ⇒ s))))) (B := 𝐅 (s)) (by simp)
      (Derives.ax (A := 𝐆 (((p ⇒ q) ⋏ ((q ⇒ 𝐅 (r)) ⋏ (r ⇒ s))))) (by simp) (by simp))
      (Derives.ax (A := 𝐅 (s)) (by simp) (by simp)))
    (by simp) (by simp)

theorem candidate {AP : Type} (p q r s : Formula AP) :
    [𝐆 (((p ⇒ q) ⋏ ((q ⇒ 𝐅 (r)) ⋏ (r ⇒ s))))] ⊢ [(p ⇒ 𝐅 (s))] :=
  Derives.impR (A := p) (B := 𝐅 (s)) (by simp) <|
  Derives.alwaysL (A := ((p ⇒ q) ⋏ ((q ⇒ 𝐅 (r)) ⋏ (r ⇒ s)))) (by simp) <|
  Derives.andL (A := (p ⇒ q)) (B := ((q ⇒ 𝐅 (r)) ⋏ (r ⇒ s))) (by simp) <|
  Derives.andL (A := (q ⇒ 𝐅 (r))) (B := (r ⇒ s)) (by simp) <|
  Derives.impL (A := p) (B := q) (by simp)
    (Derives.ax (A := p) (by simp) (by simp)) <|
  Derives.impL (A := q) (B := 𝐅 (r)) (by simp)
    (Derives.ax (A := q) (by simp) (by simp)) <|
  Derives.evL (A := r)
    (I := (𝐆 (((p ⇒ q) ⋏ ((q ⇒ 𝐅 (r)) ⋏ (r ⇒ s)))) ⇒ 𝐅 (s))) (by simp)
    (cand_h1 p q r s) (cand_h2 p q r s) <|
  Derives.impL (A := 𝐆 (((p ⇒ q) ⋏ ((q ⇒ 𝐅 (r)) ⋏ (r ⇒ s))))) (B := 𝐅 (s)) (by simp)
    (Derives.ax (A := 𝐆 (((p ⇒ q) ⋏ ((q ⇒ 𝐅 (r)) ⋏ (r ⇒ s))))) (by simp) (by simp))
    (Derives.ax (A := 𝐅 (s)) (by simp) (by simp))

end Candidate

theorem verified {AP : Type} (p q r s : Formula AP) :
    [𝐆 (((p ⇒ q) ⋏ ((q ⇒ 𝐅 (r)) ⋏ (r ⇒ s))))] ⊢ [(p ⇒ 𝐅 (s))] :=
  Candidate.candidate p q r s

#print axioms verified
