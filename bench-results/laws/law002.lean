import LTL

open LTL

-- LTL law 2: ◯ (p ⇒ q) ≈ ◯ p ⇒ ◯ q
-- (the proposer's answer starts at line 9)

namespace Candidate
theorem candidate {AP : Type} (p q : Formula AP) :
    ([𝐗 ((p ⇒ q))] ⊢ [(𝐗 (p) ⇒ 𝐗 (q))]) ∧ ([(𝐗 (p) ⇒ 𝐗 (q))] ⊢ [𝐗 ((p ⇒ q))]) := by
  refine ⟨?_, ?_⟩
  · exact Derives.impR (A := 𝐗 p) (B := 𝐗 q) (by simp)
      (Derives.next (show [p, p ⇒ q] ⊢ [q] from
          Derives.impL (A := p) (B := q) (by simp)
            (Derives.ax (A := p) (by simp) (by simp))
            (Derives.ax (A := q) (by simp) (by simp)))
        (by simp) (by simp))
  · exact Derives.impL (A := 𝐗 p) (B := 𝐗 q) (by simp)
      (Derives.next (show ([] : List (Formula AP)) ⊢ [p, p ⇒ q] from
          Derives.impR (A := p) (B := q) (by simp)
            (Derives.ax (A := p) (by simp) (by simp)))
        (by simp) (by simp))
      (Derives.next (show [q] ⊢ [p ⇒ q] from
          Derives.impR (A := p) (B := q) (by simp)
            (Derives.ax (A := q) (by simp) (by simp)))
        (by simp) (by simp))

end Candidate

theorem verified {AP : Type} (p q : Formula AP) :
    ([𝐗 ((p ⇒ q))] ⊢ [(𝐗 (p) ⇒ 𝐗 (q))]) ∧ ([(𝐗 (p) ⇒ 𝐗 (q))] ⊢ [𝐗 ((p ⇒ q))]) :=
  Candidate.candidate p q

#print axioms verified
