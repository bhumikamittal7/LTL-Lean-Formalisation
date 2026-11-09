import LTL

open LTL

-- LTL law 6: ◯ (p ≡ q) ≈ ◯ p ≡ ◯ q
-- (the proposer's answer starts at line 9)

namespace Candidate
theorem candidate {AP : Type} (p q : Formula AP) :
    ([𝐗 (((p ⇒ q) ⋏ (q ⇒ p)))] ⊢ [((𝐗 (p) ⇒ 𝐗 (q)) ⋏ (𝐗 (q) ⇒ 𝐗 (p)))]) ∧ ([((𝐗 (p) ⇒ 𝐗 (q)) ⋏ (𝐗 (q) ⇒ 𝐗 (p)))] ⊢ [𝐗 (((p ⇒ q) ⋏ (q ⇒ p)))]) := by
  constructor
  · refine Derives.andR (A := (𝐗 p ⇒ 𝐗 q)) (B := (𝐗 q ⇒ 𝐗 p)) (by simp) ?_ ?_
    · refine Derives.impR (A := 𝐗 p) (B := 𝐗 q) (by simp) ?_
      refine Derives.step (Γ' := [((p ⇒ q) ⋏ (q ⇒ p)), p]) (B := q) ?_ (by simp) (by simp)
      refine Derives.andL (A := (p ⇒ q)) (B := (q ⇒ p)) (by simp) ?_
      refine Derives.impL (A := p) (B := q) (by simp) ?_ ?_
      · exact .ax (A := p) (by simp) (by simp)
      · exact .ax (A := q) (by simp) (by simp)
    · refine Derives.impR (A := 𝐗 q) (B := 𝐗 p) (by simp) ?_
      refine Derives.step (Γ' := [((p ⇒ q) ⋏ (q ⇒ p)), q]) (B := p) ?_ (by simp) (by simp)
      refine Derives.andL (A := (p ⇒ q)) (B := (q ⇒ p)) (by simp) ?_
      refine Derives.impL (A := q) (B := p) (by simp) ?_ ?_
      · exact .ax (A := q) (by simp) (by simp)
      · exact .ax (A := p) (by simp) (by simp)
  · refine Derives.andL (A := (𝐗 p ⇒ 𝐗 q)) (B := (𝐗 q ⇒ 𝐗 p)) (by simp) ?_
    refine Derives.impL (A := 𝐗 p) (B := 𝐗 q) (by simp) ?_ ?_
    · refine Derives.impL (A := 𝐗 q) (B := 𝐗 p) (by simp) ?_ ?_
      · refine Derives.next (Γ' := []) (Δ' := [q, p, ((p ⇒ q) ⋏ (q ⇒ p))]) ?_ (by simp) (by simp)
        refine Derives.andR (A := (p ⇒ q)) (B := (q ⇒ p)) (by simp) ?_ ?_
        · refine Derives.impR (A := p) (B := q) (by simp) ?_
          exact .ax (A := p) (by simp) (by simp)
        · refine Derives.impR (A := q) (B := p) (by simp) ?_
          exact .ax (A := q) (by simp) (by simp)
      · exact .ax (A := 𝐗 p) (by simp) (by simp)
    · refine Derives.impL (A := 𝐗 q) (B := 𝐗 p) (by simp) ?_ ?_
      · exact .ax (A := 𝐗 q) (by simp) (by simp)
      · refine Derives.step (Γ' := [p, q]) (B := ((p ⇒ q) ⋏ (q ⇒ p))) ?_ (by simp) (by simp)
        refine Derives.andR (A := (p ⇒ q)) (B := (q ⇒ p)) (by simp) ?_ ?_
        · refine Derives.impR (A := p) (B := q) (by simp) ?_
          exact .ax (A := q) (by simp) (by simp)
        · refine Derives.impR (A := q) (B := p) (by simp) ?_
          exact .ax (A := p) (by simp) (by simp)

end Candidate

theorem verified {AP : Type} (p q : Formula AP) :
    ([𝐗 (((p ⇒ q) ⋏ (q ⇒ p)))] ⊢ [((𝐗 (p) ⇒ 𝐗 (q)) ⋏ (𝐗 (q) ⇒ 𝐗 (p)))]) ∧ ([((𝐗 (p) ⇒ 𝐗 (q)) ⋏ (𝐗 (q) ⇒ 𝐗 (p)))] ⊢ [𝐗 (((p ⇒ q) ⋏ (q ⇒ p)))]) :=
  Candidate.candidate p q

#print axioms verified
