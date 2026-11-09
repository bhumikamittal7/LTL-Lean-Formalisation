import LTL

open LTL

-- LTL law 57: □ (p ⇒ ◯ p) ⟹ (p ⇒ □ p)
-- (the proposer's answer starts at line 9)

namespace Candidate
theorem candidate {AP : Type} (p : Formula AP) :
    [𝐆 ((p ⇒ 𝐗 (p)))] ⊢ [(p ⇒ 𝐆 (p))] := by
  refine Derives.impR (A := p) (B := 𝐆 p) (by simp) ?_
  refine Derives.alwaysR (A := p) (p ⋏ 𝐆 (p ⇒ 𝐗 p)) (by simp) ?_ ?_ ?_
  · refine Derives.andR (A := p) (B := 𝐆 (p ⇒ 𝐗 p)) (by simp) ?_ ?_
    · exact .ax (A := p) (by simp) (by simp)
    · exact .ax (A := 𝐆 (p ⇒ 𝐗 p)) (by simp) (by simp)
  · refine Derives.andL (A := p) (B := 𝐆 (p ⇒ 𝐗 p)) (by simp) ?_
    refine Derives.alwaysL (A := p ⇒ 𝐗 p) (by simp) ?_
    refine Derives.impL (A := p) (B := 𝐗 p) (by simp) ?_ ?_
    · exact .ax (A := p) (by simp) (by simp)
    · refine Derives.step (Γ' := [p, 𝐆 (p ⇒ 𝐗 p)]) (B := p ⋏ 𝐆 (p ⇒ 𝐗 p)) ?_ (by simp) (by simp)
      refine Derives.andR (A := p) (B := 𝐆 (p ⇒ 𝐗 p)) (by simp) ?_ ?_
      · exact .ax (A := p) (by simp) (by simp)
      · exact .ax (A := 𝐆 (p ⇒ 𝐗 p)) (by simp) (by simp)
  · refine Derives.andL (A := p) (B := 𝐆 (p ⇒ 𝐗 p)) (by simp) ?_
    exact .ax (A := p) (by simp) (by simp)

end Candidate

theorem verified {AP : Type} (p : Formula AP) :
    [𝐆 ((p ⇒ 𝐗 (p)))] ⊢ [(p ⇒ 𝐆 (p))] :=
  Candidate.candidate p

#print axioms verified
