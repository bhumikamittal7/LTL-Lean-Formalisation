import LTL

open LTL

-- LTL law 25: (p U (¬q U r)) ∧ (q U r) ⟹ p U r
-- (the proposer's answer starts at line 9)

namespace Candidate
theorem untilCases {AP : Type} (a b : Formula AP) {Γ Δ : List (Formula AP)}
    (h : (a 𝐔 b) ∈ Γ) (h1 : (b :: Γ) ⊢ Δ) (h2 : (a :: (𝐗 (a 𝐔 b)) :: Γ) ⊢ Δ) : Γ ⊢ Δ := by
  refine Derives.untilL (A := a) (B := b) (I := b ⋎ (a ⋏ 𝐗 (a 𝐔 b))) h ?_ ?_ ?_
  · exact Derives.orR (A := b) (B := a ⋏ 𝐗 (a 𝐔 b)) (by simp)
      (Derives.ax (A := b) (by simp) (by simp))
  · refine Derives.orR (A := b) (B := a ⋏ 𝐗 (a 𝐔 b)) (by simp) ?_
    refine Derives.andR (A := a) (B := 𝐗 (a 𝐔 b)) (by simp)
      (Derives.ax (A := a) (by simp) (by simp)) ?_
    refine Derives.step (Γ' := [b ⋎ (a ⋏ 𝐗 (a 𝐔 b))]) (B := a 𝐔 b) ?_ (by simp) (by simp)
    refine Derives.orL (A := b) (B := a ⋏ 𝐗 (a 𝐔 b)) (by simp) ?_ ?_
    · exact Derives.untilR (A := a) (B := b) (by simp)
        (Derives.ax (A := b) (by simp) (by simp))
        (Derives.ax (A := b) (by simp) (by simp))
    · refine Derives.andL (A := a) (B := 𝐗 (a 𝐔 b)) (by simp) ?_
      exact Derives.untilR (A := a) (B := b) (by simp)
        (Derives.ax (A := a) (by simp) (by simp))
        (Derives.ax (A := 𝐗 (a 𝐔 b)) (by simp) (by simp))
  · refine Derives.orL (A := b) (B := a ⋏ 𝐗 (a 𝐔 b)) (by simp) ?_ ?_
    · refine Derives.wk h1 ?_ (fun x hx => hx)
      intro x hx
      rcases List.mem_cons.mp hx with hx | hx
      · simp [hx]
      · simp [hx]
    · refine Derives.andL (A := a) (B := 𝐗 (a 𝐔 b)) (by simp) ?_
      refine Derives.wk h2 ?_ (fun x hx => hx)
      intro x hx
      rcases List.mem_cons.mp hx with hx | hx
      · simp [hx]
      · rcases List.mem_cons.mp hx with hx | hx
        · simp [hx]
        · simp [hx]

theorem candidate {AP : Type} (p q r : Formula AP) :
    [((p 𝐔 (∼(q) 𝐔 r)) ⋏ (q 𝐔 r))] ⊢ [(p 𝐔 r)] := by
  refine Derives.andL (A := p 𝐔 (∼(q) 𝐔 r)) (B := q 𝐔 r) (by simp) ?_
  refine Derives.untilL (A := q) (B := r) (I := (p 𝐔 (∼(q) 𝐔 r)) ⇒ (p 𝐔 r)) (by simp) ?_ ?_ ?_
  · refine Derives.impR (A := p 𝐔 (∼(q) 𝐔 r)) (B := p 𝐔 r) (by simp) ?_
    exact Derives.untilR (A := p) (B := r) (by simp)
      (Derives.ax (A := r) (by simp) (by simp))
      (Derives.ax (A := r) (by simp) (by simp))
  · refine Derives.impR (A := p 𝐔 (∼(q) 𝐔 r)) (B := p 𝐔 r) (by simp) ?_
    refine untilCases p (∼(q) 𝐔 r) (by simp) ?_ ?_
    · refine untilCases (∼(q)) r (by simp) ?_ ?_
      · exact Derives.untilR (A := p) (B := r) (by simp)
          (Derives.ax (A := r) (by simp) (by simp))
          (Derives.ax (A := r) (by simp) (by simp))
      · exact Derives.negL (A := q) (by simp) (Derives.ax (A := q) (by simp) (by simp))
    · refine Derives.untilR (A := p) (B := r) (by simp)
        (Derives.ax (A := p) (by simp) (by simp)) ?_
      refine Derives.step (Γ' := [(p 𝐔 (∼(q) 𝐔 r)) ⇒ (p 𝐔 r), p 𝐔 (∼(q) 𝐔 r)])
        (B := p 𝐔 r) ?_ (by simp) (by simp)
      exact Derives.impL (A := p 𝐔 (∼(q) 𝐔 r)) (B := p 𝐔 r) (by simp)
        (Derives.ax (A := p 𝐔 (∼(q) 𝐔 r)) (by simp) (by simp))
        (Derives.ax (A := p 𝐔 r) (by simp) (by simp))
  · exact Derives.impL (A := p 𝐔 (∼(q) 𝐔 r)) (B := p 𝐔 r) (by simp)
      (Derives.ax (A := p 𝐔 (∼(q) 𝐔 r)) (by simp) (by simp))
      (Derives.ax (A := p 𝐔 r) (by simp) (by simp))

end Candidate

theorem verified {AP : Type} (p q r : Formula AP) :
    [((p 𝐔 (∼(q) 𝐔 r)) ⋏ (q 𝐔 r))] ⊢ [(p 𝐔 r)] :=
  Candidate.candidate p q r

#print axioms verified
