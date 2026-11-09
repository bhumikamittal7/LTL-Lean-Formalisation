import LTL

open LTL

-- LTL law 9: ◯ (p U q) ≈ ◯ p U ◯ q
-- (the proposer's answer starts at line 9)

namespace Candidate
set_option hygiene false in
local notation "𝔘" => ((𝐗 p) 𝐔 (𝐗 q))
set_option hygiene false in
local notation "𝔚" => (∼ (𝔘))
set_option hygiene false in
local notation "𝔆" => ((𝔚) ⇒ ((𝐗 (∼ q)) ⋏ ((𝐗 p) ⇒ (𝐗 (𝔚)))))
set_option hygiene false in
local notation "𝔗" => (𝐆 (𝔆))
set_option hygiene false in
local notation "𝔎" => ((∼ q) ⋏ ((p ⇒ (𝔚)) ⋏ (𝔗)))

theorem ltlnx_hC {AP : Type} (p q : Formula AP) (Γ Δ : List (Formula AP)) :
    Γ ⊢ ((𝔆) :: Δ) := by
  refine Derives.impR (A := (𝔚)) (B := ((𝐗 (∼ q)) ⋏ ((𝐗 p) ⇒ (𝐗 (𝔚))))) (by simp) ?_
  refine Derives.andR (A := 𝐗 (∼ q)) (B := ((𝐗 p) ⇒ (𝐗 (𝔚)))) (by simp) ?_ ?_
  · refine Derives.negL (A := (𝔘)) (by simp) ?_
    refine Derives.untilR (A := 𝐗 p) (B := 𝐗 q) (by simp) ?_ ?_
    · exact Derives.next (Γ' := []) (Δ' := [q, ∼ q])
        (Derives.negR (A := q) (by simp) (Derives.ax (A := q) (by simp) (by simp)))
        (by simp) (by simp)
    · exact Derives.next (Γ' := []) (Δ' := [q, ∼ q])
        (Derives.negR (A := q) (by simp) (Derives.ax (A := q) (by simp) (by simp)))
        (by simp) (by simp)
  · refine Derives.impR (A := 𝐗 p) (B := 𝐗 (𝔚)) (by simp) ?_
    refine Derives.negL (A := (𝔘)) (by simp) ?_
    refine Derives.untilR (A := 𝐗 p) (B := 𝐗 q) (by simp) ?_ ?_
    · exact Derives.ax (A := 𝐗 p) (by simp) (by simp)
    · exact Derives.next (Γ' := []) (Δ' := [(𝔘), (𝔚)])
        (Derives.negR (A := (𝔘)) (by simp) (Derives.ax (A := (𝔘)) (by simp) (by simp)))
        (by simp) (by simp)

theorem ltlnx_hT {AP : Type} (p q : Formula AP) (Γ Δ : List (Formula AP)) :
    Γ ⊢ ((𝔗) :: Δ) :=
  Derives.alwaysR (A := (𝔆)) (I := (𝔆)) (by simp) (ltlnx_hC p q _ _)
    (Derives.next (Γ' := []) (Δ' := [(𝔆)]) (ltlnx_hC p q [] []) (by simp) (by simp))
    (Derives.ax (A := (𝔆)) (by simp) (by simp))

theorem ltlnx_core {AP : Type} (p q : Formula AP) :
    [𝐗 (∼ q), ((𝐗 p) ⇒ (𝐗 (𝔚))), 𝐗 (𝔗)] ⊢ [𝐗 (𝔎)] := by
  refine Derives.impL (A := 𝐗 p) (B := 𝐗 (𝔚)) (by simp) ?_ ?_
  · refine Derives.next (Γ' := [∼ q, (𝔗)]) (Δ' := [p, (𝔎)]) ?_ (by simp) (by simp)
    refine Derives.andR (A := ∼ q) (B := ((p ⇒ (𝔚)) ⋏ (𝔗))) (by simp) ?_ ?_
    · exact Derives.ax (A := ∼ q) (by simp) (by simp)
    · refine Derives.andR (A := (p ⇒ (𝔚))) (B := (𝔗)) (by simp) ?_ ?_
      · refine Derives.impR (A := p) (B := (𝔚)) (by simp) ?_
        exact Derives.ax (A := p) (by simp) (by simp)
      · exact Derives.ax (A := (𝔗)) (by simp) (by simp)
  · refine Derives.next (Γ' := [∼ q, (𝔚), (𝔗)]) (Δ' := [(𝔎)]) ?_ (by simp) (by simp)
    refine Derives.andR (A := ∼ q) (B := ((p ⇒ (𝔚)) ⋏ (𝔗))) (by simp) ?_ ?_
    · exact Derives.ax (A := ∼ q) (by simp) (by simp)
    · refine Derives.andR (A := (p ⇒ (𝔚))) (B := (𝔗)) (by simp) ?_ ?_
      · refine Derives.impR (A := p) (B := (𝔚)) (by simp) ?_
        exact Derives.ax (A := (𝔚)) (by simp) (by simp)
      · exact Derives.ax (A := (𝔗)) (by simp) (by simp)

theorem ltlnx_start {AP : Type} (p q : Formula AP) :
    [(𝔚), (𝔗)] ⊢ [𝐗 (𝔎)] := by
  refine Derives.alwaysL (A := (𝔆)) (by simp) ?_
  refine Derives.impL (A := (𝔚)) (B := ((𝐗 (∼ q)) ⋏ ((𝐗 p) ⇒ (𝐗 (𝔚))))) (by simp) ?_ ?_
  · exact Derives.ax (A := (𝔚)) (by simp) (by simp)
  · refine Derives.andL (A := 𝐗 (∼ q)) (B := ((𝐗 p) ⇒ (𝐗 (𝔚)))) (by simp) ?_
    exact Derives.wk (ltlnx_core p q) (by simp) (by simp)

theorem ltlnx_stepK {AP : Type} (p q : Formula AP) :
    [(𝔎), p] ⊢ [𝐗 (𝔎)] := by
  refine Derives.andL (A := ∼ q) (B := ((p ⇒ (𝔚)) ⋏ (𝔗))) (by simp) ?_
  refine Derives.andL (A := (p ⇒ (𝔚))) (B := (𝔗)) (by simp) ?_
  refine Derives.impL (A := p) (B := (𝔚)) (by simp) ?_ ?_
  · exact Derives.ax (A := p) (by simp) (by simp)
  · exact Derives.wk (ltlnx_start p q) (by simp) (by simp)

theorem ltlnx_L1 {AP : Type} (p q : Formula AP) :
    [(p 𝐔 q), (𝔎)] ⊢ [] := by
  refine Derives.untilL (A := p) (B := q) (I := ∼ (𝔎)) (by simp) ?_ ?_ ?_
  · refine Derives.negR (A := (𝔎)) (by simp) ?_
    refine Derives.andL (A := ∼ q) (B := ((p ⇒ (𝔚)) ⋏ (𝔗))) (by simp) ?_
    refine Derives.negL (A := q) (by simp) ?_
    exact Derives.ax (A := q) (by simp) (by simp)
  · refine Derives.negR (A := (𝔎)) (by simp) ?_
    refine Derives.cut (A := 𝐗 (𝔎)) ?_ ?_
    · exact Derives.wk (ltlnx_stepK p q) (by simp) (by simp)
    · refine Derives.next (Γ' := [(𝔎), ∼ (𝔎)]) (Δ' := []) ?_ (by simp) (by simp)
      refine Derives.negL (A := (𝔎)) (by simp) ?_
      exact Derives.ax (A := (𝔎)) (by simp) (by simp)
  · refine Derives.negL (A := (𝔎)) (by simp) ?_
    exact Derives.ax (A := (𝔎)) (by simp) (by simp)

theorem ltlnx_dir1 {AP : Type} (p q : Formula AP) :
    [𝐗 ((p 𝐔 q))] ⊢ [(𝐗 (p) 𝐔 𝐗 (q))] := by
  refine Derives.cut (A := (𝔗)) (ltlnx_hT p q _ _) ?_
  refine Derives.cut (A := (𝔚)) ?_ ?_
  · refine Derives.negR (A := (𝔘)) (by simp) ?_
    exact Derives.ax (A := (𝔘)) (by simp) (by simp)
  · refine Derives.cut (A := 𝐗 (𝔎)) ?_ ?_
    · exact Derives.wk (ltlnx_start p q) (by simp) (by simp)
    · exact Derives.next (Γ' := [(p 𝐔 q), (𝔎)]) (Δ' := []) (ltlnx_L1 p q) (by simp) (by simp)

theorem ltlnx_dir2 {AP : Type} (p q : Formula AP) :
    [(𝐗 (p) 𝐔 𝐗 (q))] ⊢ [𝐗 ((p 𝐔 q))] := by
  refine Derives.untilL (A := 𝐗 p) (B := 𝐗 q) (I := 𝐗 (p 𝐔 q)) (by simp) ?_ ?_ ?_
  · refine Derives.next (Γ' := [q]) (Δ' := [(p 𝐔 q)]) ?_ (by simp) (by simp)
    refine Derives.untilR (A := p) (B := q) (by simp) ?_ ?_
    · exact Derives.ax (A := q) (by simp) (by simp)
    · exact Derives.ax (A := q) (by simp) (by simp)
  · refine Derives.next (Γ' := [p, 𝐗 (p 𝐔 q)]) (Δ' := [(p 𝐔 q)]) ?_ (by simp) (by simp)
    refine Derives.untilR (A := p) (B := q) (by simp) ?_ ?_
    · exact Derives.ax (A := p) (by simp) (by simp)
    · exact Derives.ax (A := 𝐗 (p 𝐔 q)) (by simp) (by simp)
  · exact Derives.ax (A := 𝐗 (p 𝐔 q)) (by simp) (by simp)

theorem candidate {AP : Type} (p q : Formula AP) :
    ([𝐗 ((p 𝐔 q))] ⊢ [(𝐗 (p) 𝐔 𝐗 (q))]) ∧ ([(𝐗 (p) 𝐔 𝐗 (q))] ⊢ [𝐗 ((p 𝐔 q))]) :=
  ⟨ltlnx_dir1 p q, ltlnx_dir2 p q⟩

end Candidate

theorem verified {AP : Type} (p q : Formula AP) :
    ([𝐗 ((p 𝐔 q))] ⊢ [(𝐗 (p) 𝐔 𝐗 (q))]) ∧ ([(𝐗 (p) 𝐔 𝐗 (q))] ⊢ [𝐗 ((p 𝐔 q))]) :=
  Candidate.candidate p q

#print axioms verified
