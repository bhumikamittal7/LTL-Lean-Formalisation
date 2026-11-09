import LTL.Sequent

/-!
# Soundness of the sequent calculus

`Γ ⊢ Δ` implies `SValid Γ Δ`, by induction on the derivation. The temporal
cases with an invariant use induction over positions: forward for `G`,
backward from the witness for `U`.
-/

namespace LTL

variable {AP : Type}


/-- Forward induction: an invariant that holds at `i` and is preserved holds from `i` on. -/
theorem inv_forward {σ : Trace AP} {I : Formula AP} {i : Nat}
    (step : ∀ n, Sat σ n I → Sat σ (n + 1) I) (h0 : Sat σ i I) :
    ∀ j, i ≤ j → Sat σ j I := by
  intro j hj
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hj
  induction d with
  | zero => exact h0
  | succ d ih => exact step _ (ih (Nat.le_add_right _ _))

/-- Backward induction: if `I` holds at `j` and is pulled back one step on `[i, j)`,
then it holds at `i`. -/
theorem inv_backward {σ : Trace AP} {I : Formula AP} {i j : Nat} (hij : i ≤ j)
    (hj : Sat σ j I) (back : ∀ k, i ≤ k → k < j → Sat σ (k + 1) I → Sat σ k I) :
    Sat σ i I := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hij
  induction d generalizing i with
  | zero => simpa using hj
  | succ d ih =>
    have h1 : Sat σ (i + 1) I :=
      ih (Nat.le_add_right _ _) (by rw [show i + 1 + d = i + (d + 1) by omega]; exact hj)
        fun k hk hkj => back k (by omega) (by omega)
    exact back i (Nat.le_refl _) (by omega) h1

/-- A context-free sequent `[A] ⊢ [B]` gives `A → B` at every position. -/
theorem SValid.single {A B : Formula AP} (h : SValid [A] [B]) (σ : Trace AP) (i : Nat)
    (hA : Sat σ i A) : Sat σ i B := by
  obtain ⟨C, hC, hs⟩ := h σ i (by simpa using hA)
  simp only [List.mem_singleton] at hC
  exact hC ▸ hs

theorem soundness {Γ Δ : List (Formula AP)} (h : Γ ⊢ Δ) : SValid Γ Δ := by
  induction h with
  | ax hΓ hΔ => exact fun σ i hs => ⟨_, hΔ, hs _ hΓ⟩
  | cut A _ _ ih₁ ih₂ =>
    intro σ i hs
    obtain ⟨B, hB, hsB⟩ := ih₁ σ i hs
    rcases List.mem_cons.mp hB with rfl | hB
    · exact ih₂ σ i fun C hC => (List.mem_cons.mp hC).elim (· ▸ hsB) (hs C)
    · exact ⟨B, hB, hsB⟩
  | botL hΓ => exact fun σ i hs => (hs _ hΓ).elim
  | negL hΓ _ ih =>
    intro σ i hs
    obtain ⟨B, hB, hsB⟩ := ih σ i hs
    rcases List.mem_cons.mp hB with rfl | hB
    · exact (hs _ hΓ hsB).elim
    · exact ⟨B, hB, hsB⟩
  | @negR Γ Δ A hΔ _ ih =>
    intro σ i hs
    by_cases hA : Sat σ i A
    · exact ih σ i fun C hC => (List.mem_cons.mp hC).elim (· ▸ hA) (hs C)
    · exact ⟨_, hΔ, hA⟩
  | andL hΓ _ ih =>
    intro σ i hs
    have hAB := hs _ hΓ
    refine ih σ i fun C hC => ?_
    simp only [List.mem_cons] at hC
    rcases hC with rfl | rfl | hC
    · exact hAB.1
    · exact hAB.2
    · exact hs C hC
  | andR hΔ _ _ ih₁ ih₂ =>
    intro σ i hs
    obtain ⟨B₁, hB₁, hs₁⟩ := ih₁ σ i hs
    obtain ⟨B₂, hB₂, hs₂⟩ := ih₂ σ i hs
    rcases List.mem_cons.mp hB₁ with rfl | hB₁
    · rcases List.mem_cons.mp hB₂ with rfl | hB₂
      · exact ⟨_, hΔ, hs₁, hs₂⟩
      · exact ⟨B₂, hB₂, hs₂⟩
    · exact ⟨B₁, hB₁, hs₁⟩
  | impL hΓ _ _ ih₁ ih₂ =>
    intro σ i hs
    obtain ⟨B, hB, hsB⟩ := ih₁ σ i hs
    rcases List.mem_cons.mp hB with rfl | hB
    · exact ih₂ σ i fun C hC => (List.mem_cons.mp hC).elim (· ▸ hs _ hΓ hsB) (hs C)
    · exact ⟨B, hB, hsB⟩
  | @impR Γ Δ A B hΔ _ ih =>
    intro σ i hs
    by_cases hA : Sat σ i A
    · obtain ⟨C, hC, hsC⟩ := ih σ i fun C hC => (List.mem_cons.mp hC).elim (· ▸ hA) (hs C)
      rcases List.mem_cons.mp hC with rfl | hC
      · exact ⟨_, hΔ, fun _ => hsC⟩
      · exact ⟨C, hC, hsC⟩
    · exact ⟨_, hΔ, fun h => (hA h).elim⟩
  | next _ hΓ hΔ ih =>
    intro σ i hs
    obtain ⟨B, hB, hsB⟩ := ih σ (i + 1) fun A hA => hs _ (hΓ A hA)
    exact ⟨_, hΔ B hB, hsB⟩
  | alwaysL hΓ _ ih =>
    intro σ i hs
    have hG := hs _ hΓ
    refine ih σ i fun C hC => ?_
    simp only [List.mem_cons] at hC
    rcases hC with rfl | rfl | hC
    · exact hG i (Nat.le_refl _)
    · exact fun j hj => hG j (by omega)
    · exact hs C hC
  | alwaysR I hΔ _ _ _ ih₁ ih₂ ih₃ =>
    intro σ i hs
    obtain ⟨B, hB, hsB⟩ := ih₁ σ i hs
    rcases List.mem_cons.mp hB with rfl | hB
    · refine ⟨_, hΔ, fun j hj => ih₃.single σ j ?_⟩
      exact inv_forward (fun n => ih₂.single σ n) hsB j hj
    · exact ⟨B, hB, hsB⟩
  | untilL I hΓ _ _ _ ih₁ ih₂ ih₃ =>
    intro σ i hs
    obtain ⟨j, hij, hB, hA⟩ := hs _ hΓ
    have hI : Sat σ i I := by
      refine inv_backward hij (ih₁.single σ j hB) fun k hik hkj h => ?_
      obtain ⟨C, hC, hsC⟩ := ih₂ σ k (by
        intro D hD
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hD
        rcases hD with rfl | rfl
        · exact hA k hik hkj
        · exact h)
      simp only [List.mem_singleton] at hC
      exact hC ▸ hsC
    exact ih₃ σ i fun C hC => (List.mem_cons.mp hC).elim (· ▸ hI) (hs C)
  | untilR hΔ _ _ ih₁ ih₂ =>
    intro σ i hs
    obtain ⟨B₁, hB₁, hs₁⟩ := ih₁ σ i hs
    obtain ⟨B₂, hB₂, hs₂⟩ := ih₂ σ i hs
    simp only [List.mem_cons] at hB₁ hB₂
    rcases hB₁ with rfl | rfl | hB₁
    · exact ⟨_, hΔ, i, Nat.le_refl _, hs₁, fun k hk hki => absurd hki (by omega)⟩
    · rcases hB₂ with h | rfl | hB₂
      · subst h
        exact ⟨_, hΔ, i, Nat.le_refl _, hs₂, fun k hk hki => absurd hki (by omega)⟩
      · obtain ⟨j, hj, hB, hA⟩ := hs₂
        refine ⟨_, hΔ, j, by omega, hB, fun k hik hkj => ?_⟩
        rcases Nat.eq_or_lt_of_le hik with rfl | hik
        · exact hs₁
        · exact hA k (by omega) hkj
      · exact ⟨B₂, hB₂, hs₂⟩
    · exact ⟨B₁, hB₁, hs₁⟩

end LTL
