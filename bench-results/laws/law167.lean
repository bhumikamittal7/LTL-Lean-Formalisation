import LTL

open LTL

-- LTL law 167: □ ((□ p ⇒ ◇ q) ∧ (q ⇒ ◯ r)) ⟹ (□ p ⇒ ◯ □ ◇ r)
-- (the proposer's answer starts at line 9)

namespace Candidate
theorem cand_inv_next {AP : Type} (p q r : Formula AP) :
    [𝐆 p ⋏ 𝐆 (((𝐆 (p) ⇒ 𝐅 (q)) ⋏ (q ⇒ 𝐗 (r))))] ⊢
      [𝐗 (𝐆 p ⋏ 𝐆 (((𝐆 (p) ⇒ 𝐅 (q)) ⋏ (q ⇒ 𝐗 (r)))))] :=
  .andL (A := 𝐆 p) (B := 𝐆 (((𝐆 (p) ⇒ 𝐅 (q)) ⋏ (q ⇒ 𝐗 (r))))) (by simp) <|
  .alwaysL (A := p) (by simp) <|
  .alwaysL (A := ((𝐆 (p) ⇒ 𝐅 (q)) ⋏ (q ⇒ 𝐗 (r)))) (by simp) <|
  Derives.step (Γ' := [𝐆 p, 𝐆 (((𝐆 (p) ⇒ 𝐅 (q)) ⋏ (q ⇒ 𝐗 (r))))])
    (B := 𝐆 p ⋏ 𝐆 (((𝐆 (p) ⇒ 𝐅 (q)) ⋏ (q ⇒ 𝐗 (r)))))
    (.andR (A := 𝐆 p) (B := 𝐆 (((𝐆 (p) ⇒ 𝐅 (q)) ⋏ (q ⇒ 𝐗 (r))))) (by simp)
      (.ax (A := 𝐆 p) (by simp) (by simp))
      (.ax (A := 𝐆 (((𝐆 (p) ⇒ 𝐅 (q)) ⋏ (q ⇒ 𝐗 (r))))) (by simp) (by simp)))
    (by simp) (by simp)

theorem cand_evbase {AP : Type} (p q r : Formula AP) :
    [q] ⊢ [𝐆 (((𝐆 (p) ⇒ 𝐅 (q)) ⋏ (q ⇒ 𝐗 (r)))) ⇒ 𝐅 r] :=
  .impR (A := 𝐆 (((𝐆 (p) ⇒ 𝐅 (q)) ⋏ (q ⇒ 𝐗 (r))))) (B := 𝐅 r) (by simp) <|
  .alwaysL (A := ((𝐆 (p) ⇒ 𝐅 (q)) ⋏ (q ⇒ 𝐗 (r)))) (by simp) <|
  .andL (A := 𝐆 p ⇒ 𝐅 q) (B := q ⇒ 𝐗 r) (by simp) <|
  .impL (A := q) (B := 𝐗 r) (by simp) (.ax (A := q) (by simp) (by simp)) <|
  Derives.evR (A := r) (by simp) <|
  Derives.step (Γ' := [r]) (B := 𝐅 r)
    (Derives.evR (A := r) (by simp) (.ax (A := r) (by simp) (by simp)))
    (by simp) (by simp)

theorem cand_evstep {AP : Type} (p q r : Formula AP) :
    [𝐗 (𝐆 (((𝐆 (p) ⇒ 𝐅 (q)) ⋏ (q ⇒ 𝐗 (r)))) ⇒ 𝐅 r)] ⊢
      [𝐆 (((𝐆 (p) ⇒ 𝐅 (q)) ⋏ (q ⇒ 𝐗 (r)))) ⇒ 𝐅 r] :=
  .impR (A := 𝐆 (((𝐆 (p) ⇒ 𝐅 (q)) ⋏ (q ⇒ 𝐗 (r))))) (B := 𝐅 r) (by simp) <|
  .alwaysL (A := ((𝐆 (p) ⇒ 𝐅 (q)) ⋏ (q ⇒ 𝐗 (r)))) (by simp) <|
  Derives.evR (A := r) (by simp) <|
  Derives.step (Γ' := [𝐆 (((𝐆 (p) ⇒ 𝐅 (q)) ⋏ (q ⇒ 𝐗 (r)))) ⇒ 𝐅 r,
                       𝐆 (((𝐆 (p) ⇒ 𝐅 (q)) ⋏ (q ⇒ 𝐗 (r))))]) (B := 𝐅 r)
    (.impL (A := 𝐆 (((𝐆 (p) ⇒ 𝐅 (q)) ⋏ (q ⇒ 𝐗 (r))))) (B := 𝐅 r) (by simp)
      (.ax (A := 𝐆 (((𝐆 (p) ⇒ 𝐅 (q)) ⋏ (q ⇒ 𝐗 (r))))) (by simp) (by simp))
      (.ax (A := 𝐅 r) (by simp) (by simp)))
    (by simp) (by simp)

theorem cand_inv_goal {AP : Type} (p q r : Formula AP) :
    [𝐆 p ⋏ 𝐆 (((𝐆 (p) ⇒ 𝐅 (q)) ⋏ (q ⇒ 𝐗 (r))))] ⊢ [𝐅 r] :=
  .andL (A := 𝐆 p) (B := 𝐆 (((𝐆 (p) ⇒ 𝐅 (q)) ⋏ (q ⇒ 𝐗 (r))))) (by simp) <|
  .alwaysL (A := ((𝐆 (p) ⇒ 𝐅 (q)) ⋏ (q ⇒ 𝐗 (r)))) (by simp) <|
  .andL (A := 𝐆 p ⇒ 𝐅 q) (B := q ⇒ 𝐗 r) (by simp) <|
  .impL (A := 𝐆 p) (B := 𝐅 q) (by simp) (.ax (A := 𝐆 p) (by simp) (by simp)) <|
  Derives.evL (A := q) (I := 𝐆 (((𝐆 (p) ⇒ 𝐅 (q)) ⋏ (q ⇒ 𝐗 (r)))) ⇒ 𝐅 r) (by simp)
    (cand_evbase p q r) (cand_evstep p q r) <|
  .impL (A := 𝐆 (((𝐆 (p) ⇒ 𝐅 (q)) ⋏ (q ⇒ 𝐗 (r))))) (B := 𝐅 r) (by simp)
    (.ax (A := 𝐆 (((𝐆 (p) ⇒ 𝐅 (q)) ⋏ (q ⇒ 𝐗 (r))))) (by simp) (by simp))
    (.ax (A := 𝐅 r) (by simp) (by simp))

theorem cand_inner {AP : Type} (p q r : Formula AP) :
    [𝐆 p, 𝐆 (((𝐆 (p) ⇒ 𝐅 (q)) ⋏ (q ⇒ 𝐗 (r))))] ⊢ [𝐆 (𝐅 r)] :=
  .alwaysR (A := 𝐅 r) (I := 𝐆 p ⋏ 𝐆 (((𝐆 (p) ⇒ 𝐅 (q)) ⋏ (q ⇒ 𝐗 (r))))) (by simp)
    (.andR (A := 𝐆 p) (B := 𝐆 (((𝐆 (p) ⇒ 𝐅 (q)) ⋏ (q ⇒ 𝐗 (r))))) (by simp)
      (.ax (A := 𝐆 p) (by simp) (by simp))
      (.ax (A := 𝐆 (((𝐆 (p) ⇒ 𝐅 (q)) ⋏ (q ⇒ 𝐗 (r))))) (by simp) (by simp)))
    (cand_inv_next p q r) (cand_inv_goal p q r)

theorem candidate {AP : Type} (p q r : Formula AP) :
    [𝐆 (((𝐆 (p) ⇒ 𝐅 (q)) ⋏ (q ⇒ 𝐗 (r))))] ⊢ [(𝐆 (p) ⇒ 𝐗 (𝐆 (𝐅 (r))))] :=
  .impR (A := 𝐆 p) (B := 𝐗 (𝐆 (𝐅 r))) (by simp) <|
  .alwaysL (A := p) (by simp) <|
  .alwaysL (A := ((𝐆 (p) ⇒ 𝐅 (q)) ⋏ (q ⇒ 𝐗 (r)))) (by simp) <|
  Derives.step (Γ' := [𝐆 p, 𝐆 (((𝐆 (p) ⇒ 𝐅 (q)) ⋏ (q ⇒ 𝐗 (r))))]) (B := 𝐆 (𝐅 r))
    (cand_inner p q r) (by simp) (by simp)

end Candidate

theorem verified {AP : Type} (p q r : Formula AP) :
    [𝐆 (((𝐆 (p) ⇒ 𝐅 (q)) ⋏ (q ⇒ 𝐗 (r))))] ⊢ [(𝐆 (p) ⇒ 𝐗 (𝐆 (𝐅 (r))))] :=
  Candidate.candidate p q r

#print axioms verified
