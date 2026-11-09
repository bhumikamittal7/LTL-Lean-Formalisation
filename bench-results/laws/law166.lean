import LTL

open LTL

-- LTL law 166: ◇ □ p ∧ □ ◇ q ⟹ □ ◇ (p ∧ q)
-- (the proposer's answer starts at line 9)

namespace Candidate
theorem back_aux {AP : Type} (H C : Formula AP) :
    [𝐗 ((𝐆 H) ⇒ (𝐅 C))] ⊢ [(𝐆 H) ⇒ (𝐅 C)] := by
  have m3 : [(𝐆 H) ⇒ (𝐅 C), 𝐆 H] ⊢ [𝐅 C] :=
    Derives.impL (A := 𝐆 H) (B := 𝐅 C) (by simp)
      (Derives.ax (A := 𝐆 H) (by simp) (by simp))
      (Derives.ax (A := 𝐅 C) (by simp) (by simp))
  have m2 : H :: 𝐗 (𝐆 H) :: 𝐆 H :: [𝐗 ((𝐆 H) ⇒ (𝐅 C))] ⊢
      C :: 𝐗 (𝐅 C) :: 𝐅 C :: [(𝐆 H) ⇒ (𝐅 C)] :=
    Derives.step m3 (by simp) (by simp)
  have m1 : 𝐆 H :: [𝐗 ((𝐆 H) ⇒ (𝐅 C))] ⊢
      C :: 𝐗 (𝐅 C) :: 𝐅 C :: [(𝐆 H) ⇒ (𝐅 C)] :=
    Derives.alwaysL (A := H) (by simp) m2
  have m0 : 𝐆 H :: [𝐗 ((𝐆 H) ⇒ (𝐅 C))] ⊢ 𝐅 C :: [(𝐆 H) ⇒ (𝐅 C)] :=
    Derives.evR (A := C) (by simp) m1
  exact Derives.impR (A := 𝐆 H) (B := 𝐅 C) (by simp) m0

theorem FG_step_aux {AP : Type} (p : Formula AP) :
    [𝐅 (𝐆 p)] ⊢ [𝐗 (𝐅 (𝐆 p))] := by
  have a1 : [𝐆 p] ⊢ [𝐅 (𝐆 p)] :=
    Derives.evR (A := 𝐆 p) (by simp) (Derives.ax (A := 𝐆 p) (by simp) (by simp))
  have a2 : p :: 𝐗 (𝐆 p) :: [𝐆 p] ⊢ [𝐗 (𝐅 (𝐆 p))] :=
    Derives.step a1 (by simp) (by simp)
  have h1 : [𝐆 p] ⊢ [𝐗 (𝐅 (𝐆 p))] :=
    Derives.alwaysL (A := p) (by simp) a2
  have b1 : [𝐗 (𝐅 (𝐆 p))] ⊢ [𝐅 (𝐆 p)] :=
    Derives.evR (A := 𝐆 p) (by simp)
      (Derives.ax (A := 𝐗 (𝐅 (𝐆 p))) (by simp) (by simp))
  have h2 : [𝐗 (𝐗 (𝐅 (𝐆 p)))] ⊢ [𝐗 (𝐅 (𝐆 p))] :=
    Derives.step b1 (by simp) (by simp)
  have h3 : 𝐗 (𝐅 (𝐆 p)) :: [𝐅 (𝐆 p)] ⊢ [𝐗 (𝐅 (𝐆 p))] :=
    Derives.ax (A := 𝐗 (𝐅 (𝐆 p))) (by simp) (by simp)
  exact Derives.evL (A := 𝐆 p) (I := 𝐗 (𝐅 (𝐆 p))) (by simp) h1 h2 h3

theorem J_step_aux {AP : Type} (p q : Formula AP) :
    [(𝐅 (𝐆 p) ⋏ 𝐆 (𝐅 q))] ⊢ [𝐗 (𝐅 (𝐆 p) ⋏ 𝐆 (𝐅 q))] := by
  have h3 : [𝐅 (𝐆 p), 𝐆 (𝐅 q)] ⊢ [(𝐅 (𝐆 p) ⋏ 𝐆 (𝐅 q))] :=
    Derives.andR (A := 𝐅 (𝐆 p)) (B := 𝐆 (𝐅 q)) (by simp)
      (Derives.ax (A := 𝐅 (𝐆 p)) (by simp) (by simp))
      (Derives.ax (A := 𝐆 (𝐅 q)) (by simp) (by simp))
  have h2 : 𝐗 (𝐅 (𝐆 p)) :: 𝐅 q :: 𝐗 (𝐆 (𝐅 q)) :: 𝐅 (𝐆 p) :: 𝐆 (𝐅 q) ::
      [(𝐅 (𝐆 p) ⋏ 𝐆 (𝐅 q))] ⊢ [𝐗 (𝐅 (𝐆 p) ⋏ 𝐆 (𝐅 q))] :=
    Derives.step h3 (by simp) (by simp)
  have h1 : 𝐅 q :: 𝐗 (𝐆 (𝐅 q)) :: 𝐅 (𝐆 p) :: 𝐆 (𝐅 q) ::
      [(𝐅 (𝐆 p) ⋏ 𝐆 (𝐅 q))] ⊢ 𝐗 (𝐅 (𝐆 p)) :: [𝐗 (𝐅 (𝐆 p) ⋏ 𝐆 (𝐅 q))] :=
    Derives.wk (FG_step_aux p) (by simp) (by simp)
  have h' : 𝐅 q :: 𝐗 (𝐆 (𝐅 q)) :: 𝐅 (𝐆 p) :: 𝐆 (𝐅 q) ::
      [(𝐅 (𝐆 p) ⋏ 𝐆 (𝐅 q))] ⊢ [𝐗 (𝐅 (𝐆 p) ⋏ 𝐆 (𝐅 q))] :=
    Derives.cut (A := 𝐗 (𝐅 (𝐆 p))) h1 h2
  have h : 𝐅 (𝐆 p) :: 𝐆 (𝐅 q) :: [(𝐅 (𝐆 p) ⋏ 𝐆 (𝐅 q))] ⊢
      [𝐗 (𝐅 (𝐆 p) ⋏ 𝐆 (𝐅 q))] :=
    Derives.alwaysL (A := 𝐅 q) (by simp) h'
  exact Derives.andL (A := 𝐅 (𝐆 p)) (B := 𝐆 (𝐅 q)) (by simp) h

theorem Gp_GFq_aux {AP : Type} (p q : Formula AP) :
    [𝐆 (𝐅 q), 𝐆 p] ⊢ [𝐅 (p ⋏ q)] := by
  have a : 𝐆 p :: [q] ⊢ p :: (p ⋏ q) :: 𝐗 (𝐅 (p ⋏ q)) :: 𝐅 (p ⋏ q) ::
      [(𝐆 p) ⇒ (𝐅 (p ⋏ q))] :=
    Derives.alwaysL (A := p) (by simp) (Derives.ax (A := p) (by simp) (by simp))
  have b : 𝐆 p :: [q] ⊢ q :: (p ⋏ q) :: 𝐗 (𝐅 (p ⋏ q)) :: 𝐅 (p ⋏ q) ::
      [(𝐆 p) ⇒ (𝐅 (p ⋏ q))] :=
    Derives.ax (A := q) (by simp) (by simp)
  have n1'' : 𝐆 p :: [q] ⊢ (p ⋏ q) :: 𝐗 (𝐅 (p ⋏ q)) :: 𝐅 (p ⋏ q) ::
      [(𝐆 p) ⇒ (𝐅 (p ⋏ q))] :=
    Derives.andR (A := p) (B := q) (by simp) a b
  have n1' : 𝐆 p :: [q] ⊢ 𝐅 (p ⋏ q) :: [(𝐆 p) ⇒ (𝐅 (p ⋏ q))] :=
    Derives.evR (A := p ⋏ q) (by simp) n1''
  have n1 : [q] ⊢ [(𝐆 p) ⇒ (𝐅 (p ⋏ q))] :=
    Derives.impR (A := 𝐆 p) (B := 𝐅 (p ⋏ q)) (by simp) n1'
  have n2 : [𝐗 ((𝐆 p) ⇒ (𝐅 (p ⋏ q)))] ⊢ [(𝐆 p) ⇒ (𝐅 (p ⋏ q))] :=
    back_aux p (p ⋏ q)
  have n3 : ((𝐆 p) ⇒ (𝐅 (p ⋏ q))) :: 𝐅 q :: 𝐗 (𝐆 (𝐅 q)) ::
      [𝐆 (𝐅 q), 𝐆 p] ⊢ [𝐅 (p ⋏ q)] :=
    Derives.impL (A := 𝐆 p) (B := 𝐅 (p ⋏ q)) (by simp)
      (Derives.ax (A := 𝐆 p) (by simp) (by simp))
      (Derives.ax (A := 𝐅 (p ⋏ q)) (by simp) (by simp))
  have n : 𝐅 q :: 𝐗 (𝐆 (𝐅 q)) :: [𝐆 (𝐅 q), 𝐆 p] ⊢ [𝐅 (p ⋏ q)] :=
    Derives.evL (A := q) (I := (𝐆 p) ⇒ (𝐅 (p ⋏ q))) (by simp) n1 n2 n3
  exact Derives.alwaysL (A := 𝐅 q) (by simp) n

theorem J_goal_aux {AP : Type} (p q : Formula AP) :
    [(𝐅 (𝐆 p) ⋏ 𝐆 (𝐅 q))] ⊢ [𝐅 (p ⋏ q)] := by
  have k1' : 𝐆 (𝐅 q) :: [𝐆 p] ⊢ 𝐅 (p ⋏ q) :: [(𝐆 (𝐅 q)) ⇒ (𝐅 (p ⋏ q))] :=
    Derives.wk (Gp_GFq_aux p q) (by simp) (by simp)
  have k1 : [𝐆 p] ⊢ [(𝐆 (𝐅 q)) ⇒ (𝐅 (p ⋏ q))] :=
    Derives.impR (A := 𝐆 (𝐅 q)) (B := 𝐅 (p ⋏ q)) (by simp) k1'
  have k2 : [𝐗 ((𝐆 (𝐅 q)) ⇒ (𝐅 (p ⋏ q)))] ⊢ [(𝐆 (𝐅 q)) ⇒ (𝐅 (p ⋏ q))] :=
    back_aux (𝐅 q) (p ⋏ q)
  have k3 : ((𝐆 (𝐅 q)) ⇒ (𝐅 (p ⋏ q))) :: 𝐅 (𝐆 p) :: 𝐆 (𝐅 q) ::
      [(𝐅 (𝐆 p) ⋏ 𝐆 (𝐅 q))] ⊢ [𝐅 (p ⋏ q)] :=
    Derives.impL (A := 𝐆 (𝐅 q)) (B := 𝐅 (p ⋏ q)) (by simp)
      (Derives.ax (A := 𝐆 (𝐅 q)) (by simp) (by simp))
      (Derives.ax (A := 𝐅 (p ⋏ q)) (by simp) (by simp))
  have k : 𝐅 (𝐆 p) :: 𝐆 (𝐅 q) :: [(𝐅 (𝐆 p) ⋏ 𝐆 (𝐅 q))] ⊢ [𝐅 (p ⋏ q)] :=
    Derives.evL (A := 𝐆 p) (I := (𝐆 (𝐅 q)) ⇒ (𝐅 (p ⋏ q))) (by simp) k1 k2 k3
  exact Derives.andL (A := 𝐅 (𝐆 p)) (B := 𝐆 (𝐅 q)) (by simp) k

theorem candidate {AP : Type} (p q : Formula AP) :
    [(𝐅 (𝐆 (p)) ⋏ 𝐆 (𝐅 (q)))] ⊢ [𝐆 (𝐅 ((p ⋏ q)))] := by
  exact Derives.alwaysR (A := 𝐅 (p ⋏ q)) (I := (𝐅 (𝐆 p) ⋏ 𝐆 (𝐅 q))) (by simp)
    (Derives.ax (A := (𝐅 (𝐆 p) ⋏ 𝐆 (𝐅 q))) (by simp) (by simp))
    (J_step_aux p q) (J_goal_aux p q)

end Candidate

theorem verified {AP : Type} (p q : Formula AP) :
    [(𝐅 (𝐆 (p)) ⋏ 𝐆 (𝐅 (q)))] ⊢ [𝐆 (𝐅 ((p ⋏ q)))] :=
  Candidate.candidate p q

#print axioms verified
