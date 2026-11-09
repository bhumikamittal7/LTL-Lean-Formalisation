import LTL

open LTL

-- LTL law 131: □ ((p ⇒ ◇ (q ∨ r)) ∧ (q ⇒ ◇ s) ∧ (r ⇒ ◇ s)) ⟹ (p ⇒ ◇ s)
-- (the proposer's answer starts at line 9)

namespace Candidate
theorem aux_base {AP : Type} (p q r s : Formula AP) :
    [q ⋎ r] ⊢ [(𝐆 (((p ⇒ 𝐅 ((q ⋎ r))) ⋏ ((q ⇒ 𝐅 (s)) ⋏ (r ⇒ 𝐅 (s)))))) ⇒ 𝐅 s] :=
  Derives.impR (A := 𝐆 (((p ⇒ 𝐅 ((q ⋎ r))) ⋏ ((q ⇒ 𝐅 (s)) ⋏ (r ⇒ 𝐅 (s))))))
    (B := 𝐅 s) (by simp)
    (Derives.alwaysL (A := ((p ⇒ 𝐅 ((q ⋎ r))) ⋏ ((q ⇒ 𝐅 (s)) ⋏ (r ⇒ 𝐅 (s))))) (by simp)
      (Derives.andL (A := (p ⇒ 𝐅 ((q ⋎ r)))) (B := ((q ⇒ 𝐅 (s)) ⋏ (r ⇒ 𝐅 (s)))) (by simp)
        (Derives.andL (A := (q ⇒ 𝐅 (s))) (B := (r ⇒ 𝐅 (s))) (by simp)
          (Derives.orL (A := q) (B := r) (by simp)
            (Derives.impL (A := q) (B := 𝐅 s) (by simp)
              (Derives.ax (A := q) (by simp) (by simp))
              (Derives.ax (A := 𝐅 s) (by simp) (by simp)))
            (Derives.impL (A := r) (B := 𝐅 s) (by simp)
              (Derives.ax (A := r) (by simp) (by simp))
              (Derives.ax (A := 𝐅 s) (by simp) (by simp)))))))

theorem aux_step {AP : Type} (p q r s : Formula AP) :
    [𝐗 ((𝐆 (((p ⇒ 𝐅 ((q ⋎ r))) ⋏ ((q ⇒ 𝐅 (s)) ⋏ (r ⇒ 𝐅 (s)))))) ⇒ 𝐅 s)] ⊢
      [(𝐆 (((p ⇒ 𝐅 ((q ⋎ r))) ⋏ ((q ⇒ 𝐅 (s)) ⋏ (r ⇒ 𝐅 (s)))))) ⇒ 𝐅 s] :=
  Derives.impR (A := 𝐆 (((p ⇒ 𝐅 ((q ⋎ r))) ⋏ ((q ⇒ 𝐅 (s)) ⋏ (r ⇒ 𝐅 (s))))))
    (B := 𝐅 s) (by simp)
    (Derives.alwaysL (A := ((p ⇒ 𝐅 ((q ⋎ r))) ⋏ ((q ⇒ 𝐅 (s)) ⋏ (r ⇒ 𝐅 (s))))) (by simp)
      (Derives.evR (A := s) (by simp)
        (Derives.step
          (Γ' := [(𝐆 (((p ⇒ 𝐅 ((q ⋎ r))) ⋏ ((q ⇒ 𝐅 (s)) ⋏ (r ⇒ 𝐅 (s)))))) ⇒ 𝐅 s,
                  𝐆 (((p ⇒ 𝐅 ((q ⋎ r))) ⋏ ((q ⇒ 𝐅 (s)) ⋏ (r ⇒ 𝐅 (s)))))])
          (B := 𝐅 s)
          (Derives.impL (A := 𝐆 (((p ⇒ 𝐅 ((q ⋎ r))) ⋏ ((q ⇒ 𝐅 (s)) ⋏ (r ⇒ 𝐅 (s))))))
            (B := 𝐅 s) (by simp)
            (Derives.ax (A := 𝐆 (((p ⇒ 𝐅 ((q ⋎ r))) ⋏ ((q ⇒ 𝐅 (s)) ⋏ (r ⇒ 𝐅 (s))))))
              (by simp) (by simp))
            (Derives.ax (A := 𝐅 s) (by simp) (by simp)))
          (by simp) (by simp))))

theorem candidate {AP : Type} (p q r s : Formula AP) :
    [𝐆 (((p ⇒ 𝐅 ((q ⋎ r))) ⋏ ((q ⇒ 𝐅 (s)) ⋏ (r ⇒ 𝐅 (s)))))] ⊢ [(p ⇒ 𝐅 (s))] :=
  Derives.impR (A := p) (B := 𝐅 s) (by simp)
    (Derives.alwaysL (A := ((p ⇒ 𝐅 ((q ⋎ r))) ⋏ ((q ⇒ 𝐅 (s)) ⋏ (r ⇒ 𝐅 (s))))) (by simp)
      (Derives.andL (A := (p ⇒ 𝐅 ((q ⋎ r)))) (B := ((q ⇒ 𝐅 (s)) ⋏ (r ⇒ 𝐅 (s)))) (by simp)
        (Derives.impL (A := p) (B := 𝐅 (q ⋎ r)) (by simp)
          (Derives.ax (A := p) (by simp) (by simp))
          (Derives.evL (A := q ⋎ r)
            (I := (𝐆 (((p ⇒ 𝐅 ((q ⋎ r))) ⋏ ((q ⇒ 𝐅 (s)) ⋏ (r ⇒ 𝐅 (s)))))) ⇒ 𝐅 s)
            (by simp)
            (aux_base p q r s)
            (aux_step p q r s)
            (Derives.impL (A := 𝐆 (((p ⇒ 𝐅 ((q ⋎ r))) ⋏ ((q ⇒ 𝐅 (s)) ⋏ (r ⇒ 𝐅 (s))))))
              (B := 𝐅 s) (by simp)
              (Derives.ax (A := 𝐆 (((p ⇒ 𝐅 ((q ⋎ r))) ⋏ ((q ⇒ 𝐅 (s)) ⋏ (r ⇒ 𝐅 (s))))))
                (by simp) (by simp))
              (Derives.ax (A := 𝐅 s) (by simp) (by simp)))))))

end Candidate

theorem verified {AP : Type} (p q r s : Formula AP) :
    [𝐆 (((p ⇒ 𝐅 ((q ⋎ r))) ⋏ ((q ⇒ 𝐅 (s)) ⋏ (r ⇒ 𝐅 (s)))))] ⊢ [(p ⇒ 𝐅 (s))] :=
  Candidate.candidate p q r s

#print axioms verified
