module

public import GaussianRiesz.HermiteFunDeriv
public import GaussianRiesz.MultiIndexSum

@[expose] public section
theorem HermiteFunOU {n : ℕ} (α : Fin n → ℕ) (x : EuclideanSpace ℝ (Fin n)) :
    ContDiff ℝ (2 : ℕ) (HermiteFun α)
      ∧ -(1 / 2 : ℝ) *
            (∑ j, fderiv ℝ (fun y => fderiv ℝ (HermiteFun α) y (EuclideanSpace.single j 1)) x
              (EuclideanSpace.single j 1))
          + ∑ j, x j * fderiv ℝ (HermiteFun α) x (EuclideanSpace.single j 1)
          = (MultiIndexSum α : ℝ) * HermiteFun α x := by
  refine ⟨(HermiteFunContDiff α).of_le (by norm_cast), ?_⟩
  -- (1) the one-variable three-term recurrence `√2 s h_k = √(k+1) h_{k+1} + √k h_{k-1}`
  have hrec1 : ∀ (k : ℕ) (s : ℝ),
      Real.sqrt 2 * s * Hermite1 k s
        = Real.sqrt (k + 1) * Hermite1 (k + 1) s + Real.sqrt k * Hermite1 (k - 1) s := by
    intro k s
    cases k with
    | zero =>
        simp [Hermite1, Polynomial.hermite_zero]
    | succ m =>
        have hdm := HermiteDerivative m
        have h2 : (Real.sqrt 2 * s) *
              Polynomial.aeval (Real.sqrt 2 * s) (Polynomial.hermite (m+1))
            = Polynomial.aeval (Real.sqrt 2 * s) (Polynomial.hermite (m+2))
              + ((m : ℝ)+1) * Polynomial.aeval (Real.sqrt 2 * s) (Polynomial.hermite m) := by
          have hX : Polynomial.X * Polynomial.hermite (m+1)
              = Polynomial.hermite (m+2)
                + Polynomial.derivative (Polynomial.hermite (m+1)) := by
            rw [Polynomial.hermite_succ (m+1)]
            ring
          have h3 : Polynomial.aeval (Real.sqrt 2 * s)
                (Polynomial.X * Polynomial.hermite (m+1))
              = Polynomial.aeval (Real.sqrt 2 * s)
                (Polynomial.hermite (m+2)
                  + Polynomial.derivative (Polynomial.hermite (m+1))) := by
            rw [hX]
          rw [hdm] at h3
          simp only [map_mul, map_add, Polynomial.aeval_X, nsmul_eq_mul, map_natCast] at h3
          push_cast at h3
          linarith [h3]
        simp only [Hermite1, Nat.add_sub_cancel]
        push_cast
        set A0 := Polynomial.aeval (Real.sqrt 2 * s) (Polynomial.hermite m) with hA0
        set A1 := Polynomial.aeval (Real.sqrt 2 * s) (Polynomial.hermite (m+1)) with hA1
        set A2 := Polynomial.aeval (Real.sqrt 2 * s) (Polynomial.hermite (m+1+1)) with hA2
        have hs : Real.sqrt ((m:ℝ)+1) * Real.sqrt ((m:ℝ)+1) = (m:ℝ)+1 :=
          Real.mul_self_sqrt (by positivity)
        have e2 : Real.sqrt ((Nat.factorial (m+1) : ℝ))
            = Real.sqrt ((m:ℝ)+1) * Real.sqrt ((Nat.factorial m : ℝ)) := by
          rw [← Real.sqrt_mul (by positivity)]
          congr 1
          rw [Nat.factorial_succ m]
          push_cast
          ring
        have e1 : Real.sqrt ((Nat.factorial (m+1+1) : ℝ))
            = Real.sqrt ((m:ℝ)+1+1) * Real.sqrt ((Nat.factorial (m+1) : ℝ)) := by
          rw [← Real.sqrt_mul (by positivity)]
          congr 1
          rw [Nat.factorial_succ (m+1)]
          push_cast
          ring
        rw [e1, e2]
        have r1 : Real.sqrt ((m:ℝ)+1+1) *
              (A2 / (Real.sqrt ((m:ℝ)+1+1) *
                (Real.sqrt ((m:ℝ)+1) * Real.sqrt ((Nat.factorial m : ℝ)))))
            = A2 / (Real.sqrt ((m:ℝ)+1) * Real.sqrt ((Nat.factorial m : ℝ))) := by
          field_simp
        have r2 : Real.sqrt ((m:ℝ)+1) * (A0 / Real.sqrt ((Nat.factorial m : ℝ)))
            = ((m:ℝ)+1) * A0
              / (Real.sqrt ((m:ℝ)+1) * Real.sqrt ((Nat.factorial m : ℝ))) := by
          have hx : ((m:ℝ)+1) * A0
                / (Real.sqrt ((m:ℝ)+1) * Real.sqrt ((Nat.factorial m : ℝ)))
              = (Real.sqrt ((m:ℝ)+1) * Real.sqrt ((m:ℝ)+1)) * A0
                / (Real.sqrt ((m:ℝ)+1) * Real.sqrt ((Nat.factorial m : ℝ))) := by
            rw [hs]
          rw [hx]
          field_simp
        rw [r1, r2, ← add_div, ← h2]
        ring
  -- (2) the same recurrence in the `j`-th coordinate of the `n`-variable Hermite functions
  have hrecN : ∀ (j : Fin n) (β : Fin n → ℕ) (y : EuclideanSpace ℝ (Fin n)),
      Real.sqrt 2 * (y j * HermiteFun β y)
        = Real.sqrt (β j + 1) * HermiteFun (Function.update β j (β j + 1)) y
          + Real.sqrt (β j) * HermiteFun (Function.update β j (β j - 1)) y := by
    intro j β y
    have hsplit : ∀ δ : Fin n → ℕ, HermiteFun δ y
        = Hermite1 (δ j) (y j) * ∏ i ∈ Finset.univ.erase j, Hermite1 (δ i) (y i) := by
      intro δ
      rw [HermiteFun]
      exact (Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ j)).symm
    have hR : ∀ (v : ℕ),
        (∏ i ∈ Finset.univ.erase j, Hermite1 ((Function.update β j v) i) (y i))
        = ∏ i ∈ Finset.univ.erase j, Hermite1 (β i) (y i) := by
      intro v
      refine Finset.prod_congr rfl ?_
      intro i hi
      rw [Function.update_of_ne (Finset.ne_of_mem_erase hi)]
    rw [hsplit β, hsplit (Function.update β j (β j + 1)),
      hsplit (Function.update β j (β j - 1)), hR, hR,
      Function.update_self, Function.update_self]
    have hh := hrec1 (β j) (y j)
    push_cast at hh ⊢
    linear_combination (∏ i ∈ Finset.univ.erase j, Hermite1 (β i) (y i)) * hh
  -- (3) the per-coordinate eigenvalue identity
  have hper : ∀ j : Fin n,
      -(1/2 : ℝ) * fderiv ℝ (fun y => fderiv ℝ (HermiteFun α) y (EuclideanSpace.single j 1)) x
          (EuclideanSpace.single j 1)
        + x j * fderiv ℝ (HermiteFun α) x (EuclideanSpace.single j 1)
        = (α j : ℝ) * HermiteFun α x := by
    intro j
    have hinnerfun : (fun y => fderiv ℝ (HermiteFun α) y (EuclideanSpace.single j 1))
        = fun y => Real.sqrt 2 * Real.sqrt (α j)
            * HermiteFun (Function.update α j (α j - 1)) y :=
      funext fun y => (HermiteFunDeriv α j y).2
    rw [hinnerfun, (HermiteFunDeriv α j x).2,
      fderiv_const_mul (HermiteFunDeriv (Function.update α j (α j - 1)) j x).1,
      smul_apply,
      (HermiteFunDeriv (Function.update α j (α j - 1)) j x).2, smul_eq_mul]
    rcases Nat.eq_zero_or_pos (α j) with haj | hpos
    · rw [haj]
      simp
    · obtain ⟨m, haj0⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.1 hpos)
      have haj : α j = m + 1 := haj0
      have hup1 : Function.update (Function.update α j m) j (m+1) = α := by
        rw [Function.update_idem, ← haj, Function.update_eq_self]
      have hup2 : Function.update (Function.update α j m) j (m-1)
          = Function.update α j (m-1) := by
        rw [Function.update_idem]
      rw [haj]
      simp only [Nat.add_sub_cancel, Function.update_self]
      rw [hup2]
      have hR := hrecN j (Function.update α j m) x
      rw [Function.update_self, hup1, hup2] at hR
      have h2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
      have hS : Real.sqrt ((m:ℝ)+1) * Real.sqrt ((m:ℝ)+1) = (m:ℝ)+1 :=
        Real.mul_self_sqrt (by positivity)
      push_cast at hR ⊢
      linear_combination
        (Real.sqrt ((m:ℝ)+1)) * hR
        + (-(1/2) * Real.sqrt ((m:ℝ)+1) * Real.sqrt (m:ℝ)
            * HermiteFun (Function.update α j (m - 1)) x) * h2
        + (HermiteFun α x) * hS
  -- (4) sum over the coordinates
  have hMI : (MultiIndexSum α : ℝ) = ∑ j, (α j : ℝ) := by
    simp only [MultiIndexSum]
    push_cast
    ring
  calc -(1 / 2 : ℝ) *
          (∑ j, fderiv ℝ (fun y => fderiv ℝ (HermiteFun α) y (EuclideanSpace.single j 1)) x
            (EuclideanSpace.single j 1))
        + ∑ j, x j * fderiv ℝ (HermiteFun α) x (EuclideanSpace.single j 1)
      = ∑ j, (-(1/2 : ℝ) *
            fderiv ℝ (fun y => fderiv ℝ (HermiteFun α) y (EuclideanSpace.single j 1)) x
              (EuclideanSpace.single j 1)
          + x j * fderiv ℝ (HermiteFun α) x (EuclideanSpace.single j 1)) := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum]
    _ = ∑ j, (α j : ℝ) * HermiteFun α x := Finset.sum_congr rfl fun j _ => hper j
    _ = (MultiIndexSum α : ℝ) * HermiteFun α x := by
        rw [← Finset.sum_mul, hMI]
