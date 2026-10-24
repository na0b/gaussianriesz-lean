import GaussianRiesz.GaussRieszKernel
open MeasureTheory
theorem GaussRieszKernelNearSliceBounds {n : ℕ} (j : Fin n) (M : ℝ) (hM : 3 ≤ M)
    (y : EuclideanSpace ℝ (Fin n)) (hy : ‖y‖ ≤ M) :
    (∀ (w : EuclideanSpace ℝ (Fin n)) (r : ℝ), 0 < r → r < 1 →
        ‖r • w - y‖ ^ 2 / (1 - r ^ 2)
          = ‖y‖ ^ 2 - ‖w‖ ^ 2 + ‖w - r • y‖ ^ 2 / (1 - r ^ 2))
      ∧ (∀ w : EuclideanSpace ℝ (Fin n), ‖w‖ ≤ M → ∀ r : ℝ, 0 < r → r < 1 →
          |(y j - r * w j) / ((1 - r ^ 2) ^ ((n : ℝ) / 2 + 1) * Real.sqrt (-Real.log r))
              * Real.exp (-‖r • w - y‖ ^ 2 / (1 - r ^ 2))|
            ≤ Real.exp (M ^ 2) * (‖w - y‖ + (1 - r) * M) * (1 - r) ^ (-(n : ℝ) / 2 - 3 / 2)
                * Real.exp (-‖w - r • y‖ ^ 2 / (2 * (1 - r))))
      ∧ ∃ G : EuclideanSpace ℝ (Fin n) → ℝ → EuclideanSpace ℝ (Fin n),
          (∀ w : EuclideanSpace ℝ (Fin n),
              ContinuousOn (fun r : ℝ => G w r) (Set.Ioo (0 : ℝ) 1))
            ∧ ∀ w : EuclideanSpace ℝ (Fin n), ‖w‖ ≤ M → ∀ r : ℝ, 0 < r → r < 1 →
                HasFDerivAt (fun v : EuclideanSpace ℝ (Fin n) =>
                    (y j - r * v j) / ((1 - r ^ 2) ^ ((n : ℝ) / 2 + 1) * Real.sqrt (-Real.log r))
                      * Real.exp (-‖r • v - y‖ ^ 2 / (1 - r ^ 2)))
                  (innerSL ℝ (G w r)) w
                  ∧ ‖G w r‖ ≤ Real.exp (M ^ 2) * (1 - r) ^ (-(n : ℝ) / 2 - 3 / 2)
                      * (1 + 2 * (‖w - y‖ + (1 - r) * M) ^ 2 / (1 - r))
                      * Real.exp (-‖w - r • y‖ ^ 2 / (2 * (1 - r))) := by
  have hcoord : ∀ (v : EuclideanSpace ℝ (Fin n)) (i : Fin n), |v i| ≤ ‖v‖ :=
    fun v i => by simpa using PiLp.norm_apply_le v i
  have hlog : ∀ r : ℝ, 0 < r → 1 - r ≤ -Real.log r := by
    intro r h0
    have := Real.log_le_sub_one_of_pos h0
    linarith
  -- the splitting identity, clause (a)
  have hsplit : ∀ (w : EuclideanSpace ℝ (Fin n)) (r : ℝ), 0 < r → r < 1 →
      ‖r • w - y‖ ^ 2 / (1 - r ^ 2)
        = ‖y‖ ^ 2 - ‖w‖ ^ 2 + ‖w - r • y‖ ^ 2 / (1 - r ^ 2) := by
    intro w r hr0 hr1
    have hne : (1 - r ^ 2) ≠ 0 := by nlinarith
    have e1 : ‖r • w - y‖ ^ 2 = r ^ 2 * ‖w‖ ^ 2 - 2 * (r * inner ℝ w y) + ‖y‖ ^ 2 := by
      rw [norm_sub_sq_real, real_inner_smul_left, norm_smul, Real.norm_eq_abs,
        abs_of_pos hr0]
      ring
    have e2 : ‖w - r • y‖ ^ 2 = ‖w‖ ^ 2 - 2 * (r * inner ℝ w y) + r ^ 2 * ‖y‖ ^ 2 := by
      rw [norm_sub_sq_real, real_inner_smul_right, norm_smul, Real.norm_eq_abs,
        abs_of_pos hr0]
      ring
    rw [e1, e2]
    field_simp
    ring
  -- the common exponential/prefactor estimate behind (7) and (8)
  have hpre : ∀ w : EuclideanSpace ℝ (Fin n), ‖w‖ ≤ M → ∀ r : ℝ, 0 < r → r < 1 →
      Real.exp (-‖r • w - y‖ ^ 2 / (1 - r ^ 2))
          / ((1 - r ^ 2) ^ ((n : ℝ) / 2 + 1) * Real.sqrt (-Real.log r))
        ≤ Real.exp (M ^ 2) * (1 - r) ^ (-(n : ℝ) / 2 - 3 / 2)
            * Real.exp (-‖w - r • y‖ ^ 2 / (2 * (1 - r))) := by
    intro w hw r hr0 hr1
    have hτ : (0:ℝ) < 1 - r := by linarith
    have hτ1 : 1 - r ≤ 1 := by linarith
    have hsq : (0:ℝ) < 1 - r ^ 2 := by nlinarith
    have hsq2 : 1 - r ^ 2 ≤ 2 * (1 - r) := by nlinarith
    have hsqge : 1 - r ≤ 1 - r ^ 2 := by nlinarith
    have hlogr : 0 < -Real.log r := by
      have := Real.log_neg hr0 hr1; linarith
    -- the exponential factor
    have hexp : Real.exp (-‖r • w - y‖ ^ 2 / (1 - r ^ 2))
        ≤ Real.exp (M ^ 2) * Real.exp (-‖w - r • y‖ ^ 2 / (2 * (1 - r))) := by
      rw [← Real.exp_add]
      refine Real.exp_le_exp.2 ?_
      have h1 := hsplit w r hr0 hr1
      have h2 : -‖r • w - y‖ ^ 2 / (1 - r ^ 2)
          = ‖w‖ ^ 2 - ‖y‖ ^ 2 - ‖w - r • y‖ ^ 2 / (1 - r ^ 2) := by
        rw [neg_div, h1]; ring
      have h3 : ‖w - r • y‖ ^ 2 / (2 * (1 - r)) ≤ ‖w - r • y‖ ^ 2 / (1 - r ^ 2) := by
        refine div_le_div_of_nonneg_left (by positivity) hsq ?_
        linarith
      have h4 : ‖w‖ ^ 2 ≤ M ^ 2 := by
        have := norm_nonneg w; nlinarith
      have h5 : (0:ℝ) ≤ ‖y‖ ^ 2 := by positivity
      rw [h2]
      simp only [neg_div]
      linarith
    -- the prefactor
    have hden : (1 - r) ^ ((n : ℝ) / 2 + 3 / 2)
        ≤ (1 - r ^ 2) ^ ((n : ℝ) / 2 + 1) * Real.sqrt (-Real.log r) := by
      have ha : (1 - r) ^ ((n : ℝ) / 2 + 1) ≤ (1 - r ^ 2) ^ ((n : ℝ) / 2 + 1) :=
        Real.rpow_le_rpow hτ.le hsqge (by positivity)
      have hb : (1 - r) ^ ((1:ℝ) / 2) ≤ Real.sqrt (-Real.log r) := by
        rw [← Real.sqrt_eq_rpow]
        exact Real.sqrt_le_sqrt (hlog r hr0)
      have hprod : (1 - r) ^ ((n : ℝ) / 2 + 1) * (1 - r) ^ ((1:ℝ) / 2)
          = (1 - r) ^ ((n : ℝ) / 2 + 3 / 2) := by
        rw [← Real.rpow_add hτ]; congr 1; ring
      calc (1 - r) ^ ((n : ℝ) / 2 + 3 / 2)
          = (1 - r) ^ ((n : ℝ) / 2 + 1) * (1 - r) ^ ((1:ℝ) / 2) := hprod.symm
        _ ≤ (1 - r ^ 2) ^ ((n : ℝ) / 2 + 1) * Real.sqrt (-Real.log r) := by
            refine mul_le_mul ha hb (by positivity) (by positivity)
    have hinv : ((1 - r ^ 2) ^ ((n : ℝ) / 2 + 1) * Real.sqrt (-Real.log r))⁻¹
        ≤ (1 - r) ^ (-(n : ℝ) / 2 - 3 / 2) := by
      rw [show (-(n : ℝ) / 2 - 3 / 2) = -((n : ℝ) / 2 + 3 / 2) by ring,
        Real.rpow_neg hτ.le]
      exact inv_anti₀ (by positivity) hden
    calc Real.exp (-‖r • w - y‖ ^ 2 / (1 - r ^ 2))
            / ((1 - r ^ 2) ^ ((n : ℝ) / 2 + 1) * Real.sqrt (-Real.log r))
        = Real.exp (-‖r • w - y‖ ^ 2 / (1 - r ^ 2))
            * ((1 - r ^ 2) ^ ((n : ℝ) / 2 + 1) * Real.sqrt (-Real.log r))⁻¹ := by
          rw [div_eq_mul_inv]
      _ ≤ (Real.exp (M ^ 2) * Real.exp (-‖w - r • y‖ ^ 2 / (2 * (1 - r))))
            * (1 - r) ^ (-(n : ℝ) / 2 - 3 / 2) :=
          mul_le_mul hexp hinv (by positivity) (by positivity)
      _ = Real.exp (M ^ 2) * (1 - r) ^ (-(n : ℝ) / 2 - 3 / 2)
            * Real.exp (-‖w - r • y‖ ^ 2 / (2 * (1 - r))) := by ring
  -- the two elementary numerator bounds of (6)
  have hPb : ∀ w : EuclideanSpace ℝ (Fin n), ‖w‖ ≤ M → ∀ r : ℝ, 0 < r → r < 1 →
      |y j - r * w j| ≤ ‖w - y‖ + (1 - r) * M := by
    intro w hw r hr0 hr1
    have hτ : (0:ℝ) ≤ 1 - r := by linarith
    have e1 : y j - r * w j = (y j - w j) + (1 - r) * w j := by ring
    have e2 : |y j - w j| ≤ ‖w - y‖ := by
      have := hcoord (y - w) j
      have h3 : (y - w) j = y j - w j := rfl
      rw [h3] at this
      rwa [norm_sub_rev] at this
    have e3 : |(1 - r) * w j| ≤ (1 - r) * M := by
      rw [abs_mul, abs_of_nonneg hτ]
      exact mul_le_mul_of_nonneg_left ((hcoord w j).trans hw) hτ
    calc |y j - r * w j| = |(y j - w j) + (1 - r) * w j| := by rw [e1]
      _ ≤ |y j - w j| + |(1 - r) * w j| := abs_add_le _ _
      _ ≤ ‖w - y‖ + (1 - r) * M := by linarith
  have hRb : ∀ w : EuclideanSpace ℝ (Fin n), ‖w‖ ≤ M → ∀ r : ℝ, 0 < r → r < 1 →
      ‖r • w - y‖ ≤ ‖w - y‖ + (1 - r) * M := by
    intro w hw r hr0 hr1
    have hτ : (0:ℝ) ≤ 1 - r := by linarith
    have e1 : r • w - y = (w - y) - (1 - r) • w := by
      rw [sub_smul, one_smul]; abel
    have e3 : ‖(1 - r) • w‖ ≤ (1 - r) * M := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hτ]
      exact mul_le_mul_of_nonneg_left hw hτ
    calc ‖r • w - y‖ = ‖(w - y) - (1 - r) • w‖ := by rw [e1]
      _ ≤ ‖w - y‖ + ‖(1 - r) • w‖ := norm_sub_le _ _
      _ ≤ ‖w - y‖ + (1 - r) * M := by linarith
  refine ⟨hsplit, ?_, ?_⟩
  · -- clause (b): bound (7)
    intro w hw r hr0 hr1
    have hτ : (0:ℝ) < 1 - r := by linarith
    have hsq : (0:ℝ) < 1 - r ^ 2 := by nlinarith
    have hlogr : 0 < -Real.log r := by
      have := Real.log_neg hr0 hr1; linarith
    have hApos : (0:ℝ) < (1 - r ^ 2) ^ ((n : ℝ) / 2 + 1) * Real.sqrt (-Real.log r) := by
      have : (0:ℝ) < Real.sqrt (-Real.log r) := Real.sqrt_pos.2 hlogr
      positivity
    have hpre' := hpre w hw r hr0 hr1
    have hnum := hPb w hw r hr0 hr1
    have hnn : (0:ℝ) ≤ ‖w - y‖ + (1 - r) * M := by positivity
    calc |(y j - r * w j) / ((1 - r ^ 2) ^ ((n : ℝ) / 2 + 1) * Real.sqrt (-Real.log r))
            * Real.exp (-‖r • w - y‖ ^ 2 / (1 - r ^ 2))|
        = |y j - r * w j| * (Real.exp (-‖r • w - y‖ ^ 2 / (1 - r ^ 2))
            / ((1 - r ^ 2) ^ ((n : ℝ) / 2 + 1) * Real.sqrt (-Real.log r))) := by
          rw [abs_mul, abs_div, abs_of_pos hApos, abs_of_pos (Real.exp_pos _)]
          ring
      _ ≤ (‖w - y‖ + (1 - r) * M) * (Real.exp (M ^ 2) * (1 - r) ^ (-(n : ℝ) / 2 - 3 / 2)
            * Real.exp (-‖w - r • y‖ ^ 2 / (2 * (1 - r)))) :=
          mul_le_mul hnum hpre' (by positivity) hnn
      _ = Real.exp (M ^ 2) * (‖w - y‖ + (1 - r) * M) * (1 - r) ^ (-(n : ℝ) / 2 - 3 / 2)
            * Real.exp (-‖w - r • y‖ ^ 2 / (2 * (1 - r))) := by ring
  · -- clause (c): the gradient field, its continuity in `r`, and bound (8)
    refine ⟨fun w r => (Real.exp (-‖r • w - y‖ ^ 2 / (1 - r ^ 2))
        / ((1 - r ^ 2) ^ ((n : ℝ) / 2 + 1) * Real.sqrt (-Real.log r)))
      • ((-r) • EuclideanSpace.single j (1:ℝ)
          - ((y j - r * w j) * (2 * r / (1 - r ^ 2))) • (r • w - y)), ?_, ?_⟩
    · intro w r hr
      obtain ⟨hr0, hr1⟩ := hr
      refine ContinuousAt.continuousWithinAt ?_
      have h1 : (1 - r ^ 2) ≠ 0 := by nlinarith
      have h2 : r ≠ 0 := ne_of_gt hr0
      have hlogr : 0 < -Real.log r := by
        have := Real.log_neg hr0 hr1; linarith
      have h4 : (1 - r ^ 2) ^ ((n : ℝ) / 2 + 1) ≠ 0 := by
        have : (0:ℝ) < 1 - r ^ 2 := by nlinarith
        positivity
      fun_prop (disch := first | assumption | positivity | simp_all)
    · intro w hw r hr0 hr1
      have hτ : (0:ℝ) < 1 - r := by linarith
      have hsq : (0:ℝ) < 1 - r ^ 2 := by nlinarith
      have hlogr : 0 < -Real.log r := by
        have := Real.log_neg hr0 hr1; linarith
      refine ⟨?_, ?_⟩
      · -- the derivative, in explicit gradient form
        simp only [div_eq_mul_inv]
        have hproj : HasFDerivAt (fun v : EuclideanSpace ℝ (Fin n) => v j)
            (innerSL ℝ (EuclideanSpace.single j (1:ℝ))) w := by
          have h := (innerSL ℝ (EuclideanSpace.single j (1:ℝ))).hasFDerivAt (x := w)
          simpa [EuclideanSpace.inner_single_left] using h
        have haff : HasFDerivAt (fun v : EuclideanSpace ℝ (Fin n) => r • v - y)
            (r • ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n))) w := by
          simpa using
            (((ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n))).hasFDerivAt
              (x := w)).const_smul r).sub_const y
        have hP : HasFDerivAt (fun v : EuclideanSpace ℝ (Fin n) => y j - r * v j)
            (-(r • innerSL ℝ (EuclideanSpace.single j (1:ℝ)))) w :=
          (hproj.const_mul r).const_sub (y j)
        have hns : HasFDerivAt (fun v : EuclideanSpace ℝ (Fin n) => ‖r • v - y‖ ^ 2)
            (2 • (innerSL ℝ (r • w - y)).comp
              (r • ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n)))) w := haff.norm_sq
        have hPA := HasFDerivAt.mul_const hP
          ((1 - r ^ 2) ^ ((n : ℝ) / 2 + 1) * Real.sqrt (-Real.log r))⁻¹
        have hE := HasFDerivAt.exp
          (HasFDerivAt.mul_const (HasFDerivAt.neg hns) ((1 - r ^ 2)⁻¹))
        refine (HasFDerivAt.mul hPA hE).congr_fderiv ?_
        ext h
        simp only [Pi.neg_apply]
        generalize Real.exp (-‖r • w - y‖ ^ 2 * (1 - r ^ 2)⁻¹) = Ev
        simp only [add_apply, smul_apply,
          neg_apply, ContinuousLinearMap.comp_apply,
          ContinuousLinearMap.coe_id', id_eq, innerSL_apply_apply, smul_eq_mul, inner_sub_left,
          real_inner_smul_left, real_inner_smul_right, EuclideanSpace.inner_single_left,
          two_smul, map_one]
        ring
      · -- bound (8)
        have hnum := hPb w hw r hr0 hr1
        have hRnum := hRb w hw r hr0 hr1
        have hnn : (0:ℝ) ≤ ‖w - y‖ + (1 - r) * M := by positivity
        have hfac : ‖(-r) • EuclideanSpace.single j (1:ℝ)
              - ((y j - r * w j) * (2 * r / (1 - r ^ 2))) • (r • w - y)‖
            ≤ 1 + 2 * (‖w - y‖ + (1 - r) * M) ^ 2 / (1 - r) := by
          have hone : ‖EuclideanSpace.single j (1:ℝ)‖ = 1 := by
            simp
          have h1 : ‖(-r) • EuclideanSpace.single j (1:ℝ)‖ ≤ 1 := by
            rw [norm_smul, Real.norm_eq_abs, hone, abs_neg, abs_of_pos hr0, mul_one]
            linarith
          have hcf : |(y j - r * w j) * (2 * r / (1 - r ^ 2))|
              ≤ (‖w - y‖ + (1 - r) * M) * (2 / (1 - r)) := by
            rw [abs_mul, abs_of_pos (by positivity : (0:ℝ) < 2 * r / (1 - r ^ 2))]
            refine mul_le_mul hnum ?_ (by positivity) hnn
            rw [div_le_div_iff₀ (by linarith) hτ]
            nlinarith
          have h2 : ‖((y j - r * w j) * (2 * r / (1 - r ^ 2))) • (r • w - y)‖
              ≤ 2 * (‖w - y‖ + (1 - r) * M) ^ 2 / (1 - r) := by
            rw [norm_smul, Real.norm_eq_abs]
            calc |(y j - r * w j) * (2 * r / (1 - r ^ 2))| * ‖r • w - y‖
                ≤ ((‖w - y‖ + (1 - r) * M) * (2 / (1 - r))) * (‖w - y‖ + (1 - r) * M) :=
                  mul_le_mul hcf hRnum (norm_nonneg _) (by positivity)
              _ = 2 * (‖w - y‖ + (1 - r) * M) ^ 2 / (1 - r) := by ring
          calc ‖(-r) • EuclideanSpace.single j (1:ℝ)
                - ((y j - r * w j) * (2 * r / (1 - r ^ 2))) • (r • w - y)‖
              ≤ ‖(-r) • EuclideanSpace.single j (1:ℝ)‖
                + ‖((y j - r * w j) * (2 * r / (1 - r ^ 2))) • (r • w - y)‖ := norm_sub_le _ _
            _ ≤ 1 + 2 * (‖w - y‖ + (1 - r) * M) ^ 2 / (1 - r) := by linarith
        have hpre' := hpre w hw r hr0 hr1
        rw [norm_smul, Real.norm_eq_abs,
          abs_of_pos (by positivity : (0:ℝ) < Real.exp (-‖r • w - y‖ ^ 2 / (1 - r ^ 2))
            / ((1 - r ^ 2) ^ ((n : ℝ) / 2 + 1) * Real.sqrt (-Real.log r)))]
        calc Real.exp (-‖r • w - y‖ ^ 2 / (1 - r ^ 2))
                / ((1 - r ^ 2) ^ ((n : ℝ) / 2 + 1) * Real.sqrt (-Real.log r))
              * ‖(-r) • EuclideanSpace.single j (1:ℝ)
                  - ((y j - r * w j) * (2 * r / (1 - r ^ 2))) • (r • w - y)‖
            ≤ (Real.exp (M ^ 2) * (1 - r) ^ (-(n : ℝ) / 2 - 3 / 2)
                * Real.exp (-‖w - r • y‖ ^ 2 / (2 * (1 - r))))
                * (1 + 2 * (‖w - y‖ + (1 - r) * M) ^ 2 / (1 - r)) :=
              mul_le_mul hpre' hfac (norm_nonneg _) (by positivity)
          _ = Real.exp (M ^ 2) * (1 - r) ^ (-(n : ℝ) / 2 - 3 / 2)
                * (1 + 2 * (‖w - y‖ + (1 - r) * M) ^ 2 / (1 - r))
                * Real.exp (-‖w - r • y‖ ^ 2 / (2 * (1 - r))) := by ring
