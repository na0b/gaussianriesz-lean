import GaussianRiesz.Preamble
open MeasureTheory
theorem GaussianUnitIntegralLinearFactorBound :
    ∀ t R' : ℝ, 0 ≤ t → 0 ≤ R' →
      (t + R') * ∫ r in Set.Ioo (0:ℝ) 1, Real.exp (-(t ^ 2 / 4) * r ^ 2)
        ≤ 5 * R' + (5/2) * Real.sqrt Real.pi := by
  intro t R' ht0 hR'0
  have hvol : volume (Set.Ioo (0:ℝ) 1) ≠ ⊤ := by
    simp [Real.volume_Ioo]
  have hsp : (0:ℝ) ≤ Real.sqrt Real.pi := Real.sqrt_nonneg _
  have htR : (0:ℝ) ≤ t + R' := by linarith
  rcases le_or_gt t (4 * R') with hy | hy
  · have h1 : ∫ r in Set.Ioo (0:ℝ) 1, Real.exp (-(t ^ 2 / 4) * r ^ 2) ≤ 1 := by
      have hc : IntegrableOn (fun _ : ℝ => (1:ℝ)) (Set.Ioo (0:ℝ) 1) volume :=
        integrableOn_const hvol
      refine le_trans (integral_mono_of_nonneg
        (Filter.Eventually.of_forall fun r => (Real.exp_pos _).le) hc
        (Filter.Eventually.of_forall fun r => ?_)) ?_
      · rw [Real.exp_le_one_iff]
        have : (0:ℝ) ≤ t ^ 2 / 4 * r ^ 2 := by positivity
        linarith
      · simp [Real.volume_real_Ioo_of_le (by norm_num : (0:ℝ) ≤ 1)]
    calc (t + R') * ∫ r in Set.Ioo (0:ℝ) 1, Real.exp (-(t ^ 2 / 4) * r ^ 2)
        ≤ (t + R') * 1 := mul_le_mul_of_nonneg_left h1 htR
      _ = t + R' := by ring
      _ ≤ 5 * R' := by linarith
      _ ≤ 5 * R' + (5/2) * Real.sqrt Real.pi := by linarith
  · have hy0 : (0:ℝ) < t := by linarith
    have hb : (0:ℝ) < t ^ 2 / 4 := by positivity
    have h1 : ∫ r in Set.Ioo (0:ℝ) 1, Real.exp (-(t ^ 2 / 4) * r ^ 2)
        ≤ (2 / t) * Real.sqrt Real.pi := by
      refine le_trans (setIntegral_le_integral (integrable_exp_neg_mul_sq hb)
        (Filter.Eventually.of_forall fun r => (Real.exp_pos _).le)) ?_
      rw [integral_gaussian]
      have e1 : Real.pi / (t ^ 2 / 4) = (2 / t) ^ 2 * Real.pi := by
        field_simp
        ring
      rw [e1, Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]
    have h3 : (t + R') * (2 / t) ≤ 5/2 := by
      have e9 : (t + R') * (2 / t) = 2 + 2 * R' / t := by field_simp
      have e8 : 2 * R' / t ≤ 1/2 := by
        rw [div_le_iff₀ hy0]; linarith
      rw [e9]; linarith
    calc (t + R') * ∫ r in Set.Ioo (0:ℝ) 1, Real.exp (-(t ^ 2 / 4) * r ^ 2)
        ≤ (t + R') * ((2 / t) * Real.sqrt Real.pi) := mul_le_mul_of_nonneg_left h1 htR
      _ = ((t + R') * (2 / t)) * Real.sqrt Real.pi := by ring
      _ ≤ (5/2) * Real.sqrt Real.pi := mul_le_mul_of_nonneg_right h3 hsp
      _ ≤ 5 * R' + (5/2) * Real.sqrt Real.pi := by linarith
