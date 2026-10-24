import GaussianRiesz.GaussMeasure
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
open MeasureTheory
instance GaussIsProb (n : ℕ) : IsProbabilityMeasure (GaussMeasure n) := by
  constructor
  -- the real Gaussian is integrable on `EuclideanSpace ℝ (Fin n)`
  have hint : Integrable (fun v : EuclideanSpace ℝ (Fin n) => Real.exp (-‖v‖ ^ 2)) volume := by
    have h := (GaussianFourier.integrable_cexp_neg_mul_sq_norm_add
        (V := EuclideanSpace ℝ (Fin n)) (b := (1 : ℂ)) (by norm_num) 0 0).re
    refine h.congr ?_
    filter_upwards with v
    simp only [zero_mul, add_zero, neg_mul, one_mul]
    rw [show (-((‖v‖ : ℝ) : ℂ) ^ 2) = (((-‖v‖ ^ 2 : ℝ)) : ℂ) by push_cast; ring]
    exact Complex.exp_ofReal_re _
  have hintc : Integrable (fun x : EuclideanSpace ℝ (Fin n) =>
      Real.pi ^ (-(n : ℝ) / 2) * Real.exp (-‖x‖ ^ 2)) volume := hint.const_mul _
  have hnn : 0 ≤ᵐ[(volume : Measure (EuclideanSpace ℝ (Fin n)))]
      fun x => Real.pi ^ (-(n : ℝ) / 2) * Real.exp (-‖x‖ ^ 2) := by
    filter_upwards with x
    have : (0 : ℝ) < Real.pi ^ (-(n : ℝ) / 2) := Real.rpow_pos_of_pos Real.pi_pos _
    positivity
  -- the normalization computation
  have hval : ∫ x : EuclideanSpace ℝ (Fin n),
      Real.pi ^ (-(n : ℝ) / 2) * Real.exp (-‖x‖ ^ 2) = 1 := by
    rw [integral_const_mul]
    have hre : (fun v : EuclideanSpace ℝ (Fin n) => Real.exp (-‖v‖ ^ 2))
        = fun v : EuclideanSpace ℝ (Fin n) => Real.exp (-(1 : ℝ) * ‖v‖ ^ 2) := by
      funext v; rw [neg_one_mul]
    rw [hre, GaussianFourier.integral_rexp_neg_mul_sq_norm (b := (1 : ℝ)) (by norm_num)]
    simp only [div_one, finrank_euclideanSpace, Fintype.card_fin]
    rw [← Real.rpow_add Real.pi_pos, neg_div, neg_add_cancel, Real.rpow_zero]
  rw [GaussMeasure, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal hintc hnn, hval, ENNReal.ofReal_one]
