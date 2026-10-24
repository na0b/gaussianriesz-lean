import GaussianRiesz.GaussCharFun
import GaussianRiesz.GaussIsProb
open MeasureTheory
theorem GaussMixPushforward {n : ℕ} (a b : ℝ) (ha0 : (0:ℝ) ≤ a) (hb0 : (0:ℝ) ≤ b)
    (hab : a ^ 2 + b ^ 2 = 1) :
    ((GaussMeasure n).prod (GaussMeasure n)).map
        (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) => a • p.1 + b • p.2)
      = GaussMeasure n := by
  have hmeas : Measurable
      (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
        a • p.1 + b • p.2) := by fun_prop
  have : IsProbabilityMeasure (((GaussMeasure n).prod (GaussMeasure n)).map
      (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) => a • p.1 + b • p.2)) :=
    Measure.isProbabilityMeasure_map hmeas.aemeasurable
  refine Measure.ext_of_charFun (funext fun t => ?_)
  rw [charFun_apply, integral_map hmeas.aemeasurable (by fun_prop)]
  have hsplit : ∀ p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n),
      Complex.exp ((inner ℝ (a • p.1 + b • p.2) t : ℝ) * Complex.I)
        = Complex.exp ((inner ℝ p.1 (a • t) : ℝ) * Complex.I)
          * Complex.exp ((inner ℝ p.2 (b • t) : ℝ) * Complex.I) := by
    intro p
    rw [← Complex.exp_add]
    congr 1
    rw [inner_add_left, real_inner_smul_left, real_inner_smul_left,
      real_inner_smul_right, real_inner_smul_right]
    push_cast
    ring
  rw [integral_congr_ae (Filter.Eventually.of_forall hsplit),
    integral_prod_mul (μ := GaussMeasure n) (ν := GaussMeasure n)
      (fun x : EuclideanSpace ℝ (Fin n) => Complex.exp ((inner ℝ x (a • t) : ℝ) * Complex.I))
      (fun y : EuclideanSpace ℝ (Fin n) => Complex.exp ((inner ℝ y (b • t) : ℝ) * Complex.I))]
  rw [← charFun_apply, ← charFun_apply, GaussCharFun, GaussCharFun, GaussCharFun, ← Complex.exp_add]
  congr 1
  rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg ha0,
    abs_of_nonneg hb0]
  have hc : (a:ℂ) ^ 2 + (b:ℂ) ^ 2 = 1 := by
    rw [show ((a:ℂ))^2 + ((b:ℂ))^2 = ((a^2 + b^2 : ℝ) : ℂ) from by push_cast; ring, hab]
    norm_num
  push_cast
  field_simp
  ring_nf
  linear_combination (-(‖t‖:ℂ)^2) * hc
