module

public import GaussianRiesz.EndpointTheorem

@[expose] public section
open MeasureTheory
set_option linter.unusedVariables false
theorem SpectralNormalizationBound {n : ℕ}
    (T : Lp ℝ 1 (GaussMeasure n) →ₗ[ℝ]
      (EuclideanSpace ℝ (Fin n) →ₘ[GaussMeasure n] EuclideanSpace ℝ (Fin n)))
    (hext : ∀ v : Lp ℝ 2 (GaussMeasure n),
      T (ToL1 v) = (RieszTransform v : EuclideanSpace ℝ (Fin n)
        →ₘ[GaussMeasure n] EuclideanSpace ℝ (Fin n)))
    (hT : ∀ (f : Lp ℝ 1 (GaussMeasure n)) (t : ℝ), 0 < t →
      ENNReal.ofReal t * GaussMeasure n {x | t < ‖T f x‖} ≤ ENNReal.ofReal (2 * ‖f‖))
    (f : Lp ℝ 1 (GaussMeasure n)) (t : ℝ) (ht : 0 < t) :
    ENNReal.ofReal t * GaussMeasure n
        {x | t < ‖((-Real.sqrt 2) • T) f x‖}
      ≤ ENNReal.ofReal (2 * Real.sqrt 2 * ‖f‖) := by
  have hs2 : (0:ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hsm : (((-Real.sqrt 2) • T) f) = (-Real.sqrt 2) • (T f) :=
    LinearMap.smul_apply _ _ _
  have hae : ∀ᵐ x ∂(GaussMeasure n),
      ‖((-Real.sqrt 2) • T) f x‖ = Real.sqrt 2 * ‖T f x‖ := by
    have h := AEEqFun.coeFn_smul (-Real.sqrt 2) (T f)
    rw [hsm]
    filter_upwards [h] with x hx
    rw [hx, Pi.smul_apply, norm_smul]
    simp [abs_of_nonneg hs2.le]
  have hcong : GaussMeasure n {x | t < ‖((-Real.sqrt 2) • T) f x‖}
      = GaussMeasure n {x | t / Real.sqrt 2 < ‖T f x‖} := by
    apply measure_congr
    filter_upwards [hae] with x hx
    have : (t < ‖((-Real.sqrt 2) • T) f x‖) ↔ (t / Real.sqrt 2 < ‖T f x‖) := by
      rw [hx, div_lt_iff₀ hs2, mul_comm]
    exact propext this
  rw [hcong]
  have hsplit : ENNReal.ofReal t
      = ENNReal.ofReal (Real.sqrt 2) * ENNReal.ofReal (t / Real.sqrt 2) := by
    rw [← ENNReal.ofReal_mul hs2.le]
    congr 1
    field_simp
  rw [hsplit, mul_assoc]
  calc ENNReal.ofReal (Real.sqrt 2)
        * (ENNReal.ofReal (t / Real.sqrt 2)
            * GaussMeasure n {x | t / Real.sqrt 2 < ‖T f x‖})
      ≤ ENNReal.ofReal (Real.sqrt 2) * ENNReal.ofReal (2 * ‖f‖) := by
        gcongr
        exact hT f (t / Real.sqrt 2) (div_pos ht hs2)
    _ = ENNReal.ofReal (2 * Real.sqrt 2 * ‖f‖) := by
        rw [← ENNReal.ofReal_mul hs2.le]
        congr 1
        ring
