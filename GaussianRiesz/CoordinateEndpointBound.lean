import GaussianRiesz.EndpointTheorem
open MeasureTheory
set_option linter.unusedVariables false
theorem CoordinateEndpointBound {n : ℕ}
    (T : Lp ℝ 1 (GaussMeasure n) →ₗ[ℝ]
      (EuclideanSpace ℝ (Fin n) →ₘ[GaussMeasure n] EuclideanSpace ℝ (Fin n)))
    (hext : ∀ v : Lp ℝ 2 (GaussMeasure n),
      T (ToL1 v) = (RieszTransform v : EuclideanSpace ℝ (Fin n)
        →ₘ[GaussMeasure n] EuclideanSpace ℝ (Fin n)))
    (hT : ∀ (f : Lp ℝ 1 (GaussMeasure n)) (t : ℝ), 0 < t →
      ENNReal.ofReal t * GaussMeasure n {x | t < ‖T f x‖} ≤ ENNReal.ofReal (2 * ‖f‖))
    (f : Lp ℝ 1 (GaussMeasure n)) (j : Fin n) (t : ℝ) (ht : 0 < t) :
    ENNReal.ofReal t * GaussMeasure n {x | t < |T f x j|}
      ≤ ENNReal.ofReal (2 * ‖f‖) := by
  refine le_trans ?_ (hT f t ht)
  have hsub : {x | t < |T f x j|} ⊆ {x | t < ‖T f x‖} := by
    intro x hx
    exact lt_of_lt_of_le hx (by simpa using PiLp.norm_apply_le (T f x) j)
  gcongr
