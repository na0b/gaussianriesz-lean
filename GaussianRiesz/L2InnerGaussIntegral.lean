module

public import GaussianRiesz.GaussMeasure

@[expose] public section
open MeasureTheory
theorem L2InnerGaussIntegral {n : ℕ} (x y : Lp ℝ 2 (GaussMeasure n)) :
    (inner ℝ x y : ℝ) = ∫ z, (x : EuclideanSpace ℝ (Fin n) → ℝ) z
        * (y : EuclideanSpace ℝ (Fin n) → ℝ) z ∂(GaussMeasure n) := by
  rw [L2.inner_def]
  refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
  simp [RCLike.inner_apply, mul_comm]
