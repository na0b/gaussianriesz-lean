module

public import GaussianRiesz.GaussMeasure

@[expose] public section
open MeasureTheory
theorem GaussCoordMemLp {n : ℕ} (W : Lp (EuclideanSpace ℝ (Fin n)) 2 (GaussMeasure n))
    (i : Fin n) :
    MemLp (fun x => (W : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) x i) 2
      (GaussMeasure n) := by
  refine MemLp.of_le (Lp.memLp W) ?_
    (Filter.Eventually.of_forall fun x => PiLp.norm_apply_le _ i)
  exact ((EuclideanSpace.proj (𝕜 := ℝ) i).continuous).comp_aestronglyMeasurable
    (Lp.aestronglyMeasurable W)
