module

public import GaussianRiesz.GaussIsProb

@[expose] public section
open MeasureTheory
theorem PosPartConstSubMemLp {n : ℕ} (F : Lp ℝ 2 (GaussMeasure n)) (a : ℝ) :
    MemLp (fun x => max (a - (F : EuclideanSpace ℝ (Fin n) → ℝ) x) 0) 2
      (GaussMeasure n) := by
  -- `a - F` is `L²`: the constant is, since `γₙ` is a probability measure
  have haF : MemLp (fun x => a - (F : EuclideanSpace ℝ (Fin n) → ℝ) x) 2 (GaussMeasure n) :=
    (memLp_const a).sub (Lp.memLp F)
  refine MemLp.of_le haF ?_ ?_
  · exact aestronglyMeasurable_iff_aemeasurable.mpr (haF.aestronglyMeasurable.aemeasurable.max aemeasurable_const)
  · filter_upwards with x
    rw [Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (le_max_right (a - (F : EuclideanSpace ℝ (Fin n) → ℝ) x) 0)]
    rcases le_total (a - (F : EuclideanSpace ℝ (Fin n) → ℝ) x) 0 with h | h
    · rw [max_eq_right h]; positivity
    · rw [max_eq_left h]; exact le_abs_self _
