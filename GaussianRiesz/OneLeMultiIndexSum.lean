import GaussianRiesz.MultiIndexSum
theorem OneLeMultiIndexSum {n : ℕ} (α : Fin n → ℕ) (hα : α ≠ 0) :
    (1 : ℝ) ≤ (MultiIndexSum α : ℝ) := by
  -- a finite sum of naturals vanishes only if every term does, so `|α| ≠ 0`
  have hne : MultiIndexSum α ≠ 0 := by
    simp only [MultiIndexSum]
    intro h00
    refine hα (funext fun j => ?_)
    exact Finset.sum_eq_zero_iff.mp h00 j (Finset.mem_univ j)
  exact Nat.one_le_cast.mpr (Nat.one_le_iff_ne_zero.mpr hne)
