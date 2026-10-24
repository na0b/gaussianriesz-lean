import GaussianRiesz.OUSemigroupSpectral
open MeasureTheory
theorem OUSelfAdjointContraction {n : ℕ} (s : ℝ) (hs : 0 ≤ s)
    (v w : Lp ℝ 2 (GaussMeasure n)) :
    inner ℝ (OUSemigroup s v) w = inner ℝ v (OUSemigroup s w)
      ∧ ‖OUSemigroup s v‖ ≤ ‖v‖ := by
  have hspec : ∀ (z : Lp ℝ 2 (GaussMeasure n)) (α : Fin n → ℕ),
      (HermiteBasis n).repr (OUSemigroup s z) α
        = Real.exp (-s * MultiIndexSum α) * (HermiteBasis n).repr z α :=
    fun z α => OUSemigroupSpectral s hs z α
  have hmul : ∀ a b : ℝ, (inner ℝ a b : ℝ) = a * b := by
    intro a b
    simp [RCLike.inner_apply, mul_comm]
  refine ⟨?_, ?_⟩
  · -- self-adjointness: the multiplier is the same on both sides, termwise
    rw [← (HermiteBasis n).repr.inner_map_map (OUSemigroup s v) w,
      ← (HermiteBasis n).repr.inner_map_map v (OUSemigroup s w),
      lp.inner_eq_tsum, lp.inner_eq_tsum]
    refine tsum_congr fun α => ?_
    rw [hmul, hmul, hspec v α, hspec w α]
    ring
  · -- contraction: the multiplier is bounded by `1` on every index
    have hbd : ∀ α : Fin n → ℕ,
        ‖(HermiteBasis n).repr (OUSemigroup s v) α‖
          ≤ ‖(HermiteBasis n).repr v α‖ := by
      intro α
      rw [hspec v α, norm_mul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      refine mul_le_of_le_one_left (norm_nonneg _) ?_
      rw [Real.exp_le_one_iff]
      have h0 : (0 : ℝ) ≤ (MultiIndexSum α : ℝ) := Nat.cast_nonneg _
      nlinarith
    have hs1 := lp.hasSum_norm (p := (2 : ENNReal)) (by norm_num)
      ((HermiteBasis n).repr (OUSemigroup s v))
    have hs2 := lp.hasSum_norm (p := (2 : ENNReal)) (by norm_num) ((HermiteBasis n).repr v)
    have hle : ‖(HermiteBasis n).repr (OUSemigroup s v)‖ ^ ((2 : ENNReal).toReal)
        ≤ ‖(HermiteBasis n).repr v‖ ^ ((2 : ENNReal).toReal) :=
      hasSum_le (fun α => Real.rpow_le_rpow (norm_nonneg _) (hbd α) ENNReal.toReal_nonneg)
        hs1 hs2
    have c1 : ∀ x : ℝ, x ^ ((2 : ENNReal).toReal) = x ^ (2 : ℕ) := by
      intro x
      rw [show ((2 : ENNReal)).toReal = ((2 : ℕ) : ℝ) from by norm_num, Real.rpow_natCast]
    rw [c1, c1] at hle
    rw [← (HermiteBasis n).repr.norm_map (OUSemigroup s v), ← (HermiteBasis n).repr.norm_map v]
    nlinarith [norm_nonneg ((HermiteBasis n).repr (OUSemigroup s v)),
      norm_nonneg ((HermiteBasis n).repr v), hle]
