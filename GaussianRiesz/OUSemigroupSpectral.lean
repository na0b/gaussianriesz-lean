import GaussianRiesz.OUSemigroup
import GaussianRiesz.Hermite1Zero
open MeasureTheory
theorem OUSemigroupSpectral {n : ℕ} (s : ℝ) (hs : 0 ≤ s) (v : Lp ℝ 2 (GaussMeasure n))
    (α : Fin n → ℕ) :
    (HermiteBasis n).repr (OUSemigroup s v) α
      = Real.exp (-s * MultiIndexSum α) * (HermiteBasis n).repr v α := by
  classical
  -- the multiplier is bounded by `1` on every index
  have hb : ∀ β : Fin n → ℕ, Real.exp (-s * (MultiIndexSum β : ℝ)) ≤ 1 := by
    intro β
    rw [Real.exp_le_one_iff]
    have h0 : (0 : ℝ) ≤ (MultiIndexSum β : ℝ) := Nat.cast_nonneg _
    nlinarith
  -- Parseval: the coefficient family of `v` is square summable
  have hv : Summable fun β : Fin n → ℕ =>
      ‖(HermiteBasis n).repr v β‖ ^ ((2 : ENNReal).toReal) :=
    (memℓp_gen_iff (p := (2 : ENNReal)) (by norm_num)).mp (lp.memℓp ((HermiteBasis n).repr v))
  -- hence so is the multiplied family
  have h : Memℓp (fun β : Fin n → ℕ =>
      Real.exp (-s * (MultiIndexSum β : ℝ)) * (HermiteBasis n).repr v β) 2 := by
    refine memℓp_gen (Summable.of_nonneg_of_le (fun β => ?_) (fun β => ?_) hv)
    · positivity
    · have h1 : ‖Real.exp (-s * (MultiIndexSum β : ℝ)) * (HermiteBasis n).repr v β‖
          ≤ ‖(HermiteBasis n).repr v β‖ := by
        rw [norm_mul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
        exact mul_le_of_le_one_left (norm_nonneg _) (hb β)
      exact Real.rpow_le_rpow (norm_nonneg _) h1 ENNReal.toReal_nonneg
  rw [OUSemigroup, dif_pos h]
  simp
