import GaussianRiesz.VariationalInequality
import GaussianRiesz.ObstacleMultiplier
open MeasureTheory
theorem MultiplierPositive {n : ℕ} (F : Lp ℝ 2 (GaussMeasure n)) (a : ℝ)
    (u : Lp ℝ 2 (GaussMeasure n)) (hu : u ∈ ObstacleCone n)
    (hmin : ∀ w ∈ ObstacleCone n, ObstacleFunctional F a u ≤ ObstacleFunctional F a w)
    (φ : Lp ℝ 2 (GaussMeasure n)) (hφ : φ ∈ ObstacleCone n) :
    0 ≤ ObstacleMultiplier F a u φ := by
  obtain ⟨huE, hunn⟩ := hu
  obtain ⟨hφE, hφnn⟩ := hφ
  -- the form domain is a linear subspace: `u + φ` still has finite energy
  have hadd : Energy (u + φ)
      ≤ ENNReal.ofReal 2 * Energy u + ENNReal.ofReal 2 * Energy φ := by
    rw [Energy, Energy, Energy, ← ENNReal.tsum_mul_left, ← ENNReal.tsum_mul_left,
      ← ENNReal.tsum_add]
    refine ENNReal.tsum_le_tsum fun α => ?_
    have hr : (HermiteBasis n).repr (u + φ) (α : Fin n → ℕ)
        = (HermiteBasis n).repr u (α : Fin n → ℕ) + (HermiteBasis n).repr φ (α : Fin n → ℕ) := by
      rw [map_add, lp.coeFn_add, Pi.add_apply]
    have hK : (0 : ℝ) ≤ (MultiIndexSum (α : Fin n → ℕ) : ℝ) ^ ((1 : ℝ) / 2) := by positivity
    have hsq : ((HermiteBasis n).repr u (α : Fin n → ℕ)
          + (HermiteBasis n).repr φ (α : Fin n → ℕ)) ^ 2
        ≤ 2 * ((HermiteBasis n).repr u (α : Fin n → ℕ)) ^ 2
          + 2 * ((HermiteBasis n).repr φ (α : Fin n → ℕ)) ^ 2 := by
      nlinarith [sq_nonneg ((HermiteBasis n).repr u (α : Fin n → ℕ)
        - (HermiteBasis n).repr φ (α : Fin n → ℕ))]
    rw [hr, ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2),
      ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2),
      ← ENNReal.ofReal_add (by positivity) (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    nlinarith [mul_le_mul_of_nonneg_left hsq hK]
  have hcone : (u + φ) ∈ ObstacleCone n := by
    refine ⟨?_, ?_⟩
    · refine ne_top_of_le_ne_top ?_ hadd
      exact ENNReal.add_ne_top.mpr
        ⟨ENNReal.mul_ne_top ENNReal.ofReal_ne_top huE,
         ENNReal.mul_ne_top ENNReal.ofReal_ne_top hφE⟩
    · filter_upwards [Lp.coeFn_add u φ, hunn, hφnn] with x hx hy hz
      simp only [Pi.zero_apply] at hy hz ⊢
      rw [hx]
      simpa using by linarith
  -- apply the variational inequality with the competitor `u + φ`
  have hVI := VariationalInequality F a u ⟨huE, hunn⟩ hmin (u + φ) hcone
  rw [add_sub_cancel_left] at hVI
  have hlhs : ∫ x, ((F : EuclideanSpace ℝ (Fin n) → ℝ) x - a)
      * (((u + φ : Lp ℝ 2 (GaussMeasure n)) : EuclideanSpace ℝ (Fin n) → ℝ) x
        - (u : EuclideanSpace ℝ (Fin n) → ℝ) x) ∂(GaussMeasure n)
      = ∫ x, ((F : EuclideanSpace ℝ (Fin n) → ℝ) x - a)
          * (φ : EuclideanSpace ℝ (Fin n) → ℝ) x ∂(GaussMeasure n) := by
    refine integral_congr_ae ?_
    filter_upwards [Lp.coeFn_add u φ] with x hx
    rw [hx]
    simp only [Pi.add_apply]
    ring
  rw [hlhs] at hVI
  rw [ObstacleMultiplier]
  linarith
