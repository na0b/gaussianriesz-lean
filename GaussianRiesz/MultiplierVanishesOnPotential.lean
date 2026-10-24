import GaussianRiesz.VariationalInequality
import GaussianRiesz.ObstacleMultiplier
open MeasureTheory
theorem MultiplierVanishesOnPotential {n : ℕ} (F : Lp ℝ 2 (GaussMeasure n)) (a : ℝ)
    (u : Lp ℝ 2 (GaussMeasure n)) (hu : u ∈ ObstacleCone n)
    (hmin : ∀ w ∈ ObstacleCone n, ObstacleFunctional F a u ≤ ObstacleFunctional F a w) :
    ObstacleMultiplier F a u u = 0 := by
  obtain ⟨huE, hunn⟩ := hu
  -- `0` lies in the cone
  have hE0 : Energy (0 : Lp ℝ 2 (GaussMeasure n)) = 0 := by
    have hz : ∀ α : {α : Fin n → ℕ // α ≠ 0},
        ENNReal.ofReal ((MultiIndexSum (α : Fin n → ℕ) : ℝ) ^ ((1 : ℝ) / 2)
          * ((HermiteBasis n).repr (0 : Lp ℝ 2 (GaussMeasure n)) (α : Fin n → ℕ)) ^ 2)
          = 0 := by
      intro α; simp
    rw [Energy, tsum_congr hz, tsum_zero]
  have hcone0 : (0 : Lp ℝ 2 (GaussMeasure n)) ∈ ObstacleCone n := by
    refine ⟨by rw [hE0]; exact ENNReal.zero_ne_top, ?_⟩
    filter_upwards [Lp.coeFn_zero (E := ℝ) (p := 2) (μ := GaussMeasure n)] with x hx
    rw [hx]
  -- `2u` lies in the cone
  have hE2 : Energy ((2 : ℝ) • u) = ENNReal.ofReal 4 * Energy u := by
    rw [Energy, Energy, ← ENNReal.tsum_mul_left]
    refine tsum_congr fun α => ?_
    have hr : (HermiteBasis n).repr ((2 : ℝ) • u) (α : Fin n → ℕ)
        = 2 * (HermiteBasis n).repr u (α : Fin n → ℕ) := by
      rw [map_smul, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul]
    rw [hr, show (MultiIndexSum (α : Fin n → ℕ) : ℝ) ^ ((1 : ℝ) / 2)
        * (2 * (HermiteBasis n).repr u (α : Fin n → ℕ)) ^ 2
        = 4 * ((MultiIndexSum (α : Fin n → ℕ) : ℝ) ^ ((1 : ℝ) / 2)
            * ((HermiteBasis n).repr u (α : Fin n → ℕ)) ^ 2) from by ring,
      ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 4)]
  have hcone2 : ((2 : ℝ) • u) ∈ ObstacleCone n := by
    refine ⟨?_, ?_⟩
    · rw [hE2]
      exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top huE
    · filter_upwards [Lp.coeFn_smul (2 : ℝ) u, hunn] with x hx hy
      rw [hx]
      simp only [Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hy ⊢
      linarith
  -- abbreviations
  set I : ℝ := ∫ x, ((F : EuclideanSpace ℝ (Fin n) → ℝ) x - a)
      * (u : EuclideanSpace ℝ (Fin n) → ℝ) x ∂(GaussMeasure n) with hI
  -- test `v = 2u`
  have hsub2 : (2 : ℝ) • u - u = u := by
    rw [two_smul]; abel
  have hVI2 := VariationalInequality F a u ⟨huE, hunn⟩ hmin ((2 : ℝ) • u) hcone2
  rw [hsub2] at hVI2
  have hlhs2 : ∫ x, ((F : EuclideanSpace ℝ (Fin n) → ℝ) x - a)
      * ((((2 : ℝ) • u : Lp ℝ 2 (GaussMeasure n)) : EuclideanSpace ℝ (Fin n) → ℝ) x
        - (u : EuclideanSpace ℝ (Fin n) → ℝ) x) ∂(GaussMeasure n) = I := by
    rw [hI]
    refine integral_congr_ae ?_
    filter_upwards [Lp.coeFn_smul (2 : ℝ) u] with x hx
    rw [hx]
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  rw [hlhs2] at hVI2
  -- test `v = 0`
  have hsub0 : (0 : Lp ℝ 2 (GaussMeasure n)) - u = -u := zero_sub u
  have hVI0 := VariationalInequality F a u ⟨huE, hunn⟩ hmin (0 : Lp ℝ 2 (GaussMeasure n)) hcone0
  rw [hsub0] at hVI0
  have hbilneg : EnergyBil u (-u) = -EnergyBil u u := by
    rw [EnergyBil, EnergyBil, ← tsum_neg]
    refine tsum_congr fun α => ?_
    rw [map_neg, lp.coeFn_neg, Pi.neg_apply]
    ring
  have hlhs0 : ∫ x, ((F : EuclideanSpace ℝ (Fin n) → ℝ) x - a)
      * ((((0 : Lp ℝ 2 (GaussMeasure n)) : EuclideanSpace ℝ (Fin n) → ℝ) x
        - (u : EuclideanSpace ℝ (Fin n) → ℝ) x)) ∂(GaussMeasure n) = -I := by
    rw [hI, ← integral_neg]
    refine integral_congr_ae ?_
    filter_upwards [Lp.coeFn_zero (E := ℝ) (p := 2) (μ := GaussMeasure n)] with x hx
    rw [hx]
    simp only [Pi.zero_apply]
    ring
  rw [hlhs0, hbilneg] at hVI0
  -- combine
  rw [ObstacleMultiplier, ← hI]
  linarith
