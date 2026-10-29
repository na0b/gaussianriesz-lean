module

public import GaussianRiesz.ObstacleCoercivity
public import GaussianRiesz.HermiteZeroModeConstant

@[expose] public section
open MeasureTheory
theorem ObstacleSublevelBounded {n : ℕ} (F : Lp ℝ 2 (GaussMeasure n)) (m a : ℝ)
    (hm : m = ∫ x, (F : EuclideanSpace ℝ (Fin n) → ℝ) x ∂(GaussMeasure n)) (ha : m < a)
    (C : ℝ) (v : Lp ℝ 2 (GaussMeasure n)) (hv : v ∈ ObstacleCone n)
    (hJ : ObstacleFunctional F a v ≤ C) :
    ‖v‖ ^ 2 + (Energy v).toReal
      ≤ (C + ‖F - m • HermiteL2 (0 : Fin n → ℕ)‖ ^ 2) ^ 2 / (a - m) ^ 2
        + 8 * (C + ‖F - m • HermiteL2 (0 : Fin n → ℕ)‖ ^ 2) := by
  classical
  obtain ⟨hvE, hvnn⟩ := hv
  -- `h₀` is the constant function `1`, of norm `1`
  obtain ⟨-, hvh0, -, hhh, hnorm1⟩ := HermiteZeroModeConstant (n := n)
  have hvh := hvh0 v
  -- Step 2: Pythagoras for `v = c·1 + w`
  have hpyth : ‖v‖ ^ 2
      = ‖v - (∫ x, (v : EuclideanSpace ℝ (Fin n) → ℝ) x ∂(GaussMeasure n))
          • HermiteL2 (0 : Fin n → ℕ)‖ ^ 2
        + (∫ x, (v : EuclideanSpace ℝ (Fin n) → ℝ) x ∂(GaussMeasure n)) ^ 2 := by
    have horth : inner ℝ (v - (∫ x, (v : EuclideanSpace ℝ (Fin n) → ℝ) x ∂(GaussMeasure n))
          • HermiteL2 (0 : Fin n → ℕ))
        ((∫ x, (v : EuclideanSpace ℝ (Fin n) → ℝ) x ∂(GaussMeasure n))
          • HermiteL2 (0 : Fin n → ℕ)) = (0 : ℝ) := by
      simp only [inner_sub_left, real_inner_smul_left, real_inner_smul_right, hhh, hvh]
      ring
    have heq : (v - (∫ x, (v : EuclideanSpace ℝ (Fin n) → ℝ) x ∂(GaussMeasure n))
          • HermiteL2 (0 : Fin n → ℕ))
        + (∫ x, (v : EuclideanSpace ℝ (Fin n) → ℝ) x ∂(GaussMeasure n))
          • HermiteL2 (0 : Fin n → ℕ) = v := by abel
    have hps : ‖(v - (∫ x, (v : EuclideanSpace ℝ (Fin n) → ℝ) x ∂(GaussMeasure n))
          • HermiteL2 (0 : Fin n → ℕ))
        + (∫ x, (v : EuclideanSpace ℝ (Fin n) → ℝ) x ∂(GaussMeasure n))
          • HermiteL2 (0 : Fin n → ℕ)‖ ^ 2
        = ‖v - (∫ x, (v : EuclideanSpace ℝ (Fin n) → ℝ) x ∂(GaussMeasure n))
            • HermiteL2 (0 : Fin n → ℕ)‖ ^ 2
          + ‖(∫ x, (v : EuclideanSpace ℝ (Fin n) → ℝ) x ∂(GaussMeasure n))
            • HermiteL2 (0 : Fin n → ℕ)‖ ^ 2 := by
      rw [norm_add_sq_real, horth]
      ring
    rw [heq] at hps
    have hns : ‖(∫ x, (v : EuclideanSpace ℝ (Fin n) → ℝ) x ∂(GaussMeasure n))
        • HermiteL2 (0 : Fin n → ℕ)‖
        = |∫ x, (v : EuclideanSpace ℝ (Fin n) → ℝ) x ∂(GaussMeasure n)| := by
      rw [norm_smul, hnorm1, Real.norm_eq_abs, mul_one]
    rw [hps, hns, sq_abs]
  -- Step 1: the two separate bounds, from coercivity
  have hcoer := (ObstacleCoercivity F m a hm ha).1 v ⟨hvE, hvnn⟩
  have hc0 : 0 ≤ ∫ x, (v : EuclideanSpace ℝ (Fin n) → ℝ) x ∂(GaussMeasure n) :=
    integral_nonneg_of_ae hvnn
  have hE0 : (0 : ℝ) ≤ (Energy v).toReal := ENNReal.toReal_nonneg
  have ham : 0 < a - m := sub_pos.mpr ha
  have hwn : ‖v - (∫ x, (v : EuclideanSpace ℝ (Fin n) → ℝ) x ∂(GaussMeasure n))
        • HermiteL2 (0 : Fin n → ℕ)‖ ^ 2 ≤ (Energy v).toReal := by
    rw [← ProjZeroCentering v]
    exact (ENNReal.ofReal_le_iff_le_toReal hvE).mp (FractionalGap v)
  have hD0 : 0 ≤ C + ‖F - m • HermiteL2 (0 : Fin n → ℕ)‖ ^ 2 := by
    nlinarith [hcoer, hJ, hc0, hE0, ham]
  have hcle : (a - m) * (∫ x, (v : EuclideanSpace ℝ (Fin n) → ℝ) x ∂(GaussMeasure n))
      ≤ C + ‖F - m • HermiteL2 (0 : Fin n → ℕ)‖ ^ 2 := by
    nlinarith [hcoer, hJ, hE0]
  have hc2 : (∫ x, (v : EuclideanSpace ℝ (Fin n) → ℝ) x ∂(GaussMeasure n)) ^ 2
      ≤ (C + ‖F - m • HermiteL2 (0 : Fin n → ℕ)‖ ^ 2) ^ 2 / (a - m) ^ 2 := by
    rw [le_div_iff₀ (by positivity)]
    nlinarith [hcle, hc0, ham, hD0, mul_nonneg hc0 ham.le]
  have hEle : (Energy v).toReal ≤ 4 * (C + ‖F - m • HermiteL2 (0 : Fin n → ℕ)‖ ^ 2) := by
    nlinarith [hcoer, hJ, hc0, ham, mul_nonneg hc0 ham.le]
  rw [hpyth]
  nlinarith [hwn, hc2, hEle]
