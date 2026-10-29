module

public import GaussianRiesz.HermiteL2ZeroAEOne
public import GaussianRiesz.GaussIsProb
public import GaussianRiesz.L2InnerGaussIntegral

@[expose] public section
open MeasureTheory
theorem HermiteZeroModeConstant {n : ℕ} :
    (∀ f : EuclideanSpace ℝ (Fin n) → ℝ, (∫ x, f x *
        ((HermiteL2 (0 : Fin n → ℕ) : Lp ℝ 2 (GaussMeasure n)) :
          EuclideanSpace ℝ (Fin n) → ℝ) x ∂(GaussMeasure n)) = ∫ x, f x ∂(GaussMeasure n))
      ∧ (∀ v : Lp ℝ 2 (GaussMeasure n), (inner ℝ v (HermiteL2 (0 : Fin n → ℕ)) : ℝ)
          = ∫ x, (v : EuclideanSpace ℝ (Fin n) → ℝ) x ∂(GaussMeasure n))
      ∧ (∀ v : Lp ℝ 2 (GaussMeasure n), (inner ℝ (HermiteL2 (0 : Fin n → ℕ)) v : ℝ)
          = ∫ x, (v : EuclideanSpace ℝ (Fin n) → ℝ) x ∂(GaussMeasure n))
      ∧ (inner ℝ (HermiteL2 (0 : Fin n → ℕ)) (HermiteL2 (0 : Fin n → ℕ)) : ℝ) = 1
      ∧ ‖HermiteL2 (0 : Fin n → ℕ)‖ = 1 := by
  have hmul : ∀ f : EuclideanSpace ℝ (Fin n) → ℝ, (∫ x, f x *
      ((HermiteL2 (0 : Fin n → ℕ) : Lp ℝ 2 (GaussMeasure n)) :
        EuclideanSpace ℝ (Fin n) → ℝ) x ∂(GaussMeasure n)) = ∫ x, f x ∂(GaussMeasure n) := by
    intro f
    refine integral_congr_ae ?_
    filter_upwards [HermiteL2ZeroAEOne] with x hx
    rw [hx, mul_one]
  have hvh : ∀ v : Lp ℝ 2 (GaussMeasure n), (inner ℝ v (HermiteL2 (0 : Fin n → ℕ)) : ℝ)
      = ∫ x, (v : EuclideanSpace ℝ (Fin n) → ℝ) x ∂(GaussMeasure n) := fun v => by
    rw [L2InnerGaussIntegral, hmul]
  have hhv : ∀ v : Lp ℝ 2 (GaussMeasure n), (inner ℝ (HermiteL2 (0 : Fin n → ℕ)) v : ℝ)
      = ∫ x, (v : EuclideanSpace ℝ (Fin n) → ℝ) x ∂(GaussMeasure n) := fun v => by
    rw [real_inner_comm, hvh]
  have hhh : (inner ℝ (HermiteL2 (0 : Fin n → ℕ)) (HermiteL2 (0 : Fin n → ℕ)) : ℝ) = 1 := by
    rw [hvh, show (1 : ℝ) = ∫ _z : EuclideanSpace ℝ (Fin n), (1 : ℝ) ∂(GaussMeasure n) from by
      simp]
    exact integral_congr_ae HermiteL2ZeroAEOne
  refine ⟨hmul, hvh, hhv, hhh, ?_⟩
  nlinarith [real_inner_self_eq_norm_sq (HermiteL2 (0 : Fin n → ℕ)), hhh,
    norm_nonneg (HermiteL2 (0 : Fin n → ℕ))]
