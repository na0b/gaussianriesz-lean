module

public import GaussianRiesz.MultiplierVanishesOnPotential
public import GaussianRiesz.MultiplierPointwiseBound

@[expose] public section
open MeasureTheory
theorem Complementarity {n : ℕ} (F : Lp ℝ 2 (GaussMeasure n))
    (hF : 0 ≤ᵐ[GaussMeasure n] (F : EuclideanSpace ℝ (Fin n) → ℝ)) (a : ℝ) (ha : 0 < a)
    (u : Lp ℝ 2 (GaussMeasure n)) (hu : u ∈ ObstacleCone n)
    (hmin : ∀ w ∈ ObstacleCone n, ObstacleFunctional F a u ≤ ObstacleFunctional F a w)
    (η : Lp ℝ 2 (GaussMeasure n))
    (hη : ∀ φ : Lp ℝ 2 (GaussMeasure n), Energy φ ≠ ⊤ →
      ObstacleMultiplier F a u φ
        = ∫ x, (η : EuclideanSpace ℝ (Fin n) → ℝ) x
            * (φ : EuclideanSpace ℝ (Fin n) → ℝ) x ∂(GaussMeasure n)) :
    (∫ x, (η : EuclideanSpace ℝ (Fin n) → ℝ) x
        * (u : EuclideanSpace ℝ (Fin n) → ℝ) x ∂(GaussMeasure n)) = 0
      ∧ ∀ᵐ x ∂(GaussMeasure n), 0 < (u : EuclideanSpace ℝ (Fin n) → ℝ) x
          → (η : EuclideanSpace ℝ (Fin n) → ℝ) x = 0 := by
  obtain ⟨huE, hunn⟩ := hu
  -- `u ∈ 𝒦 ⊆ 𝒱`, so the representation hypothesis may be tested against `φ = u`
  have hzero : (∫ x, (η : EuclideanSpace ℝ (Fin n) → ℝ) x
      * (u : EuclideanSpace ℝ (Fin n) → ℝ) x ∂(GaussMeasure n)) = 0 := by
    rw [← hη u huE]
    exact MultiplierVanishesOnPotential F a u ⟨huE, hunn⟩ hmin
  refine ⟨hzero, ?_⟩
  -- the integrand is a.e. nonnegative and integrable, with integral zero
  have hbd := MultiplierPointwiseBound F hF a ha u ⟨huE, hunn⟩ hmin η hη
  have hint : Integrable (fun x => (η : EuclideanSpace ℝ (Fin n) → ℝ) x
      * (u : EuclideanSpace ℝ (Fin n) → ℝ) x) (GaussMeasure n) :=
    (Lp.memLp η).integrable_mul (Lp.memLp u)
  have hnn : 0 ≤ᵐ[GaussMeasure n] fun x => (η : EuclideanSpace ℝ (Fin n) → ℝ) x
      * (u : EuclideanSpace ℝ (Fin n) → ℝ) x := by
    filter_upwards [hbd, hunn] with x hx hy
    simp only [Pi.zero_apply] at hy ⊢
    exact mul_nonneg hx.1 hy
  have hae := (integral_eq_zero_iff_of_nonneg_ae hnn hint).mp hzero
  filter_upwards [hae] with x hx hux
  simp only [Pi.zero_apply] at hx
  exact (mul_eq_zero.mp hx).resolve_right (ne_of_gt hux)
