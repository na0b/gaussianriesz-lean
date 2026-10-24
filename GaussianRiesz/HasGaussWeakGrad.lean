import GaussianRiesz.GaussMeasure
open MeasureTheory
def HasGaussWeakGrad {n : ℕ} (v : EuclideanSpace ℝ (Fin n) → ℝ)
    (G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) : Prop :=
  ∀ (j : Fin n) (φ : EuclideanSpace ℝ (Fin n) → ℝ),
    ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      ∫ x, v x * fderiv ℝ φ x (EuclideanSpace.single j 1) = -∫ x, G x j * φ x
