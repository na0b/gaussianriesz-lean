import GaussianRiesz.EnergyBil
import GaussianRiesz.ObstacleFunctional
open MeasureTheory
noncomputable def ObstacleMultiplier {n : ℕ} (F : Lp ℝ 2 (GaussMeasure n)) (a : ℝ)
    (u φ : Lp ℝ 2 (GaussMeasure n)) : ℝ :=
  EnergyBil u φ
    - ∫ x, ((F : EuclideanSpace ℝ (Fin n) → ℝ) x - a) * (φ : EuclideanSpace ℝ (Fin n) → ℝ) x
        ∂(GaussMeasure n)
