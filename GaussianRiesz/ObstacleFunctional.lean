module

public import GaussianRiesz.Energy

@[expose] public section
open MeasureTheory
noncomputable def ObstacleFunctional {n : ℕ} (F : Lp ℝ 2 (GaussMeasure n)) (a : ℝ)
    (v : Lp ℝ 2 (GaussMeasure n)) : ℝ :=
  (Energy v).toReal / 2
    + ∫ x, (a - (F : EuclideanSpace ℝ (Fin n) → ℝ) x) * (v : EuclideanSpace ℝ (Fin n) → ℝ) x
        ∂(GaussMeasure n)
