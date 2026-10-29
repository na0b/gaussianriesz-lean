module

public import GaussianRiesz.Energy

@[expose] public section
open MeasureTheory
def ObstacleCone (n : ℕ) : Set (Lp ℝ 2 (GaussMeasure n)) :=
  {v | Energy v ≠ ⊤ ∧ 0 ≤ᵐ[GaussMeasure n] (v : EuclideanSpace ℝ (Fin n) → ℝ)}
