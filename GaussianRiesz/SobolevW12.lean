module

public import GaussianRiesz.HasGaussWeakGrad
public import GaussianRiesz.GaussMeasure

@[expose] public section
open MeasureTheory
def SobolevW12 (n : ℕ) : Set (Lp ℝ 2 (GaussMeasure n)) :=
  {v | ∃ G : Lp (EuclideanSpace ℝ (Fin n)) 2 (GaussMeasure n),
    HasGaussWeakGrad (v : EuclideanSpace ℝ (Fin n) → ℝ)
      (fun x => Real.sqrt 2 •
        (G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) x)}
