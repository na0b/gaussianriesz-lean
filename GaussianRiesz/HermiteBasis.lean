module

public import GaussianRiesz.HermiteL2Orthonormal
public import GaussianRiesz.HermiteL2Complete

@[expose] public section
open MeasureTheory
noncomputable def HermiteBasis (n : ℕ) :
    HilbertBasis (Fin n → ℕ) ℝ (Lp ℝ 2 (GaussMeasure n)) :=
  HilbertBasis.mk (HermiteL2Orthonormal n) (HermiteL2Complete n)
