module

public import GaussianRiesz.PseudoInverseSqrt
public import GaussianRiesz.SqrtDomainSobolev

@[expose] public section
open MeasureTheory
noncomputable def RieszTransform {n : ℕ} (f : Lp ℝ 2 (GaussMeasure n)) :
    Lp (EuclideanSpace ℝ (Fin n)) 2 (GaussMeasure n) :=
  GaussD (FracPow (-(1 : ℝ) / 2) f)
