import GaussianRiesz.RieszTransform
import GaussianRiesz.FracPowLinear
import GaussianRiesz.GaussDLinear
import GaussianRiesz.SqrtDomainSobolev
import GaussianRiesz.PseudoInverseSqrt
open MeasureTheory
theorem RieszTransformLinear {n : ℕ} :
    (∀ v w : Lp ℝ 2 (GaussMeasure n),
        RieszTransform (v + w) = RieszTransform v + RieszTransform w)
      ∧ (∀ (c : ℝ) (v : Lp ℝ 2 (GaussMeasure n)),
        RieszTransform (c • v) = c • RieszTransform v) := by
  -- `L^{-1/2}` is everywhere defined on `L²`, and both it and `D` are linear
  obtain ⟨hall, hFPadd, hFPsmul⟩ := FracPowLinear (-(1 : ℝ) / 2) (n := n)
  have hdomall : ∀ v : Lp ℝ 2 (GaussMeasure n), v ∈ FracPowDomain (-(1 : ℝ) / 2) :=
    hall (by norm_num)
  obtain ⟨hGDadd, hGDsmul, -⟩ := GaussDLinear (n := n)
  have hsob : ∀ v : Lp ℝ 2 (GaussMeasure n),
      FracPow (-(1 : ℝ) / 2) v ∈ SobolevW12 n := fun v =>
    (SqrtDomainSobolev _ (PseudoInverseSqrt v).1).1
  refine ⟨fun v w => ?_, fun c v => ?_⟩
  · rw [RieszTransform, RieszTransform, RieszTransform,
      (hFPadd v w (hdomall v) (hdomall w)).2, (hGDadd _ _ (hsob v) (hsob w)).2]
  · rw [RieszTransform, RieszTransform, (hFPsmul c v (hdomall v)).2,
      (hGDsmul c _ (hsob v)).2]
