import GaussianRiesz.Preamble
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
open MeasureTheory
theorem CompIntegrationByParts {n : ℕ} (q q' : ℝ → ℝ)
    (hq : ∀ t, HasDerivAt q (q' t) t) (hq'c : Continuous q')
    (w : EuclideanSpace ℝ (Fin n) → ℝ) (j : Fin n)
    (hwd : Differentiable ℝ w)
    (hwc : Continuous (fun x => fderiv ℝ w x (EuclideanSpace.single j (1 : ℝ))))
    (φ : EuclideanSpace ℝ (Fin n) → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφcs : HasCompactSupport φ) :
    ∫ x, q (w x) * fderiv ℝ φ x (EuclideanSpace.single j 1)
      = -∫ x, (q' (w x) * fderiv ℝ w x (EuclideanSpace.single j 1)) * φ x := by
  have hqc : Continuous q :=
    continuous_iff_continuousAt.2 fun t => (hq t).continuousAt
  have hwhd : ∀ x, HasFDerivAt w (fderiv ℝ w x) x :=
    fun x => (hwd x).hasFDerivAt
  have hfd : ∀ x, HasFDerivAt (fun y => q (w y)) (q' (w x) • fderiv ℝ w x) x :=
    fun x => (hq (w x)).comp_hasFDerivAt x (hwhd x)
  have hfderiv : ∀ x, fderiv ℝ (fun y => q (w y)) x (EuclideanSpace.single j 1)
      = q' (w x) * fderiv ℝ w x (EuclideanSpace.single j 1) := by
    intro x
    rw [(hfd x).fderiv]
    simp
  have hcw : Continuous w := hwd.continuous
  have hcf : Continuous (fun y => q (w y)) := hqc.comp hcw
  have hcdw : Continuous (fun x => fderiv ℝ w x (EuclideanSpace.single j 1)) := hwc
  have hcdφ : Continuous (fun x => fderiv ℝ φ x (EuclideanSpace.single j 1)) :=
    (hφ.continuous_fderiv (by simp)).clm_apply continuous_const
  have hcdf : Continuous (fun x => fderiv ℝ (fun y => q (w y)) x (EuclideanSpace.single j 1)) := by
    rw [show (fun x => fderiv ℝ (fun y => q (w y)) x (EuclideanSpace.single j 1))
        = fun x => q' (w x) * fderiv ℝ w x (EuclideanSpace.single j 1) from funext hfderiv]
    exact (hq'c.comp hcw).mul hcdw
  have hcsdφ : HasCompactSupport (fun x => fderiv ℝ φ x (EuclideanSpace.single j 1)) :=
    hφcs.fderiv_apply ℝ _
  have i1 : Integrable
      (fun x => fderiv ℝ (fun y => q (w y)) x (EuclideanSpace.single j 1) * φ x)
      (volume : Measure (EuclideanSpace ℝ (Fin n))) :=
    (hcdf.mul hφ.continuous).integrable_of_hasCompactSupport hφcs.mul_left
  have i2 : Integrable
      (fun x => (fun y => q (w y)) x * fderiv ℝ φ x (EuclideanSpace.single j 1))
      (volume : Measure (EuclideanSpace ℝ (Fin n))) :=
    (hcf.mul hcdφ).integrable_of_hasCompactSupport hcsdφ.mul_left
  have i3 : Integrable (fun x => (fun y => q (w y)) x * φ x)
      (volume : Measure (EuclideanSpace ℝ (Fin n))) :=
    (hcf.mul hφ.continuous).integrable_of_hasCompactSupport hφcs.mul_left
  have hibp := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    (μ := (volume : Measure (EuclideanSpace ℝ (Fin n)))) i1 i2 i3
    (fun x _ => (hfd x).differentiableAt)
    (fun x _ => (hφ.differentiable (by simp) x))
  rw [hibp]
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  show fderiv ℝ (fun y => q (w y)) x (EuclideanSpace.single j 1) * φ x
      = (q' (w x) * fderiv ℝ w x (EuclideanSpace.single j 1)) * φ x
  rw [hfderiv x]
