module

public import GaussianRiesz.HasGaussWeakGrad
public import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
public import Mathlib.Analysis.Calculus.BumpFunction.Normed

@[expose] public section
open MeasureTheory
open scoped ENNReal
theorem ConvolutionFDerivOfWeakGrad {n : ℕ} (ρ : EuclideanSpace ℝ (Fin n) → ℝ)
    (hρc : ContDiff ℝ (⊤ : ℕ∞) ρ) (hρcs : HasCompactSupport ρ)
    (v : EuclideanSpace ℝ (Fin n) → ℝ)
    (G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (hv : LocallyIntegrable v volume) (hwg : HasGaussWeakGrad v G)
    (j : Fin n) (x : EuclideanSpace ℝ (Fin n)) :
    fderiv ℝ (convolution ρ v (ContinuousLinearMap.lsmul ℝ ℝ) volume) x
        (EuclideanSpace.single j 1)
      = convolution ρ (fun y => G y j) (ContinuousLinearMap.lsmul ℝ ℝ) volume x := by
  have lsmulFlip : (ContinuousLinearMap.lsmul ℝ ℝ).flip
      = ContinuousLinearMap.lsmul ℝ ℝ := by
    ext
    simp
  set L : ℝ →L[ℝ] ℝ →L[ℝ] ℝ := ContinuousLinearMap.lsmul ℝ ℝ with hL
  have hρ1 : ContDiff ℝ 1 ρ := hρc.of_le (by exact_mod_cast le_top)
  have hdfc : Continuous (fderiv ℝ ρ) := hρc.continuous_fderiv (by simp)
  have hdfcs : HasCompactSupport (fderiv ℝ ρ) := hρcs.fderiv ℝ
  -- rewrite the left convolution as a right convolution
  have hswapρ : convolution ρ v L volume = convolution v ρ L volume := by
    rw [← convolution_flip L, lsmulFlip]
  -- Step A: the Fréchet derivative of the mollification
  have hfd : HasFDerivAt (convolution v ρ L volume)
      (convolution v (fderiv ℝ ρ)
        (ContinuousLinearMap.precompR (EuclideanSpace ℝ (Fin n)) L) volume x) x :=
    hρcs.hasFDerivAt_convolution_right L hv hρ1 x
  -- Step B: evaluate the derivative in the direction `e j`
  have hB : fderiv ℝ (convolution v ρ L volume) x (EuclideanSpace.single j 1)
      = convolution v (fun a => (fderiv ℝ ρ a) (EuclideanSpace.single j 1)) L volume x := by
    rw [hfd.fderiv]
    exact convolution_precompR_apply L hv hdfcs hdfc x (EuclideanSpace.single j 1)
  -- Step C: the weak-gradient identity with the reflected test function
  have hC : convolution (fun a => (fderiv ℝ ρ a) (EuclideanSpace.single j 1)) v L volume x
      = convolution ρ (fun y => G y j) L volume x := by
    set ψ : EuclideanSpace ℝ (Fin n) → ℝ := fun z => ρ (x - z) with hψdef
    have hψc : ContDiff ℝ (⊤ : ℕ∞) ψ := hρc.comp (contDiff_const.sub contDiff_id)
    have hψcs : HasCompactSupport ψ := hρcs.comp_homeomorph (Homeomorph.subLeft x)
    have hψd : ∀ y, fderiv ℝ ψ y (EuclideanSpace.single j 1)
        = -((fderiv ℝ ρ (x - y)) (EuclideanSpace.single j 1)) := by
      intro y
      have h1 : HasFDerivAt (fun z : EuclideanSpace ℝ (Fin n) => x - z)
          (-ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n))) y :=
        (hasFDerivAt_id y).const_sub x
      have h2 : HasFDerivAt ρ (fderiv ℝ ρ (x - y)) (x - y) :=
        (hρc.differentiable (by simp) (x - y)).hasFDerivAt
      have h4 : HasFDerivAt ψ
          ((fderiv ℝ ρ (x - y)).comp
            (-ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n)))) y := h2.comp y h1
      rw [h4.fderiv]
      simp
    have hid := hwg j ψ hψc hψcs
    -- unfold both convolutions by the swapped formula
    rw [convolution_eq_swap, convolution_eq_swap]
    simp only [ContinuousLinearMap.lsmul_apply, smul_eq_mul, hL]
    -- `hid` says `∫ v * (-(∂ⱼρ)(x-·)) = -∫ G·ⱼ * ρ(x-·)`
    have e1 : ∫ y, v y * fderiv ℝ ψ y (EuclideanSpace.single j 1)
        = -∫ y, (fderiv ℝ ρ (x - y)) (EuclideanSpace.single j 1) * v y := by
      rw [← integral_neg]
      refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
      show v y * fderiv ℝ ψ y (EuclideanSpace.single j 1)
          = -((fderiv ℝ ρ (x - y)) (EuclideanSpace.single j 1) * v y)
      rw [hψd y]
      ring
    have e2 : ∫ y, G y j * ψ y = ∫ y, ρ (x - y) * G y j := by
      refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
      show G y j * ψ y = ρ (x - y) * G y j
      rw [hψdef]
      ring
    rw [e1, e2] at hid
    linarith [hid]
  rw [hswapρ, hB, ← hC]
  rw [← convolution_flip L, lsmulFlip]
