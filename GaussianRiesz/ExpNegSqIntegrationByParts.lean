module

public import GaussianRiesz.Preamble
public import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts

@[expose] public section
open MeasureTheory
theorem ExpNegSqIntegrationByParts (g g' : ℝ → ℝ)
    (hg : ∀ σ : ℝ, HasDerivAt g (g' σ) σ)
    (i1 : Integrable (fun σ : ℝ => Real.exp (-σ ^ 2) * g' σ) volume)
    (i2 : Integrable (fun σ : ℝ => Real.exp (-σ ^ 2) * (σ * g σ)) volume)
    (i3 : Integrable (fun σ : ℝ => Real.exp (-σ ^ 2) * g σ) volume) :
    (∫ σ : ℝ, Real.exp (-σ ^ 2) * (σ * g σ))
      = (1 / 2) * ∫ σ : ℝ, Real.exp (-σ ^ 2) * g' σ := by
  have hGd : ∀ σ : ℝ, HasDerivAt (fun s : ℝ => -(1 / 2 : ℝ) * Real.exp (-s ^ 2))
      (σ * Real.exp (-σ ^ 2)) σ := by
    intro σ
    have hfe : (fun s : ℝ => -s ^ 2) = fun s : ℝ => (-1 : ℝ) * s ^ 2 := by
      funext s
      ring
    have h0 : HasDerivAt (fun s : ℝ => -s ^ 2) (-(2 * σ)) σ := by
      rw [hfe]
      refine ((hasDerivAt_pow 2 σ).const_mul (-1 : ℝ)).congr_deriv ?_
      push_cast
      ring
    refine ((h0.exp).const_mul (-(1 / 2 : ℝ))).congr_deriv ?_
    ring
  have hfd : ∀ σ : ℝ, fderiv ℝ g σ 1 = g' σ := fun σ => (hg σ).deriv
  have hGfd : ∀ σ : ℝ, fderiv ℝ (fun s : ℝ => -(1 / 2 : ℝ) * Real.exp (-s ^ 2)) σ 1
      = σ * Real.exp (-σ ^ 2) := fun σ => (hGd σ).deriv
  have j1 : Integrable (fun σ : ℝ => fderiv ℝ g σ 1
      * (-(1 / 2 : ℝ) * Real.exp (-σ ^ 2))) volume := by
    refine (i1.const_mul (-(1 / 2 : ℝ))).congr (Filter.Eventually.of_forall fun σ => ?_)
    show -(1 / 2 : ℝ) * (Real.exp (-σ ^ 2) * g' σ)
        = fderiv ℝ g σ 1 * (-(1 / 2 : ℝ) * Real.exp (-σ ^ 2))
    rw [hfd σ]
    ring
  have j2 : Integrable (fun σ : ℝ => g σ
      * fderiv ℝ (fun s : ℝ => -(1 / 2 : ℝ) * Real.exp (-s ^ 2)) σ 1) volume := by
    refine i2.congr (Filter.Eventually.of_forall fun σ => ?_)
    show Real.exp (-σ ^ 2) * (σ * g σ)
        = g σ * fderiv ℝ (fun s : ℝ => -(1 / 2 : ℝ) * Real.exp (-s ^ 2)) σ 1
    rw [hGfd σ]
    ring
  have j3 : Integrable (fun σ : ℝ => g σ * (-(1 / 2 : ℝ) * Real.exp (-σ ^ 2))) volume := by
    refine (i3.const_mul (-(1 / 2 : ℝ))).congr (Filter.Eventually.of_forall fun σ => ?_)
    show -(1 / 2 : ℝ) * (Real.exp (-σ ^ 2) * g σ)
        = g σ * (-(1 / 2 : ℝ) * Real.exp (-σ ^ 2))
    ring
  have hdiffg : ∀ σ : ℝ, DifferentiableAt ℝ g σ := fun σ => (hg σ).differentiableAt
  have hdiffG : ∀ σ : ℝ,
      DifferentiableAt ℝ (fun s : ℝ => -(1 / 2 : ℝ) * Real.exp (-s ^ 2)) σ :=
    fun σ => (hGd σ).differentiableAt
  have hibp := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    (μ := (volume : Measure ℝ)) (v := (1 : ℝ)) j1 j2 j3
    (fun x _ => hdiffg x) (fun x _ => hdiffG x)
  have e1 : (∫ σ : ℝ, Real.exp (-σ ^ 2) * (σ * g σ))
      = ∫ σ : ℝ, g σ * fderiv ℝ (fun s : ℝ => -(1 / 2 : ℝ) * Real.exp (-s ^ 2)) σ 1 := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun σ => ?_)
    show Real.exp (-σ ^ 2) * (σ * g σ)
        = g σ * fderiv ℝ (fun s : ℝ => -(1 / 2 : ℝ) * Real.exp (-s ^ 2)) σ 1
    rw [hGfd σ]
    ring
  have e2 : (∫ σ : ℝ, fderiv ℝ g σ 1 * (-(1 / 2 : ℝ) * Real.exp (-σ ^ 2)))
      = -((1 / 2) * ∫ σ : ℝ, Real.exp (-σ ^ 2) * g' σ) := by
    have h : (∫ σ : ℝ, fderiv ℝ g σ 1 * (-(1 / 2 : ℝ) * Real.exp (-σ ^ 2)))
        = ∫ σ : ℝ, (-(1 / 2 : ℝ)) * (Real.exp (-σ ^ 2) * g' σ) := by
      refine integral_congr_ae (Filter.Eventually.of_forall fun σ => ?_)
      show fderiv ℝ g σ 1 * (-(1 / 2 : ℝ) * Real.exp (-σ ^ 2))
          = (-(1 / 2 : ℝ)) * (Real.exp (-σ ^ 2) * g' σ)
      rw [hfd σ]
      ring
    rw [h, integral_const_mul]
    ring
  rw [e1, hibp, e2]
  ring
