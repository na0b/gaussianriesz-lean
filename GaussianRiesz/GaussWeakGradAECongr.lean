module

public import GaussianRiesz.HasGaussWeakGrad
public import GaussianRiesz.GaussMeasure

@[expose] public section
open MeasureTheory
theorem GaussWeakGradAECongr {n : ℕ}
    (v v' : EuclideanSpace ℝ (Fin n) → ℝ)
    (F F' : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (hv : v =ᵐ[GaussMeasure n] v') (hF : F =ᵐ[GaussMeasure n] F')
    (h : HasGaussWeakGrad v F) :
    HasGaussWeakGrad v' F' := by
  -- the Gaussian density is measurable and strictly positive, so `γₙ`-a.e. statements
  -- are Lebesgue-a.e. statements
  have hdens : Measurable (fun x : EuclideanSpace ℝ (Fin n) =>
      ENNReal.ofReal (Real.pi ^ (-(n : ℝ) / 2) * Real.exp (-‖x‖ ^ 2))) := by fun_prop
  have hae : ∀ p : EuclideanSpace ℝ (Fin n) → Prop,
      (∀ᵐ x ∂(GaussMeasure n), p x) →
      ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))), p x := by
    intro p hp
    rw [GaussMeasure, ae_withDensity_iff hdens] at hp
    filter_upwards [hp] with x hx
    refine hx ?_
    simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]
    positivity
  have hvv := hae (fun x => v x = v' x) hv
  have hFF := hae (fun x => F x = F' x) hF
  intro j φ hφ hφc
  have l1 : ∫ x, v' x * fderiv ℝ φ x (EuclideanSpace.single j 1)
      = ∫ x, v x * fderiv ℝ φ x (EuclideanSpace.single j 1) :=
    integral_congr_ae (by filter_upwards [hvv] with x hx; rw [hx])
  have l2 : ∫ x, F' x j * φ x = ∫ x, F x j * φ x :=
    integral_congr_ae (by filter_upwards [hFF] with x hx; rw [hx])
  rw [l1, l2]
  exact h j φ hφ hφc
