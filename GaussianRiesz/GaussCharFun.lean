module

public import GaussianRiesz.GaussMeasure
public import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform

@[expose] public section
open MeasureTheory
theorem GaussCharFun {n : ℕ} (t : EuclideanSpace ℝ (Fin n)) :
    charFun (GaussMeasure n) t = Complex.exp (-(‖t‖ ^ 2) / 4) := by
  rw [charFun_apply]
  have hdm : Measurable (fun x : EuclideanSpace ℝ (Fin n) =>
      ENNReal.ofReal (Real.pi ^ (-(n : ℝ) / 2) * Real.exp (-‖x‖ ^ 2))) := by fun_prop
  have hfin : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
      ENNReal.ofReal (Real.pi ^ (-(n : ℝ) / 2) * Real.exp (-‖x‖ ^ 2)) < ⊤ :=
    Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top
  rw [GaussMeasure, integral_withDensity_eq_integral_toReal_smul hdm hfin]
  have hre : ∀ x : EuclideanSpace ℝ (Fin n),
      (ENNReal.ofReal (Real.pi ^ (-(n : ℝ) / 2) * Real.exp (-‖x‖ ^ 2))).toReal
          • Complex.exp ((inner ℝ x t : ℝ) * Complex.I)
        = (Real.pi ^ (-(n : ℝ) / 2) : ℝ)
            • Complex.exp (-(1 : ℂ) * (‖x‖ : ℂ) ^ 2
                + Complex.I * ((inner ℝ t x : ℝ) : ℂ)) := by
    intro x
    rw [ENNReal.toReal_ofReal (by positivity)]
    rw [show (Real.pi ^ (-(n : ℝ) / 2) * Real.exp (-‖x‖ ^ 2))
        = (Real.pi ^ (-(n : ℝ) / 2)) * Real.exp (-‖x‖ ^ 2) from rfl]
    rw [mul_smul]
    congr 1
    rw [Complex.real_smul, Complex.ofReal_exp, ← Complex.exp_add]
    congr 1
    rw [real_inner_comm x t]
    push_cast
    ring
  rw [integral_congr_ae (Filter.Eventually.of_forall hre), integral_smul]
  rw [GaussianFourier.integral_cexp_neg_mul_sq_norm_add (V := EuclideanSpace ℝ (Fin n))
      (b := (1 : ℂ)) (by norm_num) Complex.I t]
  rw [finrank_euclideanSpace_fin]
  rw [Complex.real_smul, Complex.ofReal_cpow Real.pi_pos.le, div_one, Complex.I_sq,
    show ((-(n:ℝ)/2 : ℝ) : ℂ) = -((n:ℂ)/2) from by push_cast; ring,
    ← mul_assoc, ← Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)]
  norm_num
