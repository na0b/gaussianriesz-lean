import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import GaussianRiesz.Preamble
open MeasureTheory
theorem GaussEuclideanMomentBounds {n : ℕ} :
    (∀ b : ℝ, 0 < b →
        Integrable (fun w : EuclideanSpace ℝ (Fin n) => Real.exp (-b * ‖w‖ ^ 2)) volume)
  ∧ (∀ b : ℝ, 0 < b →
        ∫ w : EuclideanSpace ℝ (Fin n), Real.exp (-b * ‖w‖ ^ 2)
      = (Real.pi / b) ^ ((n : ℝ) / 2))
  ∧ (∀ (w : EuclideanSpace ℝ (Fin n)) (j : Fin n), |w j| ≤ ‖w‖)
  ∧ (∀ b : ℝ, 0 < b → ∀ v : EuclideanSpace ℝ (Fin n),
        ‖v‖ * Real.exp (-b * ‖v‖ ^ 2) ≤ (1 + 2 / b) * Real.exp (-(b / 2) * ‖v‖ ^ 2))
  ∧ (∀ b : ℝ, 0 < b →
        Integrable (fun w : EuclideanSpace ℝ (Fin n) => ‖w‖ * Real.exp (-b * ‖w‖ ^ 2)) volume
      ∧ ∫ w : EuclideanSpace ℝ (Fin n), ‖w‖ * Real.exp (-b * ‖w‖ ^ 2)
      ≤ (1 + 2 / b) * (Real.pi / (b / 2)) ^ ((n : ℝ) / 2))
  ∧ (∀ σ b' : ℝ, 0 < σ → 0 < b' →
        Real.pi ^ (-(n : ℝ) / 2) * σ ^ (-(n : ℝ) / 2) * (Real.pi / b') ^ ((n : ℝ) / 2)
      = (1 / (σ * b')) ^ ((n : ℝ) / 2)) := by
  have gint : ∀ (b : ℝ) (hb : 0 < b),
        Integrable (fun w : EuclideanSpace ℝ (Fin n) => Real.exp (-b * ‖w‖ ^ 2)) volume := by
    intro b hb
    have h := (GaussianFourier.integrable_cexp_neg_mul_sq_norm_add
        (V := EuclideanSpace ℝ (Fin n)) (b := ((b : ℝ) : ℂ)) (by simpa using hb) 0
        (0 : EuclideanSpace ℝ (Fin n))).re
    refine h.congr ?_
    filter_upwards with v
    simp only [zero_mul, add_zero, neg_mul]
    simp [← Complex.ofReal_pow, Complex.exp_re]
  have gval : ∀ (b : ℝ) (hb : 0 < b),
        ∫ w : EuclideanSpace ℝ (Fin n), Real.exp (-b * ‖w‖ ^ 2)
    = (Real.pi / b) ^ ((n : ℝ) / 2) := by
    intro b hb
    rw [GaussianFourier.integral_rexp_neg_mul_sq_norm hb, finrank_euclideanSpace_fin]
  have coordle : ∀ (w : EuclideanSpace ℝ (Fin n)) (j : Fin n),
        |w j| ≤ ‖w‖ := fun w j => by simpa using PiLp.norm_apply_le w j

  have fmom : ∀ (b : ℝ) (hb : 0 < b) (v : EuclideanSpace ℝ (Fin n)),
        ‖v‖ * Real.exp (-b * ‖v‖ ^ 2) ≤ (1 + 2 / b) * Real.exp (-(b / 2) * ‖v‖ ^ 2) := by
    intro b hb v
    set t : ℝ := ‖v‖ with ht
    set E : ℝ := Real.exp (-(b / 2) * t ^ 2) with hE
    have hE0 : 0 < E := Real.exp_pos _
    have hE1 : E ≤ 1 := by
      rw [hE, Real.exp_le_one_iff]
      have : (0 : ℝ) ≤ (b / 2) * t ^ 2 := by positivity
      linarith
    have hEE : Real.exp (-b * t ^ 2) = E * E := by rw [hE, ← Real.exp_add]; ring_nf
    have hu : ((b / 2) * t ^ 2) * E ≤ 1 := by
      have h1 : (b / 2) * t ^ 2 ≤ Real.exp ((b / 2) * t ^ 2) := by
        linarith [Real.add_one_le_exp ((b / 2) * t ^ 2)]
      have h3 : Real.exp ((b / 2) * t ^ 2) * E = 1 := by
        rw [hE, ← Real.exp_add]; ring_nf; exact Real.exp_zero
      nlinarith [hE0]
    have hmom : t ^ 2 * E ≤ 2 / b := by
      have hb2 : (0 : ℝ) < 2 / b := by positivity
      have h := mul_le_mul_of_nonneg_left hu hb2.le
      rw [mul_one] at h
      calc t ^ 2 * E = (2 / b) * (((b / 2) * t ^ 2) * E) := by field_simp
        _ ≤ 2 / b := h
    calc t * Real.exp (-b * t ^ 2) = t * (E * E) := by rw [hEE]
      _ ≤ (1 + t ^ 2) * (E * E) := by nlinarith [sq_nonneg (t - 1), mul_pos hE0 hE0]
      _ = E * E + (t ^ 2 * E) * E := by ring
      _ ≤ 1 * E + (2 / b) * E := by nlinarith
      _ = (1 + 2 / b) * E := by ring

  -- the first-moment Gaussian integral, as an integrability-plus-bound pair
  have gfirst : ∀ (b : ℝ) (hb : 0 < b),
        Integrable (fun w : EuclideanSpace ℝ (Fin n) => ‖w‖ * Real.exp (-b * ‖w‖ ^ 2)) volume
    ∧ ∫ w : EuclideanSpace ℝ (Fin n), ‖w‖ * Real.exp (-b * ‖w‖ ^ 2)
    ≤ (1 + 2 / b) * (Real.pi / (b / 2)) ^ ((n : ℝ) / 2) := by
    intro b hb
    have hb2 : (0 : ℝ) < b / 2 := by positivity
    have hmaj : Integrable (fun w : EuclideanSpace ℝ (Fin n) =>
        (1 + 2 / b) * Real.exp (-(b / 2) * ‖w‖ ^ 2)) volume := (gint (b / 2) hb2).const_mul _
    have hcont : Continuous (fun w : EuclideanSpace ℝ (Fin n) =>
        ‖w‖ * Real.exp (-b * ‖w‖ ^ 2)) := by fun_prop
    have hint : Integrable (fun w : EuclideanSpace ℝ (Fin n) =>
        ‖w‖ * Real.exp (-b * ‖w‖ ^ 2)) volume := by
      refine Integrable.mono' hmaj hcont.aestronglyMeasurable
        (Filter.Eventually.of_forall fun w => ?_)
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      exact fmom b hb w
    refine ⟨hint, ?_⟩
    calc ∫ w : EuclideanSpace ℝ (Fin n), ‖w‖ * Real.exp (-b * ‖w‖ ^ 2)
        ≤ ∫ w : EuclideanSpace ℝ (Fin n), (1 + 2 / b) * Real.exp (-(b / 2) * ‖w‖ ^ 2) :=
          integral_mono hint hmaj (fun w => fmom b hb w)
      _ = (1 + 2 / b) * (Real.pi / (b / 2)) ^ ((n : ℝ) / 2) := by
          rw [integral_const_mul, gval (b / 2) hb2]
  have canon : ∀ (σ b' : ℝ) (hσ : 0 < σ) (hb : 0 < b'),
        Real.pi ^ (-(n : ℝ) / 2) * σ ^ (-(n : ℝ) / 2) * (Real.pi / b') ^ ((n : ℝ) / 2)
    = (1 / (σ * b')) ^ ((n : ℝ) / 2) := by
    intro σ b' hσ hb
    have ha : (-(n : ℝ) / 2) = -((n : ℝ) / 2) := by ring
    rw [ha, Real.rpow_neg Real.pi_pos.le, Real.rpow_neg hσ.le,
      Real.div_rpow Real.pi_pos.le hb.le, one_div,
      Real.inv_rpow (by positivity : (0:ℝ) ≤ σ * b'), Real.mul_rpow hσ.le hb.le]
    field_simp
  exact ⟨gint, gval, coordle, fmom, gfirst, canon⟩
