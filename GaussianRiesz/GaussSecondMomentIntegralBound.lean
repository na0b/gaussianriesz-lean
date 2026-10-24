import GaussianRiesz.GaussEuclideanMomentBounds
open MeasureTheory
theorem GaussSecondMomentIntegralBound {n : ℕ} :
    ∀ b : ℝ, 0 < b →
      (∀ v : EuclideanSpace ℝ (Fin n),
          ‖v‖ ^ 2 * Real.exp (-b * ‖v‖ ^ 2) ≤ (2 / b) * Real.exp (-(b / 2) * ‖v‖ ^ 2))
        ∧ Integrable
            (fun w : EuclideanSpace ℝ (Fin n) => ‖w‖ ^ 2 * Real.exp (-b * ‖w‖ ^ 2)) volume
        ∧ ∫ w : EuclideanSpace ℝ (Fin n), ‖w‖ ^ 2 * Real.exp (-b * ‖w‖ ^ 2)
            ≤ (2 / b) * (Real.pi / (b / 2)) ^ ((n : ℝ) / 2) := by
  obtain ⟨gint, gval, -, -, -, -⟩ := GaussEuclideanMomentBounds (n := n)
  intro b hb
  have gmom : ∀ v : EuclideanSpace ℝ (Fin n),
      ‖v‖ ^ 2 * Real.exp (-b * ‖v‖ ^ 2) ≤ (2 / b) * Real.exp (-(b / 2) * ‖v‖ ^ 2) := by
    intro v
    have h1 : (b / 2) * ‖v‖ ^ 2 ≤ Real.exp ((b / 2) * ‖v‖ ^ 2) := by
      linarith [Real.add_one_le_exp ((b / 2) * ‖v‖ ^ 2)]
    have h2 : (0 : ℝ) < Real.exp (-((b / 2) * ‖v‖ ^ 2)) := Real.exp_pos _
    have h3 : ((b / 2) * ‖v‖ ^ 2) * Real.exp (-((b / 2) * ‖v‖ ^ 2)) ≤ 1 := by
      calc ((b / 2) * ‖v‖ ^ 2) * Real.exp (-((b / 2) * ‖v‖ ^ 2))
          ≤ Real.exp ((b / 2) * ‖v‖ ^ 2) * Real.exp (-((b / 2) * ‖v‖ ^ 2)) := by nlinarith
        _ = 1 := by rw [← Real.exp_add]; simp
    have h4 : ‖v‖ ^ 2 * Real.exp (-((b / 2) * ‖v‖ ^ 2)) ≤ 2 / b := by
      have hb2 : (0 : ℝ) < 2 / b := by positivity
      have h := mul_le_mul_of_nonneg_left h3 hb2.le
      rw [mul_one] at h
      calc ‖v‖ ^ 2 * Real.exp (-((b / 2) * ‖v‖ ^ 2))
          = (2 / b) * (((b / 2) * ‖v‖ ^ 2) * Real.exp (-((b / 2) * ‖v‖ ^ 2))) := by field_simp
        _ ≤ 2 / b := h
    have hsplit : Real.exp (-b * ‖v‖ ^ 2)
        = Real.exp (-((b / 2) * ‖v‖ ^ 2)) * Real.exp (-(b / 2) * ‖v‖ ^ 2) := by
      rw [← Real.exp_add]; ring_nf
    rw [hsplit]
    have hE : (0 : ℝ) < Real.exp (-(b / 2) * ‖v‖ ^ 2) := Real.exp_pos _
    nlinarith [h4, hE]
  refine ⟨gmom, ?_⟩
  have hb2 : (0 : ℝ) < b / 2 := by positivity
  have hmaj : Integrable (fun w : EuclideanSpace ℝ (Fin n) =>
      (2 / b) * Real.exp (-(b / 2) * ‖w‖ ^ 2)) volume := (gint (b / 2) hb2).const_mul _
  have hmeas : Continuous (fun w : EuclideanSpace ℝ (Fin n) =>
      ‖w‖ ^ 2 * Real.exp (-b * ‖w‖ ^ 2)) := by fun_prop
  have hint : Integrable (fun w : EuclideanSpace ℝ (Fin n) =>
      ‖w‖ ^ 2 * Real.exp (-b * ‖w‖ ^ 2)) volume := by
    refine Integrable.mono' hmaj hmeas.aestronglyMeasurable
      (Filter.Eventually.of_forall fun w => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact gmom w
  refine ⟨hint, ?_⟩
  calc ∫ w : EuclideanSpace ℝ (Fin n), ‖w‖ ^ 2 * Real.exp (-b * ‖w‖ ^ 2)
      ≤ ∫ w : EuclideanSpace ℝ (Fin n), (2 / b) * Real.exp (-(b / 2) * ‖w‖ ^ 2) :=
        integral_mono hint hmaj (fun w => gmom w)
    _ = (2 / b) * (Real.pi / (b / 2)) ^ ((n : ℝ) / 2) := by
        rw [integral_const_mul, gval (b / 2) hb2]
