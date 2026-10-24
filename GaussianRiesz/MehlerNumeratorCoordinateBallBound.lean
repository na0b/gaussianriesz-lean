import GaussianRiesz.Preamble
theorem MehlerNumeratorCoordinateBallBound {n : ℕ} (j : Fin n) (R : ℝ) :
    ∀ (x y : EuclideanSpace ℝ (Fin n)), ‖x‖ ≤ R → ∀ r : ℝ, 0 ≤ r → r ≤ 1 →
      |y j - r * x j| ≤ ‖y‖ + R := by
  intro x y hx r h0 h1
  have h2 : |y j| ≤ ‖y‖ := by simpa using PiLp.norm_apply_le y j
  have h3 : |x j| ≤ ‖x‖ := by simpa using PiLp.norm_apply_le x j
  have h4 : |y j - r * x j| ≤ |y j| + |r * x j| := by
    simpa [sub_eq_add_neg] using abs_add_le (y j) (-(r * x j))
  rw [abs_mul, abs_of_nonneg h0] at h4
  have h6 : r * |x j| ≤ 1 * |x j| := mul_le_mul_of_nonneg_right h1 (abs_nonneg _)
  rw [one_mul] at h6
  linarith
