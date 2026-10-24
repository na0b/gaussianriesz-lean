import GaussianRiesz.Preamble
theorem ExpDecayPowerBoundAndRpowAbsorption {n : ℕ} :
    (∀ t : ℝ, 0 < t →
        Real.exp (-t) ≤ ((n : ℝ) + 2) ^ (n + 2) * (t⁻¹) ^ (n + 2))
      ∧ (∀ r c : ℝ, 1/2 ≤ r → r < 1 → 0 < c →
          (1 - r) ^ (-((n : ℝ) / 2 + 3/2))
              * (((n : ℝ) + 2) ^ (n + 2) * (c * (1 - r)) ^ (n + 2))
            ≤ ((n : ℝ) + 2) ^ (n + 2) * c ^ (n + 2)) := by
  refine ⟨?_, ?_⟩
  ·
    intro t ht
    have hk : ((n : ℝ) + 2) = ((n + 2 : ℕ) : ℝ) := by push_cast; ring
    have hk0 : (0:ℝ) < (n : ℝ) + 2 := by positivity
    have h1 : t / ((n : ℝ) + 2) ≤ Real.exp (t / ((n : ℝ) + 2)) := by
      linarith [Real.add_one_le_exp (t / ((n : ℝ) + 2))]
    have h2 : (t / ((n : ℝ) + 2)) ^ (n + 2) ≤ Real.exp (t / ((n : ℝ) + 2)) ^ (n + 2) :=
      pow_le_pow_left₀ (by positivity) h1 (n + 2)
    have h3 : Real.exp (t / ((n : ℝ) + 2)) ^ (n + 2) = Real.exp t := by
      rw [← Real.exp_nat_mul]
      congr 1
      rw [hk]
      field_simp
    rw [h3, div_pow, div_le_iff₀ (by positivity)] at h2
    rw [inv_pow, ← div_eq_mul_inv, Real.exp_neg, inv_eq_one_div,
      div_le_div_iff₀ (Real.exp_pos t) (by positivity : (0:ℝ) < t ^ (n + 2))]
    linarith
  ·
    intro r c h1 h2 hc
    have hτ0 : (0:ℝ) < 1 - r := by linarith
    have hτ1 : 1 - r ≤ 1 := by linarith
    have e1 : ((1:ℝ) - r) ^ (n + 2) = (1 - r) ^ (((n + 2 : ℕ) : ℝ)) :=
      (Real.rpow_natCast (1 - r) (n + 2)).symm
    have e3 : (0:ℝ) ≤ -((n : ℝ) / 2 + 3/2) + ((n + 2 : ℕ) : ℝ) := by push_cast; linarith
    have e4 : (1 - r) ^ (-((n : ℝ) / 2 + 3/2) + ((n + 2 : ℕ) : ℝ)) ≤ 1 :=
      Real.rpow_le_one hτ0.le hτ1 e3
    calc (1 - r) ^ (-((n : ℝ) / 2 + 3/2))
            * (((n : ℝ) + 2) ^ (n + 2) * (c * (1 - r)) ^ (n + 2))
        = (((n : ℝ) + 2) ^ (n + 2) * c ^ (n + 2))
            * ((1 - r) ^ (-((n : ℝ) / 2 + 3/2)) * (1 - r) ^ (n + 2)) := by
          rw [mul_pow]; ring
      _ = (((n : ℝ) + 2) ^ (n + 2) * c ^ (n + 2))
            * (1 - r) ^ (-((n : ℝ) / 2 + 3/2) + ((n + 2 : ℕ) : ℝ)) := by
          rw [e1, ← Real.rpow_add hτ0]
      _ ≤ (((n : ℝ) + 2) ^ (n + 2) * c ^ (n + 2)) * 1 :=
          mul_le_mul_of_nonneg_left e4
            (mul_nonneg (pow_nonneg (by positivity) _) (pow_nonneg hc.le _))
      _ = ((n : ℝ) + 2) ^ (n + 2) * c ^ (n + 2) := by ring
