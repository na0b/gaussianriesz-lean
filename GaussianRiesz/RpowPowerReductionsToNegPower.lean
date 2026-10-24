import GaussianRiesz.Preamble
theorem RpowPowerReductionsToNegPower {n : ℕ} :
    (1:ℝ) ≤ (n:ℝ) → ∀ M : ℝ, 3 ≤ M → ∀ d : ℝ, 0 < d → d ≤ 2 →
      ((9/128 * d ^ 2) ^ (1 - ((n:ℝ)/2 + 3/2))
          = (9/128 : ℝ) ^ (1 - ((n:ℝ)/2 + 3/2)) * d ^ (-((n:ℝ) + 1)))
        ∧ (8 * d ^ 2 * (9/128 * d ^ 2) ^ (1 - ((n:ℝ)/2 + 5/2))
          = 8 * (9/128 : ℝ) ^ (-((n:ℝ)/2 + 3/2)) * d ^ (-((n:ℝ) + 1)))
        ∧ ((d / (8 * M / 3)) ^ (-((n:ℝ)/2 + 3/2))
          ≤ (8 * M / 3) ^ ((n:ℝ)/2 + 3/2) * 2 ^ (-((n:ℝ)/2 + 3/2) + ((n:ℝ) + 1))
            * d ^ (-((n:ℝ) + 1)))
        ∧ (8 * d ^ 2 * (d / (8 * M / 3)) ^ (-((n:ℝ)/2 + 5/2))
          ≤ 8 * (8 * M / 3) ^ ((n:ℝ)/2 + 5/2)
              * 2 ^ (1 - ((n:ℝ)/2 + 3/2) + ((n:ℝ) + 1)) * d ^ (-((n:ℝ) + 1)))
        ∧ (4 * M ^ 2 * (d / (8 * M / 3)) ^ (-((n:ℝ)/2 + 1/2))
          ≤ 4 * M ^ 2 * (8 * M / 3) ^ ((n:ℝ)/2 + 1/2)
              * 2 ^ (1 - ((n:ℝ)/2 + 3/2) + ((n:ℝ) + 1)) * d ^ (-((n:ℝ) + 1))) := by
  intro hn1 M hM d hd0 hd2
  have hdpow : ∀ β γ : ℝ, 0 ≤ β + γ → ∀ d : ℝ, 0 < d → d ≤ 2 →
      d ^ β ≤ 2 ^ (β + γ) * d ^ (-γ) := by
    intro β γ hbg d hd0 hd2
    have h1 : d ^ β = d ^ (β + γ) * d ^ (-γ) := by
      rw [← Real.rpow_add hd0]; ring_nf
    have h2 : d ^ (β + γ) ≤ 2 ^ (β + γ) := Real.rpow_le_rpow hd0.le hd2 hbg
    rw [h1]
    exact mul_le_mul_of_nonneg_right h2 (Real.rpow_pos_of_pos hd0 _).le
  have hmulrpow : ∀ κ s : ℝ, 0 < κ →
      (κ * d ^ 2) ^ (-s) = κ ^ (-s) * d ^ (-(2 * s)) := by
    intro κ s hκ
    rw [Real.mul_rpow hκ.le (by positivity)]
    congr 1
    rw [← Real.rpow_natCast d 2, ← Real.rpow_mul (hd0.le)]
    push_cast
    ring_nf
  have hdivrpow : ∀ u s : ℝ, 0 < u →
      (d / u) ^ (-s) = d ^ (-s) * u ^ s := by
    intro u s hu
    rw [Real.div_rpow (hd0.le) hu.le, Real.rpow_neg hu.le s, div_eq_mul_inv, inv_inv]
  have hmul2 : ∀ β : ℝ, d ^ 2 * d ^ β = d ^ (β + 2) := by
    intro β
    rw [← Real.rpow_natCast d 2, ← Real.rpow_add hd0]
    congr 1
    push_cast
    ring
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  ·
    rw [show (1:ℝ) - ((n:ℝ)/2 + 3/2) = -((n:ℝ)/2 + 1/2) from by ring,
      hmulrpow (9/128) ((n:ℝ)/2 + 1/2) (by norm_num),
      show (2:ℝ) * ((n:ℝ)/2 + 1/2) = (n:ℝ) + 1 from by ring,
      show -((n:ℝ)/2 + 1/2) = 1 - ((n:ℝ)/2 + 3/2) from by ring]
  ·
    rw [show (1:ℝ) - ((n:ℝ)/2 + 5/2) = -((n:ℝ)/2 + 3/2) from by ring,
      hmulrpow (9/128) ((n:ℝ)/2 + 3/2) (by norm_num),
      show (2:ℝ) * ((n:ℝ)/2 + 3/2) = (n:ℝ) + 3 from by ring]
    have h := hmul2 (-((n:ℝ) + 3))
    rw [show -((n:ℝ) + 3) + 2 = -((n:ℝ) + 1) from by ring] at h
    calc 8 * d ^ 2
            * ((9/128 : ℝ) ^ (-((n:ℝ)/2 + 3/2)) * d ^ (-((n:ℝ) + 3)))
        = 8 * (9/128 : ℝ) ^ (-((n:ℝ)/2 + 3/2))
            * (d ^ 2 * d ^ (-((n:ℝ) + 3))) := by ring
      _ = 8 * (9/128 : ℝ) ^ (-((n:ℝ)/2 + 3/2)) * d ^ (-((n:ℝ) + 1)) := by rw [h]
  ·
    rw [hdivrpow (8 * M / 3) ((n:ℝ)/2 + 3/2) (by positivity)]
    have h := hdpow (-((n:ℝ)/2 + 3/2)) ((n:ℝ) + 1) (by linarith) d hd0 hd2
    have hc : (0:ℝ) ≤ (8 * M / 3) ^ ((n:ℝ)/2 + 3/2) := by positivity
    calc d ^ (-((n:ℝ)/2 + 3/2)) * (8 * M / 3) ^ ((n:ℝ)/2 + 3/2)
        = (8 * M / 3) ^ ((n:ℝ)/2 + 3/2) * d ^ (-((n:ℝ)/2 + 3/2)) := by ring
      _ ≤ (8 * M / 3) ^ ((n:ℝ)/2 + 3/2)
            * (2 ^ (-((n:ℝ)/2 + 3/2) + ((n:ℝ) + 1)) * d ^ (-((n:ℝ) + 1))) :=
          mul_le_mul_of_nonneg_left h hc
      _ = (8 * M / 3) ^ ((n:ℝ)/2 + 3/2) * 2 ^ (-((n:ℝ)/2 + 3/2) + ((n:ℝ) + 1))
            * d ^ (-((n:ℝ) + 1)) := by ring
  ·
    rw [hdivrpow (8 * M / 3) ((n:ℝ)/2 + 5/2) (by positivity)]
    have h := hdpow (1 - ((n:ℝ)/2 + 3/2)) ((n:ℝ) + 1) (by linarith) d hd0 hd2
    have hm := hmul2 (-((n:ℝ)/2 + 5/2))
    rw [show -((n:ℝ)/2 + 5/2) + 2 = 1 - ((n:ℝ)/2 + 3/2) from by ring] at hm
    have hc : (0:ℝ) ≤ 8 * (8 * M / 3) ^ ((n:ℝ)/2 + 5/2) := by positivity
    calc 8 * d ^ 2
            * (d ^ (-((n:ℝ)/2 + 5/2)) * (8 * M / 3) ^ ((n:ℝ)/2 + 5/2))
        = 8 * (8 * M / 3) ^ ((n:ℝ)/2 + 5/2)
            * (d ^ 2 * d ^ (-((n:ℝ)/2 + 5/2))) := by ring
      _ = 8 * (8 * M / 3) ^ ((n:ℝ)/2 + 5/2) * d ^ (1 - ((n:ℝ)/2 + 3/2)) := by rw [hm]
      _ ≤ 8 * (8 * M / 3) ^ ((n:ℝ)/2 + 5/2)
            * (2 ^ (1 - ((n:ℝ)/2 + 3/2) + ((n:ℝ) + 1)) * d ^ (-((n:ℝ) + 1))) :=
          mul_le_mul_of_nonneg_left h hc
      _ = 8 * (8 * M / 3) ^ ((n:ℝ)/2 + 5/2)
            * 2 ^ (1 - ((n:ℝ)/2 + 3/2) + ((n:ℝ) + 1)) * d ^ (-((n:ℝ) + 1)) := by ring
  ·
    rw [hdivrpow (8 * M / 3) ((n:ℝ)/2 + 1/2) (by positivity)]
    have h := hdpow (1 - ((n:ℝ)/2 + 3/2)) ((n:ℝ) + 1) (by linarith) d hd0 hd2
    rw [show (1:ℝ) - ((n:ℝ)/2 + 3/2) = -((n:ℝ)/2 + 1/2) from by ring] at h
    have hc : (0:ℝ) ≤ 4 * M ^ 2 * (8 * M / 3) ^ ((n:ℝ)/2 + 1/2) := by positivity
    calc 4 * M ^ 2 * (d ^ (-((n:ℝ)/2 + 1/2)) * (8 * M / 3) ^ ((n:ℝ)/2 + 1/2))
        = 4 * M ^ 2 * (8 * M / 3) ^ ((n:ℝ)/2 + 1/2) * d ^ (-((n:ℝ)/2 + 1/2)) := by ring
      _ ≤ 4 * M ^ 2 * (8 * M / 3) ^ ((n:ℝ)/2 + 1/2)
            * (2 ^ (-((n:ℝ)/2 + 1/2) + ((n:ℝ) + 1)) * d ^ (-((n:ℝ) + 1))) :=
          mul_le_mul_of_nonneg_left h hc
      _ = 4 * M ^ 2 * (8 * M / 3) ^ ((n:ℝ)/2 + 1/2)
            * 2 ^ (1 - ((n:ℝ)/2 + 3/2) + ((n:ℝ) + 1)) * d ^ (-((n:ℝ) + 1)) := by
          rw [show (1:ℝ) - ((n:ℝ)/2 + 3/2) + ((n:ℝ) + 1)
            = -((n:ℝ)/2 + 1/2) + ((n:ℝ) + 1) from by ring]
          ring
