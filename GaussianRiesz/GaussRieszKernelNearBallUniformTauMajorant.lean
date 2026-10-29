module

public import GaussianRiesz.Preamble

@[expose] public section
open MeasureTheory Filter Topology
theorem GaussRieszKernelNearBallUniformTauMajorant {n : ℕ} :
    ∀ M : ℝ, 3 ≤ M → ∀ x y : EuclideanSpace ℝ (Fin n), ‖y‖ ≤ M → 0 < ‖x - y‖ →
      ∀ G : EuclideanSpace ℝ (Fin n) → ℝ → EuclideanSpace ℝ (Fin n),
        (∀ w : EuclideanSpace ℝ (Fin n), ‖w‖ ≤ M → ∀ r : ℝ, 0 < r → r < 1 →
            ‖G w r‖ ≤ Real.exp (M ^ 2) * (1 - r) ^ (-(n : ℝ) / 2 - 3 / 2)
                * (1 + 2 * (‖w - y‖ + (1 - r) * M) ^ 2 / (1 - r))
                * Real.exp (-‖w - r • y‖ ^ 2 / (2 * (1 - r)))) →
          (∀ w ∈ Metric.ball x (‖x - y‖ / 4), ‖w‖ ≤ M ∧ 3 * ‖x - y‖ / 4 ≤ ‖w - y‖
              ∧ ‖w - y‖ ≤ 5 * ‖x - y‖ / 4) →
            ∀ w ∈ Metric.ball x (‖x - y‖ / 4), ∀ τ : ℝ, 0 < τ → τ < 1 →
      ‖G w (1 - τ)‖
        ≤ (Real.exp (M ^ 2) * (τ ^ (-((n:ℝ)/2 + 3/2))
              * Real.exp (-(9/128 * ‖x - y‖ ^ 2) / τ))
            + Real.exp (M ^ 2) * (8 * ‖x - y‖ ^ 2) * (τ ^ (-((n:ℝ)/2 + 5/2))
              * Real.exp (-(9/128 * ‖x - y‖ ^ 2) / τ)))
          + Real.exp (M ^ 2)
            * ((‖x - y‖ / (8 * M / 3)) ^ (-((n:ℝ)/2 + 3/2))
              + 8 * ‖x - y‖ ^ 2 * (‖x - y‖ / (8 * M / 3)) ^ (-((n:ℝ)/2 + 5/2))
              + 4 * M ^ 2 * (‖x - y‖ / (8 * M / 3)) ^ (-((n:ℝ)/2 + 1/2))) := by
  intro M hM x y hyM hd0 G hGbnd hUmem
  have hnR0 : (0:ℝ) ≤ (n:ℝ) := Nat.cast_nonneg n
  have hanti : ∀ u v s : ℝ, 0 < u → u ≤ v → 0 ≤ s → v ^ (-s) ≤ u ^ (-s) := by
    intro u v s hu huv hs
    rw [Real.rpow_neg hu.le, Real.rpow_neg (by linarith)]
    exact inv_anti₀ (Real.rpow_pos_of_pos hu _) (Real.rpow_le_rpow hu.le huv hs)
  have hsqsum : ∀ p q : ℝ, (p + q) ^ 2 ≤ 2 * p ^ 2 + 2 * q ^ 2 := by
    intro p q; nlinarith [sq_nonneg (p - q)]
  have hdivmono : ∀ A B t : ℝ, 0 < t → B ≤ A → -A / t ≤ -B / t := by
    intro A B t ht h
    rw [div_le_div_iff_of_pos_right ht]; linarith
  have hsepw : ∀ (w : EuclideanSpace ℝ (Fin n)) (τ : ℝ), 0 < τ →
      ‖w - y‖ - τ * M ≤ ‖w - (1 - τ) • y‖ := by
    intro w τ hτ0
    have e1 : w - (1 - τ) • y = (w - y) - (-(τ • y)) := by
      rw [sub_smul, one_smul]; abel
    have e2 : ‖-(τ • y)‖ ≤ τ * M := by
      rw [norm_neg, norm_smul, Real.norm_eq_abs, abs_of_pos hτ0]
      exact mul_le_mul_of_nonneg_left hyM hτ0.le
    have h := norm_sub_norm_le (w - y) (-(τ • y))
    rw [← e1] at h
    linarith
  have hτ''0 : (0:ℝ) < ‖x - y‖ / (8 * M / 3) := by positivity
  have hFARC0 : (0:ℝ) ≤ Real.exp (M ^ 2)
      * ((‖x - y‖ / (8 * M / 3)) ^ (-((n:ℝ)/2 + 3/2))
        + 8 * ‖x - y‖ ^ 2 * (‖x - y‖ / (8 * M / 3)) ^ (-((n:ℝ)/2 + 5/2))
        + 4 * M ^ 2 * (‖x - y‖ / (8 * M / 3)) ^ (-((n:ℝ)/2 + 1/2))) := by positivity
  intro w hw τ hτ0 hτ1
  obtain ⟨hwM, hwlow, hwhigh⟩ := hUmem w hw
  have hG := hGbnd w hwM (1 - τ) (by linarith) (by linarith)
  rw [show (1:ℝ) - (1 - τ) = τ from by ring,
    show -(n:ℝ)/2 - 3/2 = -((n:ℝ)/2 + 3/2) from by ring] at hG
  have hGs := hG
  have hpa : (0:ℝ) < τ ^ (-((n:ℝ)/2 + 3/2)) := Real.rpow_pos_of_pos hτ0 _
  have hstep1 : τ ^ (-((n:ℝ)/2 + 3/2)) / τ = τ ^ (-((n:ℝ)/2 + 5/2)) := by
    rw [← Real.rpow_sub_one (ne_of_gt hτ0)]
    congr 1
    ring
  have hstep2 : τ ^ (-((n:ℝ)/2 + 3/2)) * τ = τ ^ (-((n:ℝ)/2 + 1/2)) := by
    rw [← Real.rpow_add_one (ne_of_gt hτ0)]
    congr 1
    ring
  rcases le_or_gt τ (‖x - y‖ / (8 * M / 3)) with hcase | hcase
  · -- near range
    have hτM : τ * M ≤ 3 * ‖x - y‖ / 8 := by
      have h := (le_div_iff₀ (show (0:ℝ) < 8 * M / 3 by positivity)).1 hcase
      nlinarith [h]
    have hsq : (‖w - y‖ + τ * M) ^ 2 ≤ 4 * ‖x - y‖ ^ 2 := by
      have h1 : ‖w - y‖ + τ * M ≤ 2 * ‖x - y‖ := by linarith
      have h2 : (0:ℝ) ≤ ‖w - y‖ + τ * M := by positivity
      have h3 := pow_le_pow_left₀ h2 h1 2
      linarith only [h3, sq_nonneg ‖x - y‖]
    have hlow2 : 3 * ‖x - y‖ / 8 ≤ ‖w - (1 - τ) • y‖ := by
      have := hsepw w τ hτ0; linarith
    have hsq2 : (3 * ‖x - y‖ / 8) ^ 2 ≤ ‖w - (1 - τ) • y‖ ^ 2 :=
      pow_le_pow_left₀ (by positivity) hlow2 2
    have hexpd : Real.exp (-‖w - (1 - τ) • y‖ ^ 2 / (2 * τ))
        ≤ Real.exp (-(9/128 * ‖x - y‖ ^ 2) / τ) := by
      refine Real.exp_le_exp.2 ?_
      rw [show -(9/128 * ‖x - y‖ ^ 2) / τ = -(9/64 * ‖x - y‖ ^ 2) / (2 * τ) by
        rw [div_eq_div_iff (ne_of_gt hτ0) (by positivity)]; ring]
      refine hdivmono _ _ _ (by positivity) ?_
      linarith only [hsq2]
    have hmid : Real.exp (M ^ 2) * τ ^ (-((n:ℝ)/2 + 3/2))
          * (1 + 2 * (‖w - y‖ + τ * M) ^ 2 / τ)
          * Real.exp (-‖w - (1 - τ) • y‖ ^ 2 / (2 * τ))
        ≤ Real.exp (M ^ 2) * τ ^ (-((n:ℝ)/2 + 3/2))
          * (1 + 2 * (4 * ‖x - y‖ ^ 2) / τ)
          * Real.exp (-(9/128 * ‖x - y‖ ^ 2) / τ) := by
      refine mul_le_mul ?_ hexpd (Real.exp_pos _).le (by positivity)
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      gcongr
    refine le_trans (le_trans hGs hmid) ?_
    have hrw : Real.exp (M ^ 2) * τ ^ (-((n:ℝ)/2 + 3/2))
          * (1 + 2 * (4 * ‖x - y‖ ^ 2) / τ)
          * Real.exp (-(9/128 * ‖x - y‖ ^ 2) / τ)
        = Real.exp (M ^ 2) * (τ ^ (-((n:ℝ)/2 + 3/2))
              * Real.exp (-(9/128 * ‖x - y‖ ^ 2) / τ))
          + Real.exp (M ^ 2) * (8 * ‖x - y‖ ^ 2) * (τ ^ (-((n:ℝ)/2 + 5/2))
              * Real.exp (-(9/128 * ‖x - y‖ ^ 2) / τ)) := by
      rw [← hstep1]
      field_simp
      ring
    rw [hrw]
    linarith [hFARC0]
  · -- far range
    have hle1 : Real.exp (-‖w - (1 - τ) • y‖ ^ 2 / (2 * τ)) ≤ 1 := by
      refine Real.exp_le_one_iff.2 ?_
      rw [div_nonpos_iff]
      exact Or.inr ⟨neg_nonpos.2 (by positivity), by positivity⟩
    have hsq : (‖w - y‖ + τ * M) ^ 2 ≤ 4 * ‖x - y‖ ^ 2 + 2 * τ ^ 2 * M ^ 2 := by
      have h2 : (0:ℝ) ≤ ‖w - y‖ := norm_nonneg _
      have hA := hsqsum ‖w - y‖ (τ * M)
      have hB := pow_le_pow_left₀ h2 hwhigh 2
      have hC : 2 * (τ * M) ^ 2 = 2 * τ ^ 2 * M ^ 2 := by ring
      have hD : (5 * ‖x - y‖ / 4) ^ 2 = 25 / 16 * ‖x - y‖ ^ 2 := by ring
      rw [hD] at hB
      linarith only [hA, hB, hC, sq_nonneg ‖x - y‖]
    have hmid : Real.exp (M ^ 2) * τ ^ (-((n:ℝ)/2 + 3/2))
          * (1 + 2 * (‖w - y‖ + τ * M) ^ 2 / τ)
          * Real.exp (-‖w - (1 - τ) • y‖ ^ 2 / (2 * τ))
        ≤ Real.exp (M ^ 2) * τ ^ (-((n:ℝ)/2 + 3/2))
          * (1 + 2 * (4 * ‖x - y‖ ^ 2 + 2 * τ ^ 2 * M ^ 2) / τ) * 1 := by
      refine mul_le_mul ?_ hle1 (Real.exp_pos _).le (by positivity)
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      gcongr
    have hrw : Real.exp (M ^ 2) * τ ^ (-((n:ℝ)/2 + 3/2))
          * (1 + 2 * (4 * ‖x - y‖ ^ 2 + 2 * τ ^ 2 * M ^ 2) / τ) * 1
        = Real.exp (M ^ 2) * (τ ^ (-((n:ℝ)/2 + 3/2))
            + 8 * ‖x - y‖ ^ 2 * τ ^ (-((n:ℝ)/2 + 5/2))
            + 4 * M ^ 2 * τ ^ (-((n:ℝ)/2 + 1/2))) := by
      rw [← hstep1, ← hstep2]
      field_simp
      ring
    refine le_trans (le_trans hGs hmid) ?_
    rw [hrw]
    have ha1 : τ ^ (-((n:ℝ)/2 + 3/2)) ≤ (‖x - y‖ / (8 * M / 3)) ^ (-((n:ℝ)/2 + 3/2)) :=
      hanti _ _ _ hτ''0 hcase.le (by linarith)
    have ha2 : τ ^ (-((n:ℝ)/2 + 5/2)) ≤ (‖x - y‖ / (8 * M / 3)) ^ (-((n:ℝ)/2 + 5/2)) :=
      hanti _ _ _ hτ''0 hcase.le (by linarith)
    have ha3 : τ ^ (-((n:ℝ)/2 + 1/2)) ≤ (‖x - y‖ / (8 * M / 3)) ^ (-((n:ℝ)/2 + 1/2)) :=
      hanti _ _ _ hτ''0 hcase.le (by linarith)
    have hc1 : (0:ℝ) ≤ Real.exp (M ^ 2) := (Real.exp_pos _).le
    have hc2 : (0:ℝ) ≤ 8 * ‖x - y‖ ^ 2 := by positivity
    have hc3 : (0:ℝ) ≤ 4 * M ^ 2 := by positivity
    have hnear0 : (0:ℝ) ≤ Real.exp (M ^ 2) * (τ ^ (-((n:ℝ)/2 + 3/2))
          * Real.exp (-(9/128 * ‖x - y‖ ^ 2) / τ))
        + Real.exp (M ^ 2) * (8 * ‖x - y‖ ^ 2) * (τ ^ (-((n:ℝ)/2 + 5/2))
          * Real.exp (-(9/128 * ‖x - y‖ ^ 2) / τ)) := by positivity
    have hsum := mul_le_mul_of_nonneg_left
      (add_le_add (add_le_add ha1 (mul_le_mul_of_nonneg_left ha2 hc2))
        (mul_le_mul_of_nonneg_left ha3 hc3)) hc1
    linarith [hsum, hnear0]
