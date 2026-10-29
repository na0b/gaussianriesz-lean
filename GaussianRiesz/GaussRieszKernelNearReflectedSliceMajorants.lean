module

public import GaussianRiesz.GaussRieszKernelNearSliceBounds

@[expose] public section
open MeasureTheory Filter Topology
theorem GaussRieszKernelNearReflectedSliceMajorants {n : ℕ} (j : Fin n) (M : ℝ)
    (hM : 3 ≤ M) :
    ∀ x y : EuclideanSpace ℝ (Fin n), ‖x‖ ≤ M → ‖y‖ ≤ M → ‖x - y‖ ≤ 2 →
      (∀ τ : ℝ, 0 < τ → τ ≤ ‖x - y‖ / (2 * M) →
        |(y j - (1 - τ) * x j)
              / ((1 - (1 - τ) ^ 2) ^ ((n : ℝ) / 2 + 1) * Real.sqrt (-Real.log (1 - τ)))
            * Real.exp (-‖(1 - τ) • x - y‖ ^ 2 / (1 - (1 - τ) ^ 2))|
          ≤ Real.exp (M ^ 2) * (3 / 2 * ‖x - y‖)
              * (τ ^ (-((n:ℝ)/2 + 3/2)) * Real.exp (-(‖x - y‖ ^ 2 / 8) / τ)))
        ∧ (∀ τ : ℝ, 0 < τ → τ < 1 →
        |(y j - (1 - τ) * x j)
              / ((1 - (1 - τ) ^ 2) ^ ((n : ℝ) / 2 + 1) * Real.sqrt (-Real.log (1 - τ)))
            * Real.exp (-‖(1 - τ) • x - y‖ ^ 2 / (1 - (1 - τ) ^ 2))|
          ≤ Real.exp (M ^ 2) * ‖x - y‖ * τ ^ (-((n:ℝ)/2 + 3/2))
              + Real.exp (M ^ 2) * M * τ ^ (-(((n:ℝ) + 2) / 2))) := by
  intro x y hxM hyM hd2
  have hsl := (GaussRieszKernelNearSliceBounds j M hM y hyM).2.1 x hxM
  have h7t : ∀ τ : ℝ, 0 < τ → τ < 1 →
      |(y j - (1 - τ) * x j)
            / ((1 - (1 - τ) ^ 2) ^ ((n : ℝ) / 2 + 1) * Real.sqrt (-Real.log (1 - τ)))
          * Real.exp (-‖(1 - τ) • x - y‖ ^ 2 / (1 - (1 - τ) ^ 2))|
        ≤ Real.exp (M ^ 2) * (‖x - y‖ + τ * M) * τ ^ (-(n : ℝ) / 2 - 3 / 2)
            * Real.exp (-‖x - (1 - τ) • y‖ ^ 2 / (2 * τ)) := by
    intro τ hτ0 hτ1
    have h := hsl (1 - τ) (by linarith) (by linarith)
    simpa [sub_sub_cancel] using h
  have hsep : ∀ τ : ℝ, 0 < τ → ‖x - y‖ - τ * M ≤ ‖x - (1 - τ) • y‖ := by
    intro τ hτ0
    have e1 : x - (1 - τ) • y = (x - y) - (-(τ • y)) := by
      rw [sub_smul, one_smul]; abel
    have e2 : ‖-(τ • y)‖ ≤ τ * M := by
      rw [norm_neg, norm_smul, Real.norm_eq_abs, abs_of_pos hτ0]
      exact mul_le_mul_of_nonneg_left hyM hτ0.le
    have := norm_sub_norm_le (x - y) (-(τ • y))
    rw [← e1] at this
    linarith
  have hτ'3 : ‖x - y‖ / (2 * M) ≤ 1 / 3 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
  refine ⟨?_, ?_⟩
  ·
    intro τ hτ0 hτle
    have hτ1 : τ < 1 := by linarith
    have hτM : τ * M ≤ ‖x - y‖ / 2 := by
      have h := (le_div_iff₀ (show (0:ℝ) < 2 * M by positivity)).1 hτle
      nlinarith [h]
    have hlow : ‖x - y‖ / 2 ≤ ‖x - (1 - τ) • y‖ := by
      have := hsep τ hτ0; linarith
    have hsq : (‖x - y‖ / 2) ^ 2 ≤ ‖x - (1 - τ) • y‖ ^ 2 :=
      pow_le_pow_left₀ (by positivity) hlow 2
    have hexpd : Real.exp (-‖x - (1 - τ) • y‖ ^ 2 / (2 * τ))
        ≤ Real.exp (-(‖x - y‖ ^ 2 / 8) / τ) := by
      refine Real.exp_le_exp.2 ?_
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [mul_nonneg (sub_nonneg.2 hsq) hτ0.le]
    have hexp' : -(n : ℝ) / 2 - 3 / 2 = -((n:ℝ)/2 + 3/2) := by ring
    have hpow : (0:ℝ) < τ ^ (-((n:ℝ)/2 + 3/2)) := Real.rpow_pos_of_pos hτ0 _
    calc |(y j - (1 - τ) * x j)
              / ((1 - (1 - τ) ^ 2) ^ ((n : ℝ) / 2 + 1) * Real.sqrt (-Real.log (1 - τ)))
            * Real.exp (-‖(1 - τ) • x - y‖ ^ 2 / (1 - (1 - τ) ^ 2))|
        ≤ Real.exp (M ^ 2) * (‖x - y‖ + τ * M) * τ ^ (-(n : ℝ) / 2 - 3 / 2)
            * Real.exp (-‖x - (1 - τ) • y‖ ^ 2 / (2 * τ)) := h7t τ hτ0 hτ1
      _ = Real.exp (M ^ 2) * (‖x - y‖ + τ * M) * τ ^ (-((n:ℝ)/2 + 3/2))
            * Real.exp (-‖x - (1 - τ) • y‖ ^ 2 / (2 * τ)) := by rw [hexp']
      _ ≤ Real.exp (M ^ 2) * (3 / 2 * ‖x - y‖) * τ ^ (-((n:ℝ)/2 + 3/2))
            * Real.exp (-(‖x - y‖ ^ 2 / 8) / τ) := by
          refine mul_le_mul ?_ hexpd (Real.exp_pos _).le (by positivity)
          refine mul_le_mul_of_nonneg_right ?_ hpow.le
          exact mul_le_mul_of_nonneg_left (by linarith) (Real.exp_pos _).le
      _ = Real.exp (M ^ 2) * (3 / 2 * ‖x - y‖)
            * (τ ^ (-((n:ℝ)/2 + 3/2)) * Real.exp (-(‖x - y‖ ^ 2 / 8) / τ)) := by ring
  ·
    intro τ hτ0 hτ1
    have hexp' : -(n : ℝ) / 2 - 3 / 2 = -((n:ℝ)/2 + 3/2) := by ring
    have hpow : (0:ℝ) < τ ^ (-((n:ℝ)/2 + 3/2)) := Real.rpow_pos_of_pos hτ0 _
    have hle1 : Real.exp (-‖x - (1 - τ) • y‖ ^ 2 / (2 * τ)) ≤ 1 := by
      refine Real.exp_le_one_iff.2 ?_
      rw [div_nonpos_iff]
      exact Or.inr ⟨neg_nonpos.2 (by positivity), by positivity⟩
    have hmulpow : τ * τ ^ (-((n:ℝ)/2 + 3/2)) = τ ^ (1 - ((n:ℝ)/2 + 3/2)) := by
      rw [mul_comm, ← Real.rpow_add_one (ne_of_gt hτ0)]
      congr 1
      ring
    have hcmp : τ ^ (1 - ((n:ℝ)/2 + 3/2)) ≤ τ ^ (-(((n:ℝ) + 2) / 2)) :=
      Real.rpow_le_rpow_of_exponent_ge hτ0 hτ1.le (by linarith)
    calc |(y j - (1 - τ) * x j)
              / ((1 - (1 - τ) ^ 2) ^ ((n : ℝ) / 2 + 1) * Real.sqrt (-Real.log (1 - τ)))
            * Real.exp (-‖(1 - τ) • x - y‖ ^ 2 / (1 - (1 - τ) ^ 2))|
        ≤ Real.exp (M ^ 2) * (‖x - y‖ + τ * M) * τ ^ (-(n : ℝ) / 2 - 3 / 2)
            * Real.exp (-‖x - (1 - τ) • y‖ ^ 2 / (2 * τ)) := h7t τ hτ0 hτ1
      _ = Real.exp (M ^ 2) * (‖x - y‖ + τ * M) * τ ^ (-((n:ℝ)/2 + 3/2))
            * Real.exp (-‖x - (1 - τ) • y‖ ^ 2 / (2 * τ)) := by rw [hexp']
      _ ≤ Real.exp (M ^ 2) * (‖x - y‖ + τ * M) * τ ^ (-((n:ℝ)/2 + 3/2)) * 1 := by
          refine mul_le_mul_of_nonneg_left hle1 ?_
          have : (0:ℝ) ≤ ‖x - y‖ + τ * M := by positivity
          positivity
      _ = Real.exp (M ^ 2) * ‖x - y‖ * τ ^ (-((n:ℝ)/2 + 3/2))
            + Real.exp (M ^ 2) * M * (τ * τ ^ (-((n:ℝ)/2 + 3/2))) := by ring
      _ = Real.exp (M ^ 2) * ‖x - y‖ * τ ^ (-((n:ℝ)/2 + 3/2))
            + Real.exp (M ^ 2) * M * τ ^ (1 - ((n:ℝ)/2 + 3/2)) := by rw [hmulpow]
      _ ≤ Real.exp (M ^ 2) * ‖x - y‖ * τ ^ (-((n:ℝ)/2 + 3/2))
            + Real.exp (M ^ 2) * M * τ ^ (-(((n:ℝ) + 2) / 2)) := by
          have hc : (0:ℝ) ≤ Real.exp (M ^ 2) * M := by positivity
          linarith [mul_le_mul_of_nonneg_left hcmp hc]
