module

public import GaussianRiesz.Preamble
public import GaussianRiesz.ExpDecayPowerBoundAndRpowAbsorption
public import GaussianRiesz.MehlerNumeratorCoordinateBallBound

@[expose] public section
open MeasureTheory
theorem GaussRieszKernelSingularRangeSliceBound {n : ℕ} (j : Fin n)
    (R' ρ' τ₀ : ℝ) (hR1 : 1 ≤ R') (hρ'0 : 0 < ρ')
    (hτ₀0 : 0 < τ₀) (hτ₀h : τ₀ ≤ 1/2) (hτ₀ρ : τ₀ ≤ ρ' / (8 * R')) :
    ∃ C₂ : ℝ, 0 < C₂ ∧
      ∀ (x y : EuclideanSpace ℝ (Fin n)), ‖x‖ ≤ R' → ρ' ≤ ‖x - y‖ →
        ∀ r : ℝ, 1/2 ≤ r → r < 1 →
          |(y j - r * x j) / ((1 - r ^ 2) ^ ((n : ℝ) / 2 + 1) * Real.sqrt (-Real.log r)) * Real.exp (-‖x - r • y‖ ^ 2 / (1 - r ^ 2))| ≤ C₂ := by
  have hR'0 : (0:ℝ) < R' := by linarith
  -- The range `r ∈ [1/2, 1)` is where the `r`-integrand of the raw kernel is singular.
  -- Writing `τ = 1 - r`, the prefactor is at most `τ^{-(n+3)/2}` and the Gaussian factor
  -- at most `exp(-d²/(2τ))` with `d = |x - r y|`; the elementary bound
  -- `e^{-t} ≤ m^m / t^m` at `m = n+2` converts that decay into a power `τ^m` that
  -- absorbs the prefactor completely, leaving a constant.  The only case analysis is on
  -- whether `|y|` is comparable to `R` (so that `d ≳ ρ` for small `τ`) or large (so that
  -- `d ≳ |y|`), plus the trivial range of `τ` bounded away from `0`.
  have hlog : ∀ r : ℝ, 0 < r → r < 1 → 1 - r ≤ -Real.log r := by
    intro r h0 _
    have := Real.log_le_sub_one_of_pos h0
    linarith
  have hpow := (ExpDecayPowerBoundAndRpowAbsorption (n := n)).1
  have hPpos : ∀ r : ℝ, 0 < r → r < 1 →
      0 < (1 - r ^ 2) ^ ((n : ℝ) / 2 + 1) * Real.sqrt (-Real.log r) := by
    intro r h0 h1
    have h2 : (0:ℝ) < 1 - r ^ 2 := by
      have := pow_lt_one₀ h0.le h1 (two_ne_zero); linarith
    have h3 : (0:ℝ) < -Real.log r := by have := Real.log_neg h0 h1; linarith
    have h4 : (0:ℝ) < (1 - r ^ 2) ^ ((n : ℝ) / 2 + 1) := Real.rpow_pos_of_pos h2 _
    have h5 : (0:ℝ) < Real.sqrt (-Real.log r) := Real.sqrt_pos.2 h3
    positivity
  have habs := (ExpDecayPowerBoundAndRpowAbsorption (n := n)).2

  have hnum := MehlerNumeratorCoordinateBallBound j R'
  have hK3 : ∀ r : ℝ, 1/2 ≤ r → r < 1 →
      ((1 - r ^ 2) ^ ((n : ℝ) / 2 + 1) * Real.sqrt (-Real.log r))⁻¹
        ≤ (1 - r) ^ (-((n : ℝ) / 2 + 3/2)) := by
    intro r h1 h2
    have h0 : (0:ℝ) < r := by linarith
    have hτ0 : (0:ℝ) < 1 - r := by linarith
    have hb2 : 1 - r ≤ 1 - r ^ 2 := by
      nlinarith [mul_nonneg h0.le (by linarith : (0:ℝ) ≤ 1 - r)]
    have e1 : (1 - r) ^ ((n : ℝ) / 2 + 1) ≤ (1 - r ^ 2) ^ ((n : ℝ) / 2 + 1) :=
      Real.rpow_le_rpow hτ0.le hb2 (by positivity)
    have e2 : Real.sqrt (1 - r) ≤ Real.sqrt (-Real.log r) :=
      Real.sqrt_le_sqrt (hlog r h0 h2)
    have e3 : (1 - r) ^ ((n : ℝ) / 2 + 1) * Real.sqrt (1 - r)
        = (1 - r) ^ ((n : ℝ) / 2 + 3/2) := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_add hτ0]
      congr 1
      ring
    have e4 : (0:ℝ) < (1 - r) ^ ((n : ℝ) / 2 + 1) := Real.rpow_pos_of_pos hτ0 _
    have e6 : (1 - r) ^ ((n : ℝ) / 2 + 3/2)
        ≤ (1 - r ^ 2) ^ ((n : ℝ) / 2 + 1) * Real.sqrt (-Real.log r) := by
      rw [← e3]
      exact mul_le_mul e1 e2 (Real.sqrt_nonneg _) (le_trans e4.le e1)
    rw [Real.rpow_neg hτ0.le]
    exact inv_anti₀ (Real.rpow_pos_of_pos hτ0 _) e6

  have hMp : (0:ℝ) < ((n : ℝ) + 2) ^ (n + 2) := pow_pos (by positivity) (n + 2)
  have h8 : (0:ℝ) < ((8:ℝ) / ρ' ^ 2) ^ (n + 2) :=
    pow_pos (div_pos (by norm_num) (pow_pos hρ'0 2)) (n + 2)
  have h32 : (0:ℝ) < ((32:ℝ)) ^ (n + 2) := pow_pos (by norm_num) (n + 2)
  have hτp : (0:ℝ) < τ₀ ^ (-((n : ℝ) / 2 + 3/2)) := Real.rpow_pos_of_pos hτ₀0 _
  refine ⟨5 * R' * (((n : ℝ) + 2) ^ (n + 2) * ((8:ℝ) / ρ' ^ 2) ^ (n + 2))
      + 5 * R' * τ₀ ^ (-((n : ℝ) / 2 + 3/2))
      + (5/4) * (((n : ℝ) + 2) ^ (n + 2) * ((32:ℝ)) ^ (n + 2)), ?_, ?_⟩
  · have e1 : (0:ℝ) < 5 * R' * (((n : ℝ) + 2) ^ (n + 2) * ((8:ℝ) / ρ' ^ 2) ^ (n + 2)) :=
      mul_pos (by linarith) (mul_pos hMp h8)
    have e2 : (0:ℝ) < 5 * R' * τ₀ ^ (-((n : ℝ) / 2 + 3/2)) := mul_pos (by linarith) hτp
    have e3 : (0:ℝ) < (5/4) * (((n : ℝ) + 2) ^ (n + 2) * ((32:ℝ)) ^ (n + 2)) :=
      mul_pos (by norm_num) (mul_pos hMp h32)
    linarith
  intro x y hx hxy r h1 h2
  have hT10 : (0:ℝ) ≤ 5 * R' * (((n : ℝ) + 2) ^ (n + 2) * ((8:ℝ) / ρ' ^ 2) ^ (n + 2)) :=
    (mul_pos (by linarith : (0:ℝ) < 5 * R') (mul_pos hMp h8)).le
  have hT20 : (0:ℝ) ≤ 5 * R' * τ₀ ^ (-((n : ℝ) / 2 + 3/2)) :=
    (mul_pos (by linarith : (0:ℝ) < 5 * R') hτp).le
  have hT30 : (0:ℝ) ≤ (5/4) * (((n : ℝ) + 2) ^ (n + 2) * ((32:ℝ)) ^ (n + 2)) :=
    (mul_pos (by norm_num : (0:ℝ) < (5:ℝ)/4) (mul_pos hMp h32)).le
  have h0 : (0:ℝ) < r := by linarith
  have hτ0 : (0:ℝ) < 1 - r := by linarith
  have hr2 : (0:ℝ) < 1 - r ^ 2 := by
    have := pow_lt_one₀ h0.le h2 (two_ne_zero); linarith
  have hP := hPpos r h0 h2
  have hpre := hK3 r h1 h2
  have hpre0 : (0:ℝ) ≤ ((1 - r ^ 2) ^ ((n : ℝ) / 2 + 1) * Real.sqrt (-Real.log r))⁻¹ := inv_nonneg.2 hP.le
  have hprenn : (0:ℝ) ≤ (1 - r) ^ (-((n : ℝ) / 2 + 3/2)) :=
    (Real.rpow_pos_of_pos hτ0 _).le
  have hval : |(y j - r * x j) / ((1 - r ^ 2) ^ ((n : ℝ) / 2 + 1) * Real.sqrt (-Real.log r)) * Real.exp (-‖x - r • y‖ ^ 2 / (1 - r ^ 2))|
      = |y j - r * x j| * ((1 - r ^ 2) ^ ((n : ℝ) / 2 + 1) * Real.sqrt (-Real.log r))⁻¹ * Real.exp (-‖x - r • y‖ ^ 2 / (1 - r ^ 2)) := by
    rw [abs_mul, abs_div, abs_of_pos hP, abs_of_pos (Real.exp_pos _), div_eq_mul_inv]
  rw [hval]
  have hexp2 : Real.exp (-‖x - r • y‖ ^ 2 / (1 - r ^ 2))
      ≤ Real.exp (-(‖x - r • y‖ ^ 2 / (2 * (1 - r)))) := by
    refine Real.exp_le_exp.2 ?_
    have h12 : 1 - r ^ 2 ≤ 2 * (1 - r) := by nlinarith [sq_nonneg (1 - r)]
    have hd2 : (0:ℝ) ≤ ‖x - r • y‖ ^ 2 := sq_nonneg _
    rw [neg_div, neg_le_neg_iff]
    exact div_le_div_of_nonneg_left hd2 hr2 h12
  rcases le_or_gt ‖y‖ (4 * R') with hy | hy
  · have hn5 : |y j - r * x j| ≤ 5 * R' := by
      have := hnum x y hx r h0.le h2.le; linarith
    have hd : ρ' - 4 * R' * (1 - r) ≤ ‖x - r • y‖ := by
      have e1 : ‖x - y‖ ≤ ‖x - r • y‖ + ‖(1 - r) • y‖ := by
        have e2 : x - y = (x - r • y) - (1 - r) • y := by rw [sub_smul, one_smul]; abel
        calc ‖x - y‖ = ‖(x - r • y) - (1 - r) • y‖ := by rw [e2]
          _ ≤ ‖x - r • y‖ + ‖(1 - r) • y‖ := norm_sub_le _ _
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hτ0.le] at e1
      linarith [hxy, mul_le_mul_of_nonneg_left hy hτ0.le]
    rcases le_or_gt (1 - r) τ₀ with hc | hc
    · have h4R : 4 * R' * (1 - r) ≤ ρ' / 2 := by
        have e0 := le_trans hc hτ₀ρ
        rw [le_div_iff₀ (by linarith : (0:ℝ) < 8 * R')] at e0
        linarith
      have hd2 : ρ' / 2 ≤ ‖x - r • y‖ := by linarith
      have hdec : Real.exp (-(‖x - r • y‖ ^ 2 / (2 * (1 - r))))
          ≤ ((n : ℝ) + 2) ^ (n + 2) * (((8:ℝ) / ρ' ^ 2) * (1 - r)) ^ (n + 2) := by
        have ht : (0:ℝ) < ρ' ^ 2 / (8 * (1 - r)) := div_pos (pow_pos hρ'0 2) (by linarith)
        have hsq : (ρ' / 2) ^ 2 ≤ ‖x - r • y‖ ^ 2 :=
          pow_le_pow_left₀ (by linarith) hd2 2
        have e1 : ρ' ^ 2 / (8 * (1 - r)) ≤ ‖x - r • y‖ ^ 2 / (2 * (1 - r)) := by
          rw [div_le_div_iff₀ (by linarith) (by linarith)]
          linarith [mul_le_mul_of_nonneg_right hsq (by linarith : (0:ℝ) ≤ 8 * (1 - r))]
        have e2 := hpow (ρ' ^ 2 / (8 * (1 - r))) ht
        have e3 : (ρ' ^ 2 / (8 * (1 - r)))⁻¹ = ((8:ℝ) / ρ' ^ 2) * (1 - r) := by
          rw [inv_div]
          field_simp
        rw [e3] at e2
        exact le_trans (Real.exp_le_exp.2 (by linarith)) e2
      calc |y j - r * x j| * ((1 - r ^ 2) ^ ((n : ℝ) / 2 + 1) * Real.sqrt (-Real.log r))⁻¹ * Real.exp (-‖x - r • y‖ ^ 2 / (1 - r ^ 2))
          ≤ 5 * R' * (1 - r) ^ (-((n : ℝ) / 2 + 3/2))
              * (((n : ℝ) + 2) ^ (n + 2) * (((8:ℝ) / ρ' ^ 2) * (1 - r)) ^ (n + 2)) := by
            refine mul_le_mul (mul_le_mul hn5 hpre hpre0 (by linarith))
              (le_trans hexp2 hdec) (Real.exp_pos _).le
              (mul_nonneg (by linarith) hprenn)
        _ = 5 * R' * ((1 - r) ^ (-((n : ℝ) / 2 + 3/2))
              * (((n : ℝ) + 2) ^ (n + 2) * (((8:ℝ) / ρ' ^ 2) * (1 - r)) ^ (n + 2))) := by ring
        _ ≤ 5 * R' * (((n : ℝ) + 2) ^ (n + 2) * ((8:ℝ) / ρ' ^ 2) ^ (n + 2)) :=
            mul_le_mul_of_nonneg_left
              (habs r ((8:ℝ) / ρ' ^ 2) h1 h2 (div_pos (by norm_num) (pow_pos hρ'0 2)))
              (by linarith)
        _ ≤ _ := by linarith
    · have hpre' : (1 - r) ^ (-((n : ℝ) / 2 + 3/2)) ≤ τ₀ ^ (-((n : ℝ) / 2 + 3/2)) := by
        rw [Real.rpow_neg hτ0.le, Real.rpow_neg hτ₀0.le]
        exact inv_anti₀ (Real.rpow_pos_of_pos hτ₀0 _)
          (Real.rpow_le_rpow hτ₀0.le hc.le (by positivity))
      have hexp1 : Real.exp (-‖x - r • y‖ ^ 2 / (1 - r ^ 2)) ≤ 1 := by
        rw [Real.exp_le_one_iff, neg_div, neg_nonpos]
        exact div_nonneg (sq_nonneg _) hr2.le
      calc |y j - r * x j| * ((1 - r ^ 2) ^ ((n : ℝ) / 2 + 1) * Real.sqrt (-Real.log r))⁻¹ * Real.exp (-‖x - r • y‖ ^ 2 / (1 - r ^ 2))
          ≤ 5 * R' * τ₀ ^ (-((n : ℝ) / 2 + 3/2)) * 1 := by
            refine mul_le_mul (mul_le_mul hn5 (le_trans hpre hpre') hpre0 (by linarith))
              hexp1 (Real.exp_pos _).le (mul_nonneg (by linarith) hτp.le)
        _ ≤ _ := by linarith
  · have hy1 : (1:ℝ) < ‖y‖ := by linarith
    have hy0 : (0:ℝ) < ‖y‖ := by linarith
    have hn5 : |y j - r * x j| ≤ (5/4) * ‖y‖ := by
      have := hnum x y hx r h0.le h2.le; linarith
    have hd : ‖y‖ / 4 ≤ ‖x - r • y‖ := by
      have h5 : ‖r • y‖ - ‖x‖ ≤ ‖r • y - x‖ := norm_sub_norm_le _ _
      rw [norm_sub_rev, norm_smul, Real.norm_eq_abs, abs_of_pos h0] at h5
      linarith [hx, mul_le_mul_of_nonneg_right h1 hy0.le]
    have hdec : Real.exp (-(‖x - r • y‖ ^ 2 / (2 * (1 - r))))
        ≤ ((n : ℝ) + 2) ^ (n + 2) * (((32:ℝ) / ‖y‖ ^ 2) * (1 - r)) ^ (n + 2) := by
      have ht : (0:ℝ) < ‖y‖ ^ 2 / (32 * (1 - r)) := div_pos (pow_pos hy0 2) (by linarith)
      have hsq : (‖y‖ / 4) ^ 2 ≤ ‖x - r • y‖ ^ 2 :=
        pow_le_pow_left₀ (by linarith) hd 2
      have e1 : ‖y‖ ^ 2 / (32 * (1 - r)) ≤ ‖x - r • y‖ ^ 2 / (2 * (1 - r)) := by
        rw [div_le_div_iff₀ (by linarith) (by linarith)]
        linarith [mul_le_mul_of_nonneg_right hsq (by linarith : (0:ℝ) ≤ 32 * (1 - r))]
      have e2 := hpow (‖y‖ ^ 2 / (32 * (1 - r))) ht
      have e3 : (‖y‖ ^ 2 / (32 * (1 - r)))⁻¹ = ((32:ℝ) / ‖y‖ ^ 2) * (1 - r) := by
        rw [inv_div]
        field_simp
      rw [e3] at e2
      exact le_trans (Real.exp_le_exp.2 (by linarith)) e2
    have hyp : (0:ℝ) < ‖y‖ ^ (2 * (n + 2)) := pow_pos hy0 _
    have hyle : ‖y‖ / ‖y‖ ^ (2 * (n + 2)) ≤ 1 := by
      rw [div_le_one hyp]
      exact le_self_pow₀ hy1.le (by omega)
    calc |y j - r * x j| * ((1 - r ^ 2) ^ ((n : ℝ) / 2 + 1) * Real.sqrt (-Real.log r))⁻¹ * Real.exp (-‖x - r • y‖ ^ 2 / (1 - r ^ 2))
        ≤ (5/4) * ‖y‖ * (1 - r) ^ (-((n : ℝ) / 2 + 3/2))
            * (((n : ℝ) + 2) ^ (n + 2) * (((32:ℝ) / ‖y‖ ^ 2) * (1 - r)) ^ (n + 2)) := by
          refine mul_le_mul (mul_le_mul hn5 hpre hpre0 (by linarith))
            (le_trans hexp2 hdec) (Real.exp_pos _).le
            (mul_nonneg (by linarith) hprenn)
      _ = (5/4) * ‖y‖ * ((1 - r) ^ (-((n : ℝ) / 2 + 3/2))
            * (((n : ℝ) + 2) ^ (n + 2) * (((32:ℝ) / ‖y‖ ^ 2) * (1 - r)) ^ (n + 2))) := by ring
      _ ≤ (5/4) * ‖y‖ * (((n : ℝ) + 2) ^ (n + 2) * ((32:ℝ) / ‖y‖ ^ 2) ^ (n + 2)) :=
          mul_le_mul_of_nonneg_left
            (habs r ((32:ℝ) / ‖y‖ ^ 2) h1 h2 (div_pos (by norm_num) (pow_pos hy0 2)))
            (by linarith)
      _ = (5/4) * (((n : ℝ) + 2) ^ (n + 2) * ((32:ℝ)) ^ (n + 2))
            * (‖y‖ / ‖y‖ ^ (2 * (n + 2))) := by
          rw [div_pow, ← pow_mul]; ring
      _ ≤ (5/4) * (((n : ℝ) + 2) ^ (n + 2) * ((32:ℝ)) ^ (n + 2)) * 1 :=
          mul_le_mul_of_nonneg_left hyle hT30
      _ ≤ _ := by linarith
