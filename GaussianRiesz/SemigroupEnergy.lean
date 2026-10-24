import GaussianRiesz.OUSemigroupSpectral
import GaussianRiesz.ScalarFractional
import GaussianRiesz.SubordinationIntegrandIntegrable
open MeasureTheory Set
theorem SemigroupEnergy {n : ℕ} (v : Lp ℝ 2 (GaussMeasure n)) :
    Energy v = ENNReal.ofReal (1 / (2 * Real.sqrt Real.pi))
      * ∫⁻ s in Set.Ioi (0 : ℝ),
          ENNReal.ofReal (inner ℝ (v - OUSemigroup s v) v / s ^ ((3 : ℝ) / 2)) := by
  classical
  -- (0) the real inner product, and square-summability of the Hermite coefficients
  have hmul : ∀ a b : ℝ, (inner ℝ a b : ℝ) = a * b := by
    intro a b; simp [RCLike.inner_apply, mul_comm]
  have c1 : ∀ x : ℝ, ‖x‖ ^ ((2:ENNReal).toReal) = x ^ (2:ℕ) := by
    intro x
    rw [show ((2 : ENNReal)).toReal = ((2 : ℕ) : ℝ) from by norm_num, Real.rpow_natCast,
      Real.norm_eq_abs, ← abs_pow, abs_of_nonneg (by positivity)]
  have hsq : Summable (fun α : Fin n → ℕ => ((HermiteBasis n).repr v α) ^ 2) := by
    have hv : Summable fun β : Fin n → ℕ =>
        ‖(HermiteBasis n).repr v β‖ ^ ((2 : ENNReal).toReal) :=
      (memℓp_gen_iff (p := (2 : ENNReal)) (by norm_num)).mp (lp.memℓp ((HermiteBasis n).repr v))
    exact hv.congr fun β => c1 _
  -- the multiplier `1 - e^{-s|α|}` lies in `[0,1]`
  have hnn1 : ∀ (s : ℝ) (α : Fin n → ℕ), 0 ≤ s →
      0 ≤ 1 - Real.exp (-s * (MultiIndexSum α : ℝ)) := by
    intro s α hs
    have : Real.exp (-s * (MultiIndexSum α : ℝ)) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      nlinarith
    linarith
  have hle1 : ∀ (s : ℝ) (α : Fin n → ℕ),
      1 - Real.exp (-s * (MultiIndexSum α : ℝ)) ≤ 1 := by
    intro s α
    linarith [Real.exp_pos (-s * (MultiIndexSum α : ℝ))]
  have hsumα : ∀ s : ℝ, 0 ≤ s → Summable (fun α : Fin n → ℕ =>
      (1 - Real.exp (-s * (MultiIndexSum α : ℝ))) * ((HermiteBasis n).repr v α) ^ 2) := by
    intro s hs
    refine Summable.of_nonneg_of_le (fun α => ?_) (fun α => ?_) hsq
    · exact mul_nonneg (hnn1 s α hs) (sq_nonneg _)
    · exact mul_le_of_le_one_left (sq_nonneg _) (hle1 s α)
  -- (1) spectral expansion of the integrand (Parseval plus `OUSemigroupSpectral`)
  have hstep1 : ∀ s : ℝ, 0 ≤ s → (inner ℝ (v - OUSemigroup s v) v : ℝ)
      = ∑' α : Fin n → ℕ,
          (1 - Real.exp (-s * (MultiIndexSum α : ℝ))) * ((HermiteBasis n).repr v α) ^ 2 := by
    intro s hs
    rw [← (HermiteBasis n).repr.inner_map_map (v - OUSemigroup s v) v, lp.inner_eq_tsum]
    refine tsum_congr fun α => ?_
    rw [hmul, map_sub, lp.coeFn_sub, Pi.sub_apply, OUSemigroupSpectral s hs v α]
    ring
  -- (3) its value, from `ScalarFractional`
  have hval : ∀ lam : ℝ, 0 ≤ lam →
      ∫ s in Ioi (0:ℝ), (1 - Real.exp (-s * lam)) / s ^ ((3:ℝ)/2)
        = 2 * Real.sqrt Real.pi * Real.sqrt lam := by
    intro lam hlam
    have hpi2 : (2 * Real.sqrt Real.pi) ≠ 0 := by positivity
    have h := ScalarFractional lam hlam
    rw [div_mul_eq_mul_div, one_mul, div_eq_iff hpi2] at h
    rw [h]
    ring
  -- (4) the one-index lower integral
  have hone : ∀ α : Fin n → ℕ,
      ∫⁻ s in Ioi (0:ℝ), ENNReal.ofReal
          ((1 - Real.exp (-s * (MultiIndexSum α : ℝ))) * ((HermiteBasis n).repr v α) ^ 2
            / s ^ ((3:ℝ)/2))
        = ENNReal.ofReal (((HermiteBasis n).repr v α) ^ 2)
          * ENNReal.ofReal (2 * Real.sqrt Real.pi * Real.sqrt (MultiIndexSum α : ℝ)) := by
    intro α
    have hm : (0:ℝ) ≤ (MultiIndexSum α : ℝ) := Nat.cast_nonneg _
    have hcong : ∀ᵐ s ∂(volume.restrict (Ioi (0:ℝ))),
        ENNReal.ofReal ((1 - Real.exp (-s * (MultiIndexSum α : ℝ)))
              * ((HermiteBasis n).repr v α) ^ 2 / s ^ ((3:ℝ)/2))
          = ENNReal.ofReal (((HermiteBasis n).repr v α) ^ 2)
            * ENNReal.ofReal ((1 - Real.exp (-s * (MultiIndexSum α : ℝ))) / s ^ ((3:ℝ)/2)) := by
      filter_upwards with s
      rw [show (1 - Real.exp (-s * (MultiIndexSum α : ℝ))) * ((HermiteBasis n).repr v α) ^ 2
            / s ^ ((3:ℝ)/2)
          = ((HermiteBasis n).repr v α) ^ 2
            * ((1 - Real.exp (-s * (MultiIndexSum α : ℝ))) / s ^ ((3:ℝ)/2)) from by ring,
        ENNReal.ofReal_mul (sq_nonneg _)]
    rw [lintegral_congr_ae hcong, lintegral_const_mul _ (by fun_prop)]
    congr 1
    rw [← ofReal_integral_eq_lintegral_ofReal (SubordinationIntegrandIntegrable _ hm) ?_, hval _ hm]
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    have hs0 : (0:ℝ) < s := hs
    have hnn := hnn1 s α hs0.le
    positivity
  -- (5) Tonelli: interchange the Hermite sum and the lower integral, with no finiteness needed
  have hint : ∀ᵐ s ∂(volume.restrict (Ioi (0:ℝ))),
      ENNReal.ofReal ((inner ℝ (v - OUSemigroup s v) v : ℝ) / s ^ ((3:ℝ)/2))
        = ∑' α : Fin n → ℕ, ENNReal.ofReal
            ((1 - Real.exp (-s * (MultiIndexSum α : ℝ))) * ((HermiteBasis n).repr v α) ^ 2
              / s ^ ((3:ℝ)/2)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    have hs0 : (0:ℝ) < s := hs
    rw [hstep1 s hs0.le, ← tsum_div_const]
    refine ENNReal.ofReal_tsum_of_nonneg (fun α => ?_) ((hsumα s hs0.le).div_const _)
    have := hnn1 s α hs0.le
    positivity
  rw [lintegral_congr_ae hint, lintegral_tsum (fun α => by fun_prop), tsum_congr hone,
    ← ENNReal.tsum_mul_left]
  -- (6) each term collapses to the `Energy` summand
  have hterm : ∀ α : Fin n → ℕ,
      ENNReal.ofReal (1 / (2 * Real.sqrt Real.pi))
          * (ENNReal.ofReal (((HermiteBasis n).repr v α) ^ 2)
            * ENNReal.ofReal (2 * Real.sqrt Real.pi * Real.sqrt (MultiIndexSum α : ℝ)))
        = ENNReal.ofReal ((MultiIndexSum α : ℝ) ^ ((1:ℝ)/2)
            * ((HermiteBasis n).repr v α) ^ 2) := by
    intro α
    rw [← ENNReal.ofReal_mul (sq_nonneg ((HermiteBasis n).repr v α)),
      ← ENNReal.ofReal_mul (show (0:ℝ) ≤ 1 / (2 * Real.sqrt Real.pi) by positivity)]
    congr 1
    rw [← Real.sqrt_eq_rpow]
    field_simp
  rw [tsum_congr hterm]
  -- (7) the `α = 0` term vanishes, so the subtype sum is the full sum
  have hsupp : Function.support (fun α : Fin n → ℕ => ENNReal.ofReal
      ((MultiIndexSum α : ℝ) ^ ((1:ℝ)/2) * ((HermiteBasis n).repr v α) ^ 2))
      ⊆ {α : Fin n → ℕ | α ≠ 0} := by
    intro α hα
    simp only [Function.mem_support] at hα
    by_contra h
    simp only [Set.mem_ofPred_eq, not_not] at h
    subst h
    exact hα (by simp [MultiIndexSum, Real.zero_rpow])
  rw [Energy]
  exact tsum_subtype_eq_of_support_subset hsupp
