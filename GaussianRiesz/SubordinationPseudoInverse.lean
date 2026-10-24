import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import GaussianRiesz.OUSemigroupSpectral
import GaussianRiesz.FracPowLinear
import GaussianRiesz.OneLeMultiIndexSum
open MeasureTheory
theorem SubordinationPseudoInverse {n : ℕ} (f : Lp ℝ 2 (GaussMeasure n)) :
    IntegrableOn (fun s : ℝ => (Real.sqrt s)⁻¹ • OUSemigroup s (FracPow (0 : ℝ) f))
        (Set.Ioi (0 : ℝ))
      ∧ FracPow (-(1 : ℝ) / 2) f
          = (Real.sqrt Real.pi)⁻¹ •
              ∫ s in Set.Ioi (0 : ℝ), (Real.sqrt s)⁻¹ • OUSemigroup s (FracPow (0 : ℝ) f) := by
  classical
  -- Step 0: the Hermite coefficients of `L^t f` for `t ≤ 0` (where the domain is everything),
  -- then of `Π₀ f = L⁰ f`, then of `P_s Π₀ f`.
  have hreprFP : ∀ t : ℝ, t ≤ 0 → ∀ α : Fin n → ℕ,
      (HermiteBasis n).repr (FracPow t f) α
        = FracPowCoeff t (fun β => (HermiteBasis n).repr f β) α := by
    intro t ht α
    have hm : Memℓp (FracPowCoeff t (fun β => (HermiteBasis n).repr f β)) 2 :=
      (FracPowLinear t).1 ht f
    simp only [FracPow]
    rw [dif_pos hm, LinearIsometryEquiv.apply_symm_apply]
  have hproj : ∀ α : Fin n → ℕ,
      (HermiteBasis n).repr (FracPow (0 : ℝ) f) α
        = if α = 0 then 0 else (HermiteBasis n).repr f α := by
    intro α
    rw [hreprFP 0 le_rfl α]
    unfold FracPowCoeff
    by_cases hα : α = 0
    · simp [hα]
    · rw [if_neg hα, if_neg hα, Real.rpow_zero, one_mul]
  have hspec : ∀ s : ℝ, 0 ≤ s → ∀ α : Fin n → ℕ,
      (HermiteBasis n).repr (OUSemigroup s (FracPow (0 : ℝ) f)) α
        = Real.exp (-s * MultiIndexSum α)
            * (if α = 0 then 0 else (HermiteBasis n).repr f α) := by
    intro s hs α
    rw [OUSemigroupSpectral s hs _ α, hproj α]
  -- Step 1: the uniform exponential norm bound `‖P_s Π₀ f‖ ≤ e^{-s}‖f‖` for every `s ≥ 0`.
  -- `|α| ≥ 1` on the support of the coefficient family is what makes this hold on all of
  -- `(0,∞)` at once, so no splitting at `s = 1` is needed anywhere below.
  have hnormbd : ∀ s : ℝ, 0 ≤ s →
      ‖OUSemigroup s (FracPow (0 : ℝ) f)‖ ≤ Real.exp (-s) * ‖f‖ := by
    intro s hs
    have hbd : ∀ α : Fin n → ℕ,
        ‖(HermiteBasis n).repr (OUSemigroup s (FracPow (0 : ℝ) f)) α‖
          ≤ ‖(Real.exp (-s) • (HermiteBasis n).repr f) α‖ := by
      intro α
      rw [hspec s hs α, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul]
      by_cases hα : α = 0
      · rw [if_pos hα, mul_zero, norm_zero]
        exact norm_nonneg _
      · rw [if_neg hα, norm_mul, norm_mul]
        refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
        rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _),
          abs_of_pos (Real.exp_pos _), Real.exp_le_exp]
        have h1 : (1 : ℝ) ≤ (MultiIndexSum α : ℝ) := OneLeMultiIndexSum α hα
        nlinarith
    have hs1 := lp.hasSum_norm (p := (2 : ENNReal)) (by norm_num)
      ((HermiteBasis n).repr (OUSemigroup s (FracPow (0 : ℝ) f)))
    have hs2 := lp.hasSum_norm (p := (2 : ENNReal)) (by norm_num)
      (Real.exp (-s) • (HermiteBasis n).repr f)
    have hle :
        ‖(HermiteBasis n).repr (OUSemigroup s (FracPow (0 : ℝ) f))‖ ^ ((2 : ENNReal).toReal)
          ≤ ‖Real.exp (-s) • (HermiteBasis n).repr f‖ ^ ((2 : ENNReal).toReal) :=
      hasSum_le (fun α => Real.rpow_le_rpow (norm_nonneg _) (hbd α) ENNReal.toReal_nonneg)
        hs1 hs2
    have c1 : ∀ x : ℝ, x ^ ((2 : ENNReal).toReal) = x ^ (2 : ℕ) := by
      intro x
      rw [show ((2 : ENNReal)).toReal = ((2 : ℕ) : ℝ) from by norm_num, Real.rpow_natCast]
    rw [c1, c1, norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _),
      (HermiteBasis n).repr.norm_map, (HermiteBasis n).repr.norm_map] at hle
    have hb : (0 : ℝ) ≤ Real.exp (-s) * ‖f‖ := by positivity
    have hsq := Real.sqrt_le_sqrt hle
    rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq hb] at hsq
  -- Step 3: strong measurability, through the Hermite expansion.  `OUSemigroupSpectral`
  -- needs `0 ≤ s`, so the auxiliary function uses `|s|`, which agrees with `s` on `(0,∞)`;
  -- the finite partial sums are continuous and converge pointwise, which is all the
  -- measurable-limit lemma asks for.
  have hsum : ∀ s : ℝ,
      HasSum (fun α : Fin n → ℕ =>
          (Real.exp (-|s| * MultiIndexSum α)
            * (if α = 0 then 0 else (HermiteBasis n).repr f α)) • (HermiteBasis n) α)
        (OUSemigroup |s| (FracPow (0 : ℝ) f)) := by
    intro s
    have hfun : (fun α : Fin n → ℕ =>
        (Real.exp (-|s| * MultiIndexSum α)
          * (if α = 0 then 0 else (HermiteBasis n).repr f α)) • (HermiteBasis n) α)
        = fun α : Fin n → ℕ =>
          (HermiteBasis n).repr (OUSemigroup |s| (FracPow (0 : ℝ) f)) α • (HermiteBasis n) α := by
      funext α
      rw [hspec |s| (abs_nonneg s) α]
    rw [hfun]
    exact (HermiteBasis n).hasSum_repr _
  have hpart : ∀ S : Finset (Fin n → ℕ),
      StronglyMeasurable (fun s : ℝ => ∑ α ∈ S,
        (Real.exp (-|s| * MultiIndexSum α)
          * (if α = 0 then 0 else (HermiteBasis n).repr f α)) • (HermiteBasis n) α) := by
    intro S
    refine Continuous.stronglyMeasurable (continuous_finsetSum S fun α _ => ?_)
    have hcs : Continuous (fun s : ℝ => Real.exp (-|s| * (MultiIndexSum α : ℝ))
        * (if α = 0 then 0 else (HermiteBasis n).repr f α)) := by fun_prop
    exact hcs.smul continuous_const
  have hGmeas : StronglyMeasurable (fun s : ℝ => OUSemigroup |s| (FracPow (0 : ℝ) f)) :=
    stronglyMeasurable_of_tendsto (Filter.atTop : Filter (Finset (Fin n → ℕ))) hpart
      (tendsto_pi_nhds.mpr fun s => hsum s)
  have hAEm : AEStronglyMeasurable
      (fun s : ℝ => (Real.sqrt s)⁻¹ • OUSemigroup s (FracPow (0 : ℝ) f))
      (volume.restrict (Set.Ioi (0 : ℝ))) := by
    have hw : StronglyMeasurable (fun s : ℝ => (Real.sqrt s)⁻¹) := by fun_prop
    have hprod : StronglyMeasurable
        (fun s : ℝ => (Real.sqrt s)⁻¹ • OUSemigroup |s| (FracPow (0 : ℝ) f)) := hw.smul hGmeas
    refine (hprod.aestronglyMeasurable).congr ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    rw [abs_of_pos hs]
  -- Step 2 at `λ = 1`: the scalar weight is integrable on `(0,∞)`.
  have hweight : IntegrableOn (fun s : ℝ => (Real.sqrt s)⁻¹ * Real.exp (-s))
      (Set.Ioi (0 : ℝ)) := by
    have hconv : IntegrableOn (fun x : ℝ => Real.exp (-x) * x ^ ((1 : ℝ) / 2 - 1))
        (Set.Ioi 0) := Real.GammaIntegral_convergent (by norm_num)
    refine hconv.congr_fun (fun s hs => ?_) measurableSet_Ioi
    have hs' : (0 : ℝ) ≤ s := le_of_lt hs
    rw [Real.sqrt_eq_rpow, ← Real.rpow_neg hs',
      show ((1 : ℝ) / 2 - 1) = -((1 : ℝ) / 2) from by norm_num, mul_comm]
  -- Step 4: clause (1).  Strong measurability together with an integrable norm majorant.
  have hint : IntegrableOn
      (fun s : ℝ => (Real.sqrt s)⁻¹ • OUSemigroup s (FracPow (0 : ℝ) f))
      (Set.Ioi (0 : ℝ)) := by
    refine Integrable.mono' (g := fun s : ℝ => ‖f‖ * ((Real.sqrt s)⁻¹ * Real.exp (-s)))
      (hweight.const_mul ‖f‖) hAEm ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_nonneg (Real.sqrt_nonneg s)]
    have h2 := hnormbd s (le_of_lt hs)
    have h3 : (0 : ℝ) ≤ (Real.sqrt s)⁻¹ := by positivity
    calc (Real.sqrt s)⁻¹ * ‖OUSemigroup s (FracPow (0 : ℝ) f)‖
        ≤ (Real.sqrt s)⁻¹ * (Real.exp (-s) * ‖f‖) := mul_le_mul_of_nonneg_left h2 h3
      _ = ‖f‖ * ((Real.sqrt s)⁻¹ * Real.exp (-s)) := by ring
  -- Step 2 at a general `λ > 0`: the scalar subordination integral.
  have hscalar : ∀ lam : ℝ, 0 < lam →
      ∫ s in Set.Ioi (0 : ℝ), (Real.sqrt s)⁻¹ * Real.exp (-s * lam)
        = (1 / lam) ^ ((1 : ℝ) / 2) * Real.sqrt Real.pi := by
    intro lam hlam
    have hpt : ∀ s ∈ Set.Ioi (0 : ℝ),
        (fun s : ℝ => s ^ ((1 : ℝ) / 2 - 1) * Real.exp (-(lam * s))) s
          = (fun s : ℝ => (Real.sqrt s)⁻¹ * Real.exp (-s * lam)) s := by
      intro s hs
      have hs' : (0 : ℝ) ≤ s := le_of_lt hs
      simp only
      rw [Real.sqrt_eq_rpow, ← Real.rpow_neg hs',
        show ((1 : ℝ) / 2 - 1) = -((1 : ℝ) / 2) from by norm_num,
        show -(lam * s) = -s * lam from by ring]
    rw [← setIntegral_congr_fun measurableSet_Ioi hpt,
      Real.integral_rpow_mul_exp_neg_mul_Ioi (by norm_num : (0 : ℝ) < (1 : ℝ) / 2) hlam,
      Real.Gamma_one_half_eq]
  -- Step 5: the Hermite coefficients of the Bochner integral, via the continuous functional
  -- `innerSL ℝ (h_α)`, whose value at `v` is exactly the `α`-th coefficient of `v`.
  have hL : ∀ (α : Fin n → ℕ) (v : Lp ℝ 2 (GaussMeasure n)),
      (innerSL ℝ ((HermiteBasis n) α)) v = (HermiteBasis n).repr v α := by
    intro α v
    rw [innerSL_apply_apply, (HermiteBasis n).repr_apply_apply]
  have hIcoef : ∀ α : Fin n → ℕ,
      (HermiteBasis n).repr
          (∫ s in Set.Ioi (0 : ℝ), (Real.sqrt s)⁻¹ • OUSemigroup s (FracPow (0 : ℝ) f)) α
        = ∫ s in Set.Ioi (0 : ℝ), (Real.sqrt s)⁻¹
            * (Real.exp (-s * MultiIndexSum α)
                * (if α = 0 then 0 else (HermiteBasis n).repr f α)) := by
    intro α
    have hcomm := ContinuousLinearMap.integral_comp_commSL (by simp)
      (innerSL ℝ ((HermiteBasis n) α)) hint
    calc (HermiteBasis n).repr
            (∫ s in Set.Ioi (0 : ℝ), (Real.sqrt s)⁻¹ • OUSemigroup s (FracPow (0 : ℝ) f)) α
        = (innerSL ℝ ((HermiteBasis n) α))
            (∫ s in Set.Ioi (0 : ℝ), (Real.sqrt s)⁻¹ • OUSemigroup s (FracPow (0 : ℝ) f)) :=
          (hL α _).symm
      _ = ∫ s in Set.Ioi (0 : ℝ), (innerSL ℝ ((HermiteBasis n) α))
            ((Real.sqrt s)⁻¹ • OUSemigroup s (FracPow (0 : ℝ) f)) := hcomm.symm
      _ = ∫ s in Set.Ioi (0 : ℝ), (Real.sqrt s)⁻¹
            * (Real.exp (-s * MultiIndexSum α)
                * (if α = 0 then 0 else (HermiteBasis n).repr f α)) := by
          refine setIntegral_congr_fun measurableSet_Ioi fun s hs => ?_
          rw [ContinuousLinearMap.map_smul, smul_eq_mul, hL α, hspec s (le_of_lt hs) α]
  -- Step 6: both sides have the same Hermite coefficients, and the coefficient map is
  -- injective.
  refine ⟨hint, (HermiteBasis n).repr.injective (lp.ext (funext fun α => ?_))⟩
  rw [map_smul, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, hIcoef α,
    hreprFP (-(1 : ℝ) / 2) (by norm_num) α]
  by_cases hα : α = 0
  · simp [FracPowCoeff, hα]
  · have hlam : (0 : ℝ) < (MultiIndexSum α : ℝ) :=
      lt_of_lt_of_le zero_lt_one (OneLeMultiIndexSum α hα)
    have hK : ∫ s in Set.Ioi (0 : ℝ), (Real.sqrt s)⁻¹
          * (Real.exp (-s * MultiIndexSum α)
              * (if α = 0 then 0 else (HermiteBasis n).repr f α))
        = ((1 / (MultiIndexSum α : ℝ)) ^ ((1 : ℝ) / 2) * Real.sqrt Real.pi)
            * (HermiteBasis n).repr f α := by
      rw [if_neg hα]
      simp only [← mul_assoc]
      rw [integral_mul_const, hscalar _ hlam]
    have hrw : (1 / (MultiIndexSum α : ℝ)) ^ ((1 : ℝ) / 2)
        = (MultiIndexSum α : ℝ) ^ (-(1 : ℝ) / 2) := by
      rw [one_div, Real.inv_rpow (le_of_lt hlam), ← Real.rpow_neg (le_of_lt hlam)]
      norm_num
    have hpi : Real.sqrt Real.pi ≠ 0 := by positivity
    rw [hK, hrw]
    unfold FracPowCoeff
    rw [if_neg hα]
    field_simp
