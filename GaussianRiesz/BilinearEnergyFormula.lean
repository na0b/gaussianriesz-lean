import GaussianRiesz.OUSelfAdjointContraction
import GaussianRiesz.EnergyBil
import GaussianRiesz.EnergyFormBilinear
import GaussianRiesz.ScalarFractional
open MeasureTheory Set
theorem BilinearEnergyFormula {n : ℕ} (v w : Lp ℝ 2 (GaussMeasure n))
    (hv : Energy v ≠ ⊤) (hw : Energy w ≠ ⊤) :
    IntegrableOn (fun s : ℝ => inner ℝ (v - OUSemigroup s v) w / s ^ ((3 : ℝ) / 2))
        (Set.Ioi (0 : ℝ))
      ∧ EnergyBil v w = (1 / (2 * Real.sqrt Real.pi))
          * ∫ s in Set.Ioi (0 : ℝ), inner ℝ (v - OUSemigroup s v) w / s ^ ((3 : ℝ) / 2) := by
  classical
  have hmul : ∀ a b : ℝ, (inner ℝ a b : ℝ) = a * b := by
    intro a b; simp [RCLike.inner_apply, mul_comm]
  have hm0 : ∀ α : Fin n → ℕ, (0 : ℝ) ≤ (MultiIndexSum α : ℝ) := fun α => Nat.cast_nonneg _
  -- (0) square-summability of the Hermite coefficients, and of the mixed product
  have c1 : ∀ x : ℝ, ‖x‖ ^ ((2 : ENNReal).toReal) = x ^ (2 : ℕ) := by
    intro x
    rw [show ((2 : ENNReal)).toReal = ((2 : ℕ) : ℝ) from by norm_num, Real.rpow_natCast,
      Real.norm_eq_abs, ← abs_pow, abs_of_nonneg (by positivity)]
  have hsq : ∀ u : Lp ℝ 2 (GaussMeasure n),
      Summable (fun α : Fin n → ℕ => ((HermiteBasis n).repr u α) ^ 2) := by
    intro u
    have h : Summable fun β : Fin n → ℕ =>
        ‖(HermiteBasis n).repr u β‖ ^ ((2 : ENNReal).toReal) :=
      (memℓp_gen_iff (p := (2 : ENNReal)) (by norm_num)).mp (lp.memℓp ((HermiteBasis n).repr u))
    exact h.congr fun β => c1 _
  have hprod : Summable (fun α : Fin n → ℕ =>
      |((HermiteBasis n).repr v α) * ((HermiteBasis n).repr w α)|) := by
    refine Summable.of_nonneg_of_le (fun α => abs_nonneg _) (fun α => ?_)
      (((hsq v).add (hsq w)).mul_left (1 / 2 : ℝ))
    rw [abs_mul]
    nlinarith [sq_abs ((HermiteBasis n).repr v α), sq_abs ((HermiteBasis n).repr w α),
      sq_nonneg (|(HermiteBasis n).repr v α| - |(HermiteBasis n).repr w α|)]
  -- (1) spectral expansion of the integrand, over the full index and then over `α ≠ 0`
  have hstep1 : ∀ s : ℝ, 0 ≤ s → (inner ℝ (v - OUSemigroup s v) w : ℝ)
      = ∑' α : Fin n → ℕ,
          (1 - Real.exp (-s * (MultiIndexSum α : ℝ)))
            * ((HermiteBasis n).repr v α) * ((HermiteBasis n).repr w α) := by
    intro s hs
    rw [← (HermiteBasis n).repr.inner_map_map (v - OUSemigroup s v) w, lp.inner_eq_tsum]
    refine tsum_congr fun α => ?_
    rw [hmul, map_sub, lp.coeFn_sub, Pi.sub_apply, OUSemigroupSpectral s hs v α]
    ring
  have hsupp0 : ∀ s : ℝ, Function.support (fun α : Fin n → ℕ =>
      (1 - Real.exp (-s * (MultiIndexSum α : ℝ)))
        * ((HermiteBasis n).repr v α) * ((HermiteBasis n).repr w α))
      ⊆ {α : Fin n → ℕ | α ≠ 0} := by
    intro s α hα
    simp only [Function.mem_support] at hα
    by_contra h
    simp only [Set.mem_ofPred_eq, not_not] at h
    subst h
    exact hα (by simp [MultiIndexSum])
  have hstep1' : ∀ s : ℝ, 0 ≤ s → (inner ℝ (v - OUSemigroup s v) w : ℝ)
      = ∑' α : {α : Fin n → ℕ // α ≠ 0},
          (1 - Real.exp (-s * (MultiIndexSum (α : Fin n → ℕ) : ℝ)))
            * ((HermiteBasis n).repr v (α : Fin n → ℕ))
            * ((HermiteBasis n).repr w (α : Fin n → ℕ)) := by
    intro s hs
    rw [hstep1 s hs]
    exact (tsum_subtype_eq_of_support_subset (hsupp0 s)).symm
  -- (2) the scalar integral: its value from `ScalarFractional`, and its integrability
  -- EXTRACTED FROM THE VALUE because the value is provably nonzero
  have hval : ∀ lam : ℝ, 0 ≤ lam →
      ∫ s in Ioi (0 : ℝ), (1 - Real.exp (-s * lam)) / s ^ ((3 : ℝ) / 2)
        = 2 * Real.sqrt Real.pi * Real.sqrt lam := by
    intro lam hlam
    have hpi2 : (2 * Real.sqrt Real.pi) ≠ 0 := by positivity
    have h := ScalarFractional lam hlam
    rw [div_mul_eq_mul_div, one_mul, div_eq_iff hpi2] at h
    rw [h]; ring
  have hAint : ∀ lam : ℝ, 0 ≤ lam →
      IntegrableOn (fun s : ℝ => (1 - Real.exp (-s * lam)) / s ^ ((3 : ℝ) / 2))
        (Ioi (0 : ℝ)) := by
    intro lam hlam
    rcases eq_or_lt_of_le hlam with h0 | hpos
    · have hz : (fun s : ℝ => (1 - Real.exp (-s * lam)) / s ^ ((3 : ℝ) / 2))
          = fun _ : ℝ => (0 : ℝ) := by
        funext s; rw [← h0]; simp
      rw [hz]
      exact integrableOn_zero
    · by_contra hcon
      have h0 : ∫ s in Ioi (0 : ℝ), (1 - Real.exp (-s * lam)) / s ^ ((3 : ℝ) / 2) = 0 :=
        integral_undef hcon
      rw [hval lam hlam] at h0
      have hne : 2 * Real.sqrt Real.pi * Real.sqrt lam ≠ 0 := by positivity
      exact hne h0
  -- (3) the per-index summand `F α`, its integral, and the norm of its integral
  have hFint : ∀ α : {α : Fin n → ℕ // α ≠ 0},
      IntegrableOn (fun s : ℝ =>
        (((HermiteBasis n).repr v (α : Fin n → ℕ)) * ((HermiteBasis n).repr w (α : Fin n → ℕ)))
          * ((1 - Real.exp (-s * (MultiIndexSum (α : Fin n → ℕ) : ℝ))) / s ^ ((3 : ℝ) / 2)))
        (Ioi (0 : ℝ)) := fun α => (hAint _ (hm0 _)).const_mul _
  have hFval : ∀ α : {α : Fin n → ℕ // α ≠ 0},
      (∫ s in Ioi (0 : ℝ),
        (((HermiteBasis n).repr v (α : Fin n → ℕ)) * ((HermiteBasis n).repr w (α : Fin n → ℕ)))
          * ((1 - Real.exp (-s * (MultiIndexSum (α : Fin n → ℕ) : ℝ))) / s ^ ((3 : ℝ) / 2)))
        = (((HermiteBasis n).repr v (α : Fin n → ℕ))
            * ((HermiteBasis n).repr w (α : Fin n → ℕ)))
          * (2 * Real.sqrt Real.pi * Real.sqrt (MultiIndexSum (α : Fin n → ℕ) : ℝ)) := by
    intro α
    rw [integral_const_mul, hval _ (hm0 _)]
  have hFnorm : ∀ α : {α : Fin n → ℕ // α ≠ 0},
      (∫ s in Ioi (0 : ℝ), ‖(((HermiteBasis n).repr v (α : Fin n → ℕ))
          * ((HermiteBasis n).repr w (α : Fin n → ℕ)))
          * ((1 - Real.exp (-s * (MultiIndexSum (α : Fin n → ℕ) : ℝ))) / s ^ ((3 : ℝ) / 2))‖)
        = |((HermiteBasis n).repr v (α : Fin n → ℕ))
            * ((HermiteBasis n).repr w (α : Fin n → ℕ))|
          * (2 * Real.sqrt Real.pi * Real.sqrt (MultiIndexSum (α : Fin n → ℕ) : ℝ)) := by
    intro α
    have hcong : ∀ᵐ s ∂(volume.restrict (Ioi (0 : ℝ))),
        ‖(((HermiteBasis n).repr v (α : Fin n → ℕ))
            * ((HermiteBasis n).repr w (α : Fin n → ℕ)))
            * ((1 - Real.exp (-s * (MultiIndexSum (α : Fin n → ℕ) : ℝ)))
              / s ^ ((3 : ℝ) / 2))‖
          = |((HermiteBasis n).repr v (α : Fin n → ℕ))
              * ((HermiteBasis n).repr w (α : Fin n → ℕ))|
            * ((1 - Real.exp (-s * (MultiIndexSum (α : Fin n → ℕ) : ℝ)))
              / s ^ ((3 : ℝ) / 2)) := by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
      have hs0 : (0 : ℝ) < s := hs
      have hexp : Real.exp (-s * (MultiIndexSum (α : Fin n → ℕ) : ℝ)) ≤ 1 := by
        rw [Real.exp_le_one_iff]
        nlinarith [hm0 (α : Fin n → ℕ)]
      have hnn : 0 ≤ (1 - Real.exp (-s * (MultiIndexSum (α : Fin n → ℕ) : ℝ)))
          / s ^ ((3 : ℝ) / 2) := by
        have h1 : 0 ≤ 1 - Real.exp (-s * (MultiIndexSum (α : Fin n → ℕ) : ℝ)) := by linarith
        positivity
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hnn]
    rw [integral_congr_ae hcong, integral_const_mul, hval _ (hm0 _)]
  -- (4) summability of the integrals of the norms: `EnergyFormBilinear` plus `summable_abs_iff`
  have hF_sum : Summable (fun α : {α : Fin n → ℕ // α ≠ 0} =>
      ∫ s in Ioi (0 : ℝ), ‖(((HermiteBasis n).repr v (α : Fin n → ℕ))
          * ((HermiteBasis n).repr w (α : Fin n → ℕ)))
          * ((1 - Real.exp (-s * (MultiIndexSum (α : Fin n → ℕ) : ℝ)))
            / s ^ ((3 : ℝ) / 2))‖) := by
    have habs := (EnergyFormBilinear.1 v w hv hw).abs
    refine (habs.mul_left (2 * Real.sqrt Real.pi)).congr fun α => ?_
    rw [hFnorm α]
    have hwt : (0 : ℝ) ≤ (MultiIndexSum (α : Fin n → ℕ) : ℝ) ^ ((1 : ℝ) / 2) :=
      Real.rpow_nonneg (hm0 _) _
    simp only [abs_mul, abs_of_nonneg hwt]
    rw [← Real.sqrt_eq_rpow]
    ring
  -- (5) THE MEASURABILITY OBLIGATION: `s ↦ ⟪(I-P_s)v, w⟫` is a uniformly summable series of
  -- continuous functions once `s` is replaced by `|s|`, which costs nothing on `(0,∞)`
  have hcont : Continuous (fun s : ℝ => ∑' α : {α : Fin n → ℕ // α ≠ 0},
      (1 - Real.exp (-|s| * (MultiIndexSum (α : Fin n → ℕ) : ℝ)))
        * ((HermiteBasis n).repr v (α : Fin n → ℕ))
        * ((HermiteBasis n).repr w (α : Fin n → ℕ))) := by
    refine continuous_tsum (fun α => by fun_prop) (hprod.subtype _) (fun α s => ?_)
    have hx : (0 : ℝ) ≤ |s| * (MultiIndexSum (α : Fin n → ℕ) : ℝ) :=
      mul_nonneg (abs_nonneg s) (hm0 _)
    have hexp : Real.exp (-|s| * (MultiIndexSum (α : Fin n → ℕ) : ℝ)) ≤ 1 := by
      rw [Real.exp_le_one_iff]; nlinarith
    have hpos : 0 < Real.exp (-|s| * (MultiIndexSum (α : Fin n → ℕ) : ℝ)) := Real.exp_pos _
    rw [Real.norm_eq_abs, mul_assoc, abs_mul,
      abs_of_nonneg (show (0:ℝ) ≤ 1 - Real.exp (-|s| * (MultiIndexSum (α : Fin n → ℕ) : ℝ))
        by linarith)]
    calc (1 - Real.exp (-|s| * (MultiIndexSum (α : Fin n → ℕ) : ℝ)))
          * |((HermiteBasis n).repr v (α : Fin n → ℕ))
              * ((HermiteBasis n).repr w (α : Fin n → ℕ))|
        ≤ 1 * |((HermiteBasis n).repr v (α : Fin n → ℕ))
              * ((HermiteBasis n).repr w (α : Fin n → ℕ))| := by
          exact mul_le_mul_of_nonneg_right (by linarith) (abs_nonneg _)
      _ = _ := one_mul _
  have hmeas0 : AEStronglyMeasurable (fun s : ℝ => (inner ℝ (v - OUSemigroup s v) w : ℝ))
      (volume.restrict (Ioi (0 : ℝ))) := by
    refine hcont.aestronglyMeasurable.congr ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    have hs0 : (0 : ℝ) < s := hs
    rw [abs_of_pos hs0]
    exact (hstep1' s hs0.le).symm
  -- (6) the integrand splits as the series, pointwise on `(0,∞)`
  have hsplit : ∀ s : ℝ, s ∈ Ioi (0 : ℝ) →
      (inner ℝ (v - OUSemigroup s v) w : ℝ) / s ^ ((3 : ℝ) / 2)
        = ∑' α : {α : Fin n → ℕ // α ≠ 0},
            (((HermiteBasis n).repr v (α : Fin n → ℕ))
              * ((HermiteBasis n).repr w (α : Fin n → ℕ)))
              * ((1 - Real.exp (-s * (MultiIndexSum (α : Fin n → ℕ) : ℝ)))
                / s ^ ((3 : ℝ) / 2)) := by
    intro s hs
    have hs0 : (0 : ℝ) < s := hs
    rw [hstep1' s hs0.le, ← tsum_div_const]
    exact tsum_congr fun α => by ring
  -- (7) conjunct 1: integrability
  have hIint : IntegrableOn
      (fun s : ℝ => inner ℝ (v - OUSemigroup s v) w / s ^ ((3 : ℝ) / 2)) (Ioi (0 : ℝ)) := by
    have hdenom : AEMeasurable (fun s : ℝ => s ^ ((3 : ℝ) / 2))
        (volume.restrict (Ioi (0 : ℝ))) := by fun_prop
    refine ⟨aestronglyMeasurable_iff_aemeasurable.mpr (hmeas0.aemeasurable.div hdenom), ?_⟩
    rw [hasFiniteIntegral_iff_enorm]
    calc ∫⁻ s in Ioi (0 : ℝ),
            ‖(inner ℝ (v - OUSemigroup s v) w : ℝ) / s ^ ((3 : ℝ) / 2)‖ₑ
        ≤ ∫⁻ s in Ioi (0 : ℝ), ∑' α : {α : Fin n → ℕ // α ≠ 0},
            ‖(((HermiteBasis n).repr v (α : Fin n → ℕ))
              * ((HermiteBasis n).repr w (α : Fin n → ℕ)))
              * ((1 - Real.exp (-s * (MultiIndexSum (α : Fin n → ℕ) : ℝ)))
                / s ^ ((3 : ℝ) / 2))‖ₑ := by
          refine lintegral_mono_ae ?_
          filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
          rw [hsplit s hs]
          exact enorm_tsum_le_tsum_enorm
      _ = ∑' α : {α : Fin n → ℕ // α ≠ 0}, ∫⁻ s in Ioi (0 : ℝ),
            ‖(((HermiteBasis n).repr v (α : Fin n → ℕ))
              * ((HermiteBasis n).repr w (α : Fin n → ℕ)))
              * ((1 - Real.exp (-s * (MultiIndexSum (α : Fin n → ℕ) : ℝ)))
                / s ^ ((3 : ℝ) / 2))‖ₑ := lintegral_tsum (fun α => by fun_prop)
      _ < ⊤ := by
          have hre : ∀ α : {α : Fin n → ℕ // α ≠ 0},
              (∫⁻ s in Ioi (0 : ℝ),
                ‖(((HermiteBasis n).repr v (α : Fin n → ℕ))
                  * ((HermiteBasis n).repr w (α : Fin n → ℕ)))
                  * ((1 - Real.exp (-s * (MultiIndexSum (α : Fin n → ℕ) : ℝ)))
                    / s ^ ((3 : ℝ) / 2))‖ₑ)
                = ENNReal.ofReal (∫ s in Ioi (0 : ℝ),
                    ‖(((HermiteBasis n).repr v (α : Fin n → ℕ))
                      * ((HermiteBasis n).repr w (α : Fin n → ℕ)))
                      * ((1 - Real.exp (-s * (MultiIndexSum (α : Fin n → ℕ) : ℝ)))
                        / s ^ ((3 : ℝ) / 2))‖) :=
            fun α => (ofReal_integral_norm_eq_lintegral_enorm (hFint α)).symm
          rw [tsum_congr hre]
          exact lt_top_iff_ne_top.mpr hF_sum.tsum_ofReal_ne_top
  refine ⟨hIint, ?_⟩
  -- (8) conjunct 2: Fubini, then `ScalarFractional` term by term
  have hvalue : (∫ s in Ioi (0 : ℝ),
      (inner ℝ (v - OUSemigroup s v) w : ℝ) / s ^ ((3 : ℝ) / 2))
      = ∑' α : {α : Fin n → ℕ // α ≠ 0}, ∫ s in Ioi (0 : ℝ),
          (((HermiteBasis n).repr v (α : Fin n → ℕ))
            * ((HermiteBasis n).repr w (α : Fin n → ℕ)))
            * ((1 - Real.exp (-s * (MultiIndexSum (α : Fin n → ℕ) : ℝ)))
              / s ^ ((3 : ℝ) / 2)) := by
    rw [integral_tsum_of_summable_integral_norm hFint hF_sum]
    refine setIntegral_congr_ae measurableSet_Ioi ?_
    filter_upwards with s hs
    exact hsplit s hs
  rw [hvalue, tsum_congr hFval]
  have hfin : (∑' α : {α : Fin n → ℕ // α ≠ 0},
      (((HermiteBasis n).repr v (α : Fin n → ℕ))
        * ((HermiteBasis n).repr w (α : Fin n → ℕ)))
        * (2 * Real.sqrt Real.pi * Real.sqrt (MultiIndexSum (α : Fin n → ℕ) : ℝ)))
      = (2 * Real.sqrt Real.pi) * EnergyBil v w := by
    rw [EnergyBil, ← tsum_mul_left]
    refine tsum_congr fun α => ?_
    rw [← Real.sqrt_eq_rpow]
    ring
  rw [hfin]
  have hpi : (0 : ℝ) < 2 * Real.sqrt Real.pi := by positivity
  rw [← mul_assoc, one_div, inv_mul_cancel₀ hpi.ne', one_mul]
