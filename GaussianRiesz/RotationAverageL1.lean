import GaussianRiesz.ToL1
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import GaussianRiesz.GaussIsProb
open MeasureTheory
theorem RotationAverageL1 {n : ℕ} (v : Lp ℂ 2 (GaussMeasure n)) :
    IntervalIntegrable
        (fun θ : ℝ =>
          ‖ToL1 (Complex.reCLM.compLp (Complex.exp ((θ : ℂ) * Complex.I) • v))‖
            + ‖ToL1 (Complex.imCLM.compLp (Complex.exp ((θ : ℂ) * Complex.I) • v))‖)
        MeasureTheory.volume 0 (2 * Real.pi)
      ∧ (1 / (2 * Real.pi)) *
          (∫ θ in (0:ℝ)..(2 * Real.pi),
            (‖ToL1 (Complex.reCLM.compLp (Complex.exp ((θ : ℂ) * Complex.I) • v))‖
              + ‖ToL1 (Complex.imCLM.compLp (Complex.exp ((θ : ℂ) * Complex.I) • v))‖))
        = (4 / Real.pi) * ∫ x, ‖(v : EuclideanSpace ℝ (Fin n) → ℂ) x‖ ∂(GaussMeasure n) := by
  classical
  -- STEP 1 of the `.tex`: the integral of `|cos|` over a period
  have cosabs : ∫ θ in (0:ℝ)..(2 * Real.pi), |Real.cos θ| = 4 := by
    have hpi := Real.pi_pos
    have h1 : ∫ θ in (0:ℝ)..(Real.pi/2), |Real.cos θ| = 1 := by
      rw [intervalIntegral.integral_congr (g := Real.cos) ?_, integral_cos]
      · simp
      · intro θ hθ
        rw [Set.uIcc_of_le (by positivity)] at hθ
        exact abs_of_nonneg (Real.cos_nonneg_of_mem_Icc ⟨by linarith [hθ.1], hθ.2⟩)
    have h2 : ∫ θ in (Real.pi/2)..(3 * Real.pi/2), |Real.cos θ| = 2 := by
      rw [intervalIntegral.integral_congr (g := fun θ => -Real.cos θ) ?_,
        intervalIntegral.integral_neg, integral_cos]
      · rw [show (3:ℝ) * Real.pi/2 = Real.pi + Real.pi/2 from by ring]
        rw [Real.sin_add_pi_div_two]
        simp [Real.cos_pi, Real.sin_pi_div_two]
        ring
      · intro θ hθ
        rw [Set.uIcc_of_le (by linarith)] at hθ
        refine abs_of_nonpos (Real.cos_nonpos_of_pi_div_two_le_of_le hθ.1 ?_)
        linarith [hθ.2]
    have h3 : ∫ θ in (3 * Real.pi/2)..(2 * Real.pi), |Real.cos θ| = 1 := by
      rw [intervalIntegral.integral_congr (g := Real.cos) ?_, integral_cos]
      · rw [show (3:ℝ) * Real.pi/2 = 2 * Real.pi - Real.pi/2 from by ring]
        simp [Real.sin_two_pi, Real.sin_sub, Real.sin_two_pi, Real.cos_two_pi]
      · intro θ hθ
        rw [Set.uIcc_of_le (by linarith)] at hθ
        have hshift : Real.cos θ = Real.cos (θ - 2 * Real.pi) := by
          rw [Real.cos_sub_two_pi]
        have hmem : θ - 2 * Real.pi ∈ Set.Icc (-(Real.pi/2)) (Real.pi/2) :=
          ⟨by linarith [hθ.1], by linarith [hθ.2]⟩
        show |Real.cos θ| = Real.cos θ
        rw [hshift]
        exact abs_of_nonneg (Real.cos_nonneg_of_mem_Icc hmem)
    have e1 : (∫ θ in (0:ℝ)..(Real.pi/2), |Real.cos θ|)
        + ∫ θ in (Real.pi/2)..(3 * Real.pi/2), |Real.cos θ|
        = ∫ θ in (0:ℝ)..(3 * Real.pi/2), |Real.cos θ| :=
      intervalIntegral.integral_add_adjacent_intervals
        ((continuous_abs.comp Real.continuous_cos).intervalIntegrable _ _)
        ((continuous_abs.comp Real.continuous_cos).intervalIntegrable _ _)
    have e2 : (∫ θ in (0:ℝ)..(3 * Real.pi/2), |Real.cos θ|)
        + ∫ θ in (3 * Real.pi/2)..(2 * Real.pi), |Real.cos θ|
        = ∫ θ in (0:ℝ)..(2 * Real.pi), |Real.cos θ| :=
      intervalIntegral.integral_add_adjacent_intervals
        ((continuous_abs.comp Real.continuous_cos).intervalIntegrable _ _)
        ((continuous_abs.comp Real.continuous_cos).intervalIntegrable _ _)
    rw [← e2, ← e1, h1, h2, h3]
    norm_num

  -- STEP 2: the phase-shifted versions
  -- STEP 2: the same after a phase shift
  have cosshift : ∀ p : ℝ, ∫ θ in (0:ℝ)..(2 * Real.pi), |Real.cos (θ + p)| = 4 := by
    intro p
    have hper : Function.Periodic (fun θ : ℝ => |Real.cos θ|) (2 * Real.pi) := by
      intro θ; simp [Real.cos_add_two_pi]
    rw [intervalIntegral.integral_comp_add_right (fun θ => |Real.cos θ|) p, zero_add,
      show 2 * Real.pi + p = p + 2 * Real.pi from by ring,
      hper.intervalIntegral_add_eq p 0, zero_add]
    exact cosabs
  have sinshift : ∀ p : ℝ, ∫ θ in (0:ℝ)..(2 * Real.pi), |Real.sin (θ + p)| = 4 := by
    intro p
    have h : ∀ θ : ℝ, |Real.sin (θ + p)| = |Real.cos (θ + (p - Real.pi/2))| := by
      intro θ
      rw [show θ + (p - Real.pi/2) = (θ + p) - Real.pi/2 from by ring, Real.cos_sub_pi_div_two]
    rw [intervalIntegral.integral_congr (g := fun θ => |Real.cos (θ + (p - Real.pi/2))|)
      (fun θ _ => h θ)]
    exact cosshift _


  -- the pointwise rotation identity (Step 3), standalone
  -- STEP 3: the pointwise rotation identity
  have hptid : ∀ z : ℂ, ∫ θ in (0:ℝ)..(2 * Real.pi),
      (|(Complex.exp ((θ:ℂ) * Complex.I) * z).re|
        + |(Complex.exp ((θ:ℂ) * Complex.I) * z).im|) = 8 * ‖z‖ := by
    intro z
    obtain ⟨φ, hφ⟩ : ∃ φ : ℝ, ((‖z‖ : ℝ) : ℂ) * Complex.exp ((φ:ℂ) * Complex.I) = z :=
      ⟨Complex.arg z, Complex.norm_mul_exp_arg_mul_I z⟩
    have hadd : ∀ θ : ℝ, Complex.exp ((θ:ℂ) * Complex.I) * Complex.exp ((φ:ℂ) * Complex.I)
        = Complex.exp (((θ + φ : ℝ) : ℂ) * Complex.I) := by
      intro θ
      rw [← Complex.exp_add, Complex.ofReal_add]
      ring_nf
    have hkey : ∀ θ : ℝ, Complex.exp ((θ:ℂ) * Complex.I) * z
        = ((‖z‖ : ℝ) : ℂ) * Complex.exp (((θ + φ : ℝ) : ℂ) * Complex.I) := by
      intro θ
      calc Complex.exp ((θ:ℂ) * Complex.I) * z
          = Complex.exp ((θ:ℂ) * Complex.I)
              * (((‖z‖ : ℝ) : ℂ) * Complex.exp ((φ:ℂ) * Complex.I)) := by rw [hφ]
        _ = ((‖z‖ : ℝ) : ℂ)
              * (Complex.exp ((θ:ℂ) * Complex.I) * Complex.exp ((φ:ℂ) * Complex.I)) := by ring
        _ = _ := by rw [hadd]
    have hint : ∀ θ : ℝ,
        |(Complex.exp ((θ:ℂ) * Complex.I) * z).re| + |(Complex.exp ((θ:ℂ) * Complex.I) * z).im|
          = ‖z‖ * |Real.cos (θ + φ)| + ‖z‖ * |Real.sin (θ + φ)| := by
      intro θ
      rw [hkey θ, Complex.re_ofReal_mul, Complex.im_ofReal_mul,
        Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im,
        abs_mul, abs_mul, abs_of_nonneg (norm_nonneg z)]
    rw [intervalIntegral.integral_congr
      (g := fun θ => ‖z‖ * |Real.cos (θ + φ)| + ‖z‖ * |Real.sin (θ + φ)|) (fun θ _ => hint θ)]
    have ic : IntervalIntegrable (fun θ : ℝ => ‖z‖ * |Real.cos (θ + φ)|) volume 0 (2 * Real.pi) :=
      (((continuous_abs.comp (Real.continuous_cos.comp (continuous_id.add
        continuous_const))).const_smul ‖z‖)).intervalIntegrable _ _
    have is : IntervalIntegrable (fun θ : ℝ => ‖z‖ * |Real.sin (θ + φ)|) volume 0 (2 * Real.pi) :=
      (((continuous_abs.comp (Real.continuous_sin.comp (continuous_id.add
        continuous_const))).const_smul ‖z‖)).intervalIntegrable _ _
    rw [intervalIntegral.integral_add ic is, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul, cosshift φ, sinshift φ]
    ring
  classical
  -- `v` is in `L¹(γ)` as well, γ being a probability measure
  have hv1 : Integrable (v : EuclideanSpace ℝ (Fin n) → ℂ) (GaussMeasure n) :=
    memLp_one_iff_integrable.1 ((Lp.memLp v).mono_exponent (by norm_num))
  have hvmeas : Measurable (v : EuclideanSpace ℝ (Fin n) → ℂ) :=
    (AEEqFun.stronglyMeasurable
      (v : EuclideanSpace ℝ (Fin n) →ₘ[GaussMeasure n] ℂ)).measurable
  -- the `ToL1` norm is the integral of the absolute value
  have htoL1 : ∀ u : Lp ℝ 2 (GaussMeasure n),
      ‖ToL1 u‖ = ∫ x, ‖(u : EuclideanSpace ℝ (Fin n) → ℝ) x‖ ∂(GaussMeasure n) := by
    intro u
    rw [L1.norm_eq_integral_norm]
    refine integral_congr_ae ?_
    rw [ToL1]
    filter_upwards [MemLp.coeFn_toLp (p := 1) ((Lp.memLp u).mono_exponent (by norm_num))]
      with x hx
    rw [hx]
  -- STEP 6: the inner integral is the integrand of the statement
  have hS : ∀ θ : ℝ,
      ‖ToL1 (Complex.reCLM.compLp (Complex.exp ((θ : ℂ) * Complex.I) • v))‖
          + ‖ToL1 (Complex.imCLM.compLp (Complex.exp ((θ : ℂ) * Complex.I) • v))‖
        = ∫ x, (|(Complex.exp ((θ:ℂ) * Complex.I)
                * (v : EuclideanSpace ℝ (Fin n) → ℂ) x).re|
              + |(Complex.exp ((θ:ℂ) * Complex.I)
                * (v : EuclideanSpace ℝ (Fin n) → ℂ) x).im|) ∂(GaussMeasure n) := by
    intro θ
    have hcv : Integrable (fun x => Complex.exp ((θ:ℂ) * Complex.I)
        * (v : EuclideanSpace ℝ (Fin n) → ℂ) x) (GaussMeasure n) :=
      hv1.const_mul _
    have hre : (fun x => ‖(Complex.reCLM.compLp (Complex.exp ((θ : ℂ) * Complex.I) • v)
          : EuclideanSpace ℝ (Fin n) → ℝ) x‖)
        =ᵐ[GaussMeasure n] fun x => |(Complex.exp ((θ:ℂ) * Complex.I)
          * (v : EuclideanSpace ℝ (Fin n) → ℂ) x).re| := by
      filter_upwards [ContinuousLinearMap.coeFn_compLp' Complex.reCLM
          (Complex.exp ((θ : ℂ) * Complex.I) • v),
        Lp.coeFn_smul (Complex.exp ((θ : ℂ) * Complex.I)) v] with x e1 e2
      show ‖(Complex.reCLM.compLp (Complex.exp ((θ : ℂ) * Complex.I) • v)
        : EuclideanSpace ℝ (Fin n) → ℝ) x‖ = _
      rw [e1]
      show ‖Complex.reCLM ((Complex.exp ((θ : ℂ) * Complex.I) • v
        : Lp ℂ 2 (GaussMeasure n)) x)‖ = _
      rw [e2]
      simp [Real.norm_eq_abs]
    have him : (fun x => ‖(Complex.imCLM.compLp (Complex.exp ((θ : ℂ) * Complex.I) • v)
          : EuclideanSpace ℝ (Fin n) → ℝ) x‖)
        =ᵐ[GaussMeasure n] fun x => |(Complex.exp ((θ:ℂ) * Complex.I)
          * (v : EuclideanSpace ℝ (Fin n) → ℂ) x).im| := by
      filter_upwards [ContinuousLinearMap.coeFn_compLp' Complex.imCLM
          (Complex.exp ((θ : ℂ) * Complex.I) • v),
        Lp.coeFn_smul (Complex.exp ((θ : ℂ) * Complex.I)) v] with x e1 e2
      show ‖(Complex.imCLM.compLp (Complex.exp ((θ : ℂ) * Complex.I) • v)
        : EuclideanSpace ℝ (Fin n) → ℝ) x‖ = _
      rw [e1]
      show ‖Complex.imCLM ((Complex.exp ((θ : ℂ) * Complex.I) • v
        : Lp ℂ 2 (GaussMeasure n)) x)‖ = _
      rw [e2]
      simp [Real.norm_eq_abs]
    have hreint : Integrable (fun x => |(Complex.exp ((θ:ℂ) * Complex.I)
        * (v : EuclideanSpace ℝ (Fin n) → ℂ) x).re|) (GaussMeasure n) :=
      hcv.re.abs.congr (Filter.Eventually.of_forall fun x => rfl)
    have himint : Integrable (fun x => |(Complex.exp ((θ:ℂ) * Complex.I)
        * (v : EuclideanSpace ℝ (Fin n) → ℂ) x).im|) (GaussMeasure n) :=
      hcv.im.abs.congr (Filter.Eventually.of_forall fun x => rfl)
    rw [htoL1, htoL1, integral_congr_ae hre, integral_congr_ae him,
      ← integral_add hreint himint]
  -- STEP 4: joint measurability, uncurried
  have hprod : Measurable (fun p : ℝ × EuclideanSpace ℝ (Fin n) =>
      Complex.exp ((p.1 : ℂ) * Complex.I)
        * (v : EuclideanSpace ℝ (Fin n) → ℂ) p.2) := by
    refine Measurable.mul ?_ (hvmeas.comp measurable_snd)
    exact Complex.measurable_exp.comp (by fun_prop)
  have hGmeas : Measurable (fun p : ℝ × EuclideanSpace ℝ (Fin n) => ENNReal.ofReal
      (|(Complex.exp ((p.1 : ℂ) * Complex.I)
            * (v : EuclideanSpace ℝ (Fin n) → ℂ) p.2).re|
        + |(Complex.exp ((p.1 : ℂ) * Complex.I)
            * (v : EuclideanSpace ℝ (Fin n) → ℂ) p.2).im|)) :=
    ENNReal.measurable_ofReal.comp
      (Measurable.add (continuous_abs.measurable.comp (Complex.measurable_re.comp hprod))
        (continuous_abs.measurable.comp (Complex.measurable_im.comp hprod)))
  -- the two one-variable integrabilities
  have hcont : ∀ x : EuclideanSpace ℝ (Fin n), Continuous (fun θ : ℝ =>
      |(Complex.exp ((θ:ℂ) * Complex.I)
          * (v : EuclideanSpace ℝ (Fin n) → ℂ) x).re|
        + |(Complex.exp ((θ:ℂ) * Complex.I)
            * (v : EuclideanSpace ℝ (Fin n) → ℂ) x).im|) := by
    intro x; fun_prop
  have hnn : ∀ (θ : ℝ) (x : EuclideanSpace ℝ (Fin n)), (0:ℝ) ≤
      |(Complex.exp ((θ:ℂ) * Complex.I)
          * (v : EuclideanSpace ℝ (Fin n) → ℂ) x).re|
        + |(Complex.exp ((θ:ℂ) * Complex.I)
            * (v : EuclideanSpace ℝ (Fin n) → ℂ) x).im| := fun θ x => by positivity
  -- the inner `x`-integral, as an `ℝ≥0∞` identity
  have hinner : ∀ θ : ℝ, (∫⁻ x, ENNReal.ofReal
        (|(Complex.exp ((θ:ℂ) * Complex.I)
            * (v : EuclideanSpace ℝ (Fin n) → ℂ) x).re|
          + |(Complex.exp ((θ:ℂ) * Complex.I)
              * (v : EuclideanSpace ℝ (Fin n) → ℂ) x).im|) ∂(GaussMeasure n))
      = ENNReal.ofReal
          (‖ToL1 (Complex.reCLM.compLp (Complex.exp ((θ : ℂ) * Complex.I) • v))‖
            + ‖ToL1 (Complex.imCLM.compLp (Complex.exp ((θ : ℂ) * Complex.I) • v))‖) := by
    intro θ
    have hcv : Integrable (fun x => Complex.exp ((θ:ℂ) * Complex.I)
        * (v : EuclideanSpace ℝ (Fin n) → ℂ) x) (GaussMeasure n) := hv1.const_mul _
    have hint : Integrable (fun x =>
        |(Complex.exp ((θ:ℂ) * Complex.I)
            * (v : EuclideanSpace ℝ (Fin n) → ℂ) x).re|
          + |(Complex.exp ((θ:ℂ) * Complex.I)
              * (v : EuclideanSpace ℝ (Fin n) → ℂ) x).im|) (GaussMeasure n) :=
      (hcv.re.abs.congr (Filter.Eventually.of_forall fun x => rfl)).add
        (hcv.im.abs.congr (Filter.Eventually.of_forall fun x => rfl))
    rw [hS θ, ofReal_integral_eq_lintegral_ofReal hint
      (Filter.Eventually.of_forall fun x => hnn θ x)]
  -- the inner `θ`-integral, by the pointwise rotation identity
  have houter : ∀ x : EuclideanSpace ℝ (Fin n),
      (∫⁻ θ in Set.Ioc (0:ℝ) (2 * Real.pi), ENNReal.ofReal
        (|(Complex.exp ((θ:ℂ) * Complex.I)
            * (v : EuclideanSpace ℝ (Fin n) → ℂ) x).re|
          + |(Complex.exp ((θ:ℂ) * Complex.I)
              * (v : EuclideanSpace ℝ (Fin n) → ℂ) x).im|))
      = ENNReal.ofReal (8 * ‖(v : EuclideanSpace ℝ (Fin n) → ℂ) x‖) := by
    intro x
    have hio : IntegrableOn (fun θ : ℝ =>
        |(Complex.exp ((θ:ℂ) * Complex.I)
            * (v : EuclideanSpace ℝ (Fin n) → ℂ) x).re|
          + |(Complex.exp ((θ:ℂ) * Complex.I)
              * (v : EuclideanSpace ℝ (Fin n) → ℂ) x).im|)
        (Set.Ioc (0:ℝ) (2 * Real.pi)) volume :=
      ((hcont x).integrableOn_Icc).mono_set Set.Ioc_subset_Icc_self
    rw [← ofReal_integral_eq_lintegral_ofReal hio
      (ae_restrict_of_forall_mem measurableSet_Ioc fun θ _ => hnn θ x),
      ← intervalIntegral.integral_of_le (by positivity), hptid]
  -- STEP 5: Tonelli, and the key identity
  have h8int : Integrable (fun x => 8 * ‖(v : EuclideanSpace ℝ (Fin n) → ℂ) x‖)
      (GaussMeasure n) := hv1.norm.const_mul 8
  have hkey : (∫⁻ θ in Set.Ioc (0:ℝ) (2 * Real.pi), ENNReal.ofReal
        (‖ToL1 (Complex.reCLM.compLp (Complex.exp ((θ : ℂ) * Complex.I) • v))‖
          + ‖ToL1 (Complex.imCLM.compLp (Complex.exp ((θ : ℂ) * Complex.I) • v))‖))
      = ENNReal.ofReal (8 * ∫ x, ‖(v : EuclideanSpace ℝ (Fin n) → ℂ) x‖
          ∂(GaussMeasure n)) := by
    calc (∫⁻ θ in Set.Ioc (0:ℝ) (2 * Real.pi), ENNReal.ofReal
          (‖ToL1 (Complex.reCLM.compLp (Complex.exp ((θ : ℂ) * Complex.I) • v))‖
            + ‖ToL1 (Complex.imCLM.compLp (Complex.exp ((θ : ℂ) * Complex.I) • v))‖))
        = ∫⁻ θ in Set.Ioc (0:ℝ) (2 * Real.pi), (∫⁻ x, ENNReal.ofReal
            (|(Complex.exp ((θ:ℂ) * Complex.I)
                * (v : EuclideanSpace ℝ (Fin n) → ℂ) x).re|
              + |(Complex.exp ((θ:ℂ) * Complex.I)
                  * (v : EuclideanSpace ℝ (Fin n) → ℂ) x).im|) ∂(GaussMeasure n)) :=
          lintegral_congr fun θ => (hinner θ).symm
      _ = ∫⁻ x, (∫⁻ θ in Set.Ioc (0:ℝ) (2 * Real.pi), ENNReal.ofReal
            (|(Complex.exp ((θ:ℂ) * Complex.I)
                * (v : EuclideanSpace ℝ (Fin n) → ℂ) x).re|
              + |(Complex.exp ((θ:ℂ) * Complex.I)
                  * (v : EuclideanSpace ℝ (Fin n) → ℂ) x).im|)) ∂(GaussMeasure n) :=
          lintegral_lintegral_swap hGmeas.aemeasurable
      _ = ∫⁻ x, ENNReal.ofReal (8 * ‖(v : EuclideanSpace ℝ (Fin n) → ℂ) x‖)
            ∂(GaussMeasure n) := lintegral_congr houter
      _ = ENNReal.ofReal (8 * ∫ x, ‖(v : EuclideanSpace ℝ (Fin n) → ℂ) x‖
            ∂(GaussMeasure n)) := by
          rw [← ofReal_integral_eq_lintegral_ofReal h8int
            (Filter.Eventually.of_forall fun x => by positivity), integral_const_mul]
  -- STEP 7: clause (1) then clause (2)
  have hSnn : ∀ θ : ℝ, (0:ℝ) ≤
      ‖ToL1 (Complex.reCLM.compLp (Complex.exp ((θ : ℂ) * Complex.I) • v))‖
        + ‖ToL1 (Complex.imCLM.compLp (Complex.exp ((θ : ℂ) * Complex.I) • v))‖ :=
    fun θ => by positivity
  have hSm : Measurable (fun θ : ℝ =>
      ‖ToL1 (Complex.reCLM.compLp (Complex.exp ((θ : ℂ) * Complex.I) • v))‖
        + ‖ToL1 (Complex.imCLM.compLp (Complex.exp ((θ : ℂ) * Complex.I) • v))‖) := by
    have heq : (fun θ : ℝ =>
        ‖ToL1 (Complex.reCLM.compLp (Complex.exp ((θ : ℂ) * Complex.I) • v))‖
          + ‖ToL1 (Complex.imCLM.compLp (Complex.exp ((θ : ℂ) * Complex.I) • v))‖)
        = fun θ : ℝ => (∫⁻ x, ENNReal.ofReal
            (|(Complex.exp ((θ:ℂ) * Complex.I)
                * (v : EuclideanSpace ℝ (Fin n) → ℂ) x).re|
              + |(Complex.exp ((θ:ℂ) * Complex.I)
                  * (v : EuclideanSpace ℝ (Fin n) → ℂ) x).im|)
            ∂(GaussMeasure n)).toReal := by
      funext θ
      rw [hinner θ, ENNReal.toReal_ofReal (hSnn θ)]
    rw [heq]
    exact Measurable.ennreal_toReal
      (Measurable.lintegral_prod_right' (ν := GaussMeasure n) hGmeas)
  have hio : IntegrableOn (fun θ : ℝ =>
      ‖ToL1 (Complex.reCLM.compLp (Complex.exp ((θ : ℂ) * Complex.I) • v))‖
        + ‖ToL1 (Complex.imCLM.compLp (Complex.exp ((θ : ℂ) * Complex.I) • v))‖)
      (Set.Ioc (0:ℝ) (2 * Real.pi)) volume := by
    refine ⟨hSm.aestronglyMeasurable.restrict, ?_⟩
    rw [HasFiniteIntegral]
    have : (∫⁻ θ in Set.Ioc (0:ℝ) (2 * Real.pi), ‖(fun θ : ℝ =>
        ‖ToL1 (Complex.reCLM.compLp (Complex.exp ((θ : ℂ) * Complex.I) • v))‖
          + ‖ToL1 (Complex.imCLM.compLp (Complex.exp ((θ : ℂ) * Complex.I) • v))‖) θ‖ₑ)
        = ENNReal.ofReal (8 * ∫ x, ‖(v : EuclideanSpace ℝ (Fin n) → ℂ) x‖
            ∂(GaussMeasure n)) := by
      rw [← hkey]
      refine lintegral_congr fun θ => ?_
      rw [Real.enorm_eq_ofReal_abs, abs_of_nonneg (hSnn θ)]
    rw [this]
    exact ENNReal.ofReal_lt_top
  refine ⟨(intervalIntegrable_iff_integrableOn_Ioc_of_le (by positivity)).2 hio, ?_⟩
  have hval : (∫ θ in Set.Ioc (0:ℝ) (2 * Real.pi),
      (‖ToL1 (Complex.reCLM.compLp (Complex.exp ((θ : ℂ) * Complex.I) • v))‖
        + ‖ToL1 (Complex.imCLM.compLp (Complex.exp ((θ : ℂ) * Complex.I) • v))‖))
      = 8 * ∫ x, ‖(v : EuclideanSpace ℝ (Fin n) → ℂ) x‖ ∂(GaussMeasure n) := by
    refine (ENNReal.ofReal_eq_ofReal_iff (by
      exact integral_nonneg_of_ae (ae_restrict_of_forall_mem measurableSet_Ioc
        fun θ _ => hSnn θ)) (by positivity)).1 ?_
    rw [← hkey, ofReal_integral_eq_lintegral_ofReal hio
      (ae_restrict_of_forall_mem measurableSet_Ioc fun θ _ => hSnn θ)]
  rw [intervalIntegral.integral_of_le (by positivity), hval]
  field_simp
  ring
