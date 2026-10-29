module

public import GaussianRiesz.ComplexTransformedLocalization
public import GaussianRiesz.ComplexRieszL2Identity
public import GaussianRiesz.ComplexRieszTransformLinear
public import GaussianRiesz.RotationAverageL1
public import GaussianRiesz.SignedDecomposition
public import GaussianRiesz.RieszL2Identity
public import GaussianRiesz.GaussIsProb

@[expose] public section
open MeasureTheory
theorem ComplexMainBound {n : ℕ} (v : Lp ℂ 2 (GaussMeasure n)) (t : ℝ) (ht : 0 < t) :
    ENNReal.ofReal t * GaussMeasure n
        {x | t < ‖(ComplexRieszTransform v :
            EuclideanSpace ℝ (Fin n) → EuclideanSpace ℂ (Fin n)) x‖}
      ≤ ENNReal.ofReal ((8 / Real.pi) *
          ∫ x, ‖(v : EuclideanSpace ℝ (Fin n) → ℂ) x‖ ∂(GaussMeasure n)) := by
  classical
  have hpi := Real.pi_pos
  have hpi8 : Real.pi < 8 := by linarith [Real.pi_le_four]
  have h8p : (1:ℝ) ≤ 8 / Real.pi := by rw [le_div_iff₀ hpi]; linarith
  -- `L¹` facts about `v`, and `M`
  have hv1 : Integrable (v : EuclideanSpace ℝ (Fin n) → ℂ) (GaussMeasure n) :=
    memLp_one_iff_integrable.1 ((Lp.memLp v).mono_exponent (by norm_num))
  have hM0 : (0:ℝ) ≤ ∫ x, ‖(v : EuclideanSpace ℝ (Fin n) → ℂ) x‖ ∂(GaussMeasure n) :=
    integral_nonneg fun x => norm_nonneg _
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
  have hL1int : ∀ u : Lp ℝ 2 (GaussMeasure n),
      Integrable (fun x => ‖(u : EuclideanSpace ℝ (Fin n) → ℝ) x‖) (GaussMeasure n) :=
    fun u => (memLp_one_iff_integrable.1 ((Lp.memLp u).mono_exponent (by norm_num))).norm
  -- the `L²` norm squared, as an integral, for the Chebyshev step
  have hsq : ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      (W : Lp E 2 (GaussMeasure n)),
      ‖W‖ ^ 2 = ∫ x, ‖(W : EuclideanSpace ℝ (Fin n) → E) x‖ ^ 2 ∂(GaussMeasure n) := by
    intro E _ _ W
    rw [← real_inner_self_eq_norm_sq, L2.inner_def (𝕜 := ℝ)]
    simp
  have hsqint : ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      (W : Lp E 2 (GaussMeasure n)),
      Integrable (fun x => ‖(W : EuclideanSpace ℝ (Fin n) → E) x‖ ^ 2) (GaussMeasure n) := by
    intro E _ _ W
    simpa [real_inner_self_eq_norm_sq] using L2.integrable_inner (𝕜 := ℝ) W W
  -- STEP 2.6, isolated: Chebyshev for an `Lp _ 2` element
  have hcheb : ∀ W : Lp (EuclideanSpace ℂ (Fin n)) 2 (GaussMeasure n),
      ENNReal.ofReal (t ^ 2) * GaussMeasure n
          {x | t < ‖(W : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℂ (Fin n)) x‖}
        ≤ ENNReal.ofReal (‖W‖ ^ 2) := by
    intro W
    have hlin : ENNReal.ofReal (‖W‖ ^ 2)
        = ∫⁻ x, ‖(W : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℂ (Fin n)) x‖ₑ ^ 2
          ∂(GaussMeasure n) := by
      rw [hsq _ W, ofReal_integral_eq_lintegral_ofReal (hsqint _ W)
        (Filter.Eventually.of_forall fun x => by positivity)]
      refine lintegral_congr fun x => ?_
      rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]
    have hae : AEMeasurable (fun x =>
        ‖(W : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℂ (Fin n)) x‖ₑ ^ 2)
        (GaussMeasure n) := ((Lp.aestronglyMeasurable W).enorm.pow_const 2)
    have hsub : {x : EuclideanSpace ℝ (Fin n) |
          t < ‖(W : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℂ (Fin n)) x‖}
        ⊆ {x : EuclideanSpace ℝ (Fin n) | ENNReal.ofReal (t ^ 2)
            ≤ ‖(W : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℂ (Fin n)) x‖ₑ ^ 2} := by
      intro x hx
      rw [Set.mem_ofPred_eq, ENNReal.ofReal_pow ht.le, ← ofReal_norm,
        pow_two, pow_two]
      have h1 : ENNReal.ofReal t
          ≤ ENNReal.ofReal ‖(W : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℂ (Fin n)) x‖ :=
        ENNReal.ofReal_le_ofReal hx.le
      exact mul_le_mul' h1 h1
    rw [hlin]
    exact le_trans (mul_le_mul' le_rfl (measure_mono hsub))
      (mul_meas_ge_le_lintegral₀ hae (ENNReal.ofReal (t ^ 2)))
  -- reduce the `ℝ≥0∞` goal to a real inequality
  have hEtop : GaussMeasure n {x : EuclideanSpace ℝ (Fin n) |
      t < ‖(ComplexRieszTransform v :
        EuclideanSpace ℝ (Fin n) → EuclideanSpace ℂ (Fin n)) x‖} ≠ ⊤ := measure_ne_top _ _
  rw [show ENNReal.ofReal t * GaussMeasure n {x : EuclideanSpace ℝ (Fin n) |
        t < ‖(ComplexRieszTransform v :
          EuclideanSpace ℝ (Fin n) → EuclideanSpace ℂ (Fin n)) x‖}
      = ENNReal.ofReal (t * (GaussMeasure n {x : EuclideanSpace ℝ (Fin n) |
          t < ‖(ComplexRieszTransform v :
            EuclideanSpace ℝ (Fin n) → EuclideanSpace ℂ (Fin n)) x‖}).toReal) from by
    rw [ENNReal.ofReal_mul ht.le, ENNReal.ofReal_toReal hEtop]]
  refine ENNReal.ofReal_le_ofReal ?_
  -- STEP 0 and CASE 1
  have hle1 : (GaussMeasure n {x : EuclideanSpace ℝ (Fin n) |
      t < ‖(ComplexRieszTransform v :
        EuclideanSpace ℝ (Fin n) → EuclideanSpace ℂ (Fin n)) x‖}).toReal ≤ 1 := by
    rw [← ENNReal.toReal_one]
    exact ENNReal.toReal_mono ENNReal.one_ne_top (le_trans (measure_mono (Set.subset_univ _))
      (le_of_eq measure_univ))
  rcases le_or_gt t (∫ x, ‖(v : EuclideanSpace ℝ (Fin n) → ℂ) x‖ ∂(GaussMeasure n))
    with hcase | hcase
  · calc t * (GaussMeasure n {x : EuclideanSpace ℝ (Fin n) |
          t < ‖(ComplexRieszTransform v :
            EuclideanSpace ℝ (Fin n) → EuclideanSpace ℂ (Fin n)) x‖}).toReal
        ≤ t * 1 := by nlinarith [ENNReal.toReal_nonneg (a := GaussMeasure n
            {x : EuclideanSpace ℝ (Fin n) | t < ‖(ComplexRieszTransform v :
              EuclideanSpace ℝ (Fin n) → EuclideanSpace ℂ (Fin n)) x‖})]
      _ = t := mul_one t
      _ ≤ ∫ x, ‖(v : EuclideanSpace ℝ (Fin n) → ℂ) x‖ ∂(GaussMeasure n) := hcase
      _ ≤ (8 / Real.pi) * ∫ x, ‖(v : EuclideanSpace ℝ (Fin n) → ℂ) x‖ ∂(GaussMeasure n) :=
          le_mul_of_one_le_left hM0 h8p
  -- CASE 2: the per-rotation bound, Steps 2.1 through 2.8
  have hper : ∀ θ : ℝ, t * (GaussMeasure n {x : EuclideanSpace ℝ (Fin n) |
        t < ‖(ComplexRieszTransform v :
          EuclideanSpace ℝ (Fin n) → EuclideanSpace ℂ (Fin n)) x‖}).toReal
      ≤ 2 * (‖ToL1 (Complex.reCLM.compLp (Complex.exp ((θ : ℂ) * Complex.I) • v))‖
          + ‖ToL1 (Complex.imCLM.compLp (Complex.exp ((θ : ℂ) * Complex.I) • v))‖) := by
    intro θ
    have hcn : ‖Complex.exp ((θ : ℂ) * Complex.I)‖ = 1 := by
      simp [Complex.norm_exp_ofReal_mul_I]
    -- STEP 2.1
    have h21 : ∀ L : ℂ →L[ℝ] ℝ, (∀ z : ℂ, ‖L z‖ ≤ ‖z‖) →
        ‖ToL1 (L.compLp (Complex.exp ((θ : ℂ) * Complex.I) • v))‖
          ≤ ∫ x, ‖(v : EuclideanSpace ℝ (Fin n) → ℂ) x‖ ∂(GaussMeasure n) := by
      intro L hL
      rw [htoL1]
      refine integral_mono_ae (hL1int _) hv1.norm ?_
      filter_upwards [ContinuousLinearMap.coeFn_compLp' L
          (Complex.exp ((θ : ℂ) * Complex.I) • v),
        Lp.coeFn_smul (Complex.exp ((θ : ℂ) * Complex.I)) v] with x e1 e2
      show ‖(L.compLp (Complex.exp ((θ : ℂ) * Complex.I) • v)
        : EuclideanSpace ℝ (Fin n) → ℝ) x‖ ≤ _
      rw [e1]
      show ‖L ((Complex.exp ((θ : ℂ) * Complex.I) • v : Lp ℂ 2 (GaussMeasure n)) x)‖ ≤ _
      rw [e2]
      calc ‖L (Complex.exp ((θ : ℂ) * Complex.I) • (v : EuclideanSpace ℝ (Fin n) → ℂ) x)‖
          ≤ ‖Complex.exp ((θ : ℂ) * Complex.I) • (v : EuclideanSpace ℝ (Fin n) → ℂ) x‖ :=
            hL _
        _ = ‖(v : EuclideanSpace ℝ (Fin n) → ℂ) x‖ := by rw [norm_smul, hcn, one_mul]
    have h21re := h21 Complex.reCLM fun z => by
      simpa [Real.norm_eq_abs] using Complex.abs_re_le_norm z
    have h21im := h21 Complex.imCLM fun z => by
      simpa [Real.norm_eq_abs] using Complex.abs_im_le_norm z
    -- STEP 2.2: two signed decompositions
    obtain ⟨u₁, hu₁, g₁, Ω₁, hΩ₁m, hdec₁, hmeas₁, -, -, hL2₁, hloc₁⟩ :=
      SignedDecomposition (Complex.reCLM.compLp (Complex.exp ((θ : ℂ) * Complex.I) • v)) t
        (by linarith)
    obtain ⟨u₂, hu₂, g₂, Ω₂, hΩ₂m, hdec₂, hmeas₂, -, -, hL2₂, hloc₂⟩ :=
      SignedDecomposition (Complex.imCLM.compLp (Complex.exp ((θ : ℂ) * Complex.I) • v)) t
        (by linarith)
    -- STEP 2.3: the shared exceptional set
    have hlocΩ₁ : ∀ᵐ x ∂(GaussMeasure n), x ∉ Ω₁ ∪ Ω₂ →
        (GaussD u₁ : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) x = 0 := by
      filter_upwards [hloc₁] with x hx hmem
      exact hx fun h => hmem (Or.inl h)
    have hlocΩ₂ : ∀ᵐ x ∂(GaussMeasure n), x ∉ Ω₁ ∪ Ω₂ →
        (GaussD u₂ : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) x = 0 := by
      filter_upwards [hloc₂] with x hx hmem
      exact hx fun h => hmem (Or.inr h)
    have h23a : ENNReal.ofReal t * GaussMeasure n (Ω₁ ∪ Ω₂)
        ≤ ENNReal.ofReal (‖ToL1 (Complex.reCLM.compLp
              (Complex.exp ((θ : ℂ) * Complex.I) • v))‖
            + ‖ToL1 (Complex.imCLM.compLp (Complex.exp ((θ : ℂ) * Complex.I) • v))‖) := by
      calc ENNReal.ofReal t * GaussMeasure n (Ω₁ ∪ Ω₂)
          ≤ ENNReal.ofReal t * (GaussMeasure n Ω₁ + GaussMeasure n Ω₂) :=
            mul_le_mul' le_rfl (measure_union_le _ _)
        _ = ENNReal.ofReal t * GaussMeasure n Ω₁ + ENNReal.ofReal t * GaussMeasure n Ω₂ := by
            ring
        _ ≤ _ := by
            rw [ENNReal.ofReal_add (by positivity) (by positivity)]
            exact add_le_add hmeas₁ hmeas₂
    -- STEP 2.4: the complex good function
    obtain ⟨w, hw₁, hw₂⟩ : ∃ w : Lp ℂ 2 (GaussMeasure n),
        Complex.reCLM.compLp w = g₁ ∧ Complex.imCLM.compLp w = g₂ := by
      refine ⟨Complex.ofRealCLM.compLp g₁ + Complex.I • Complex.ofRealCLM.compLp g₂, ?_, ?_⟩
      · refine Lp.ext_iff.mpr ?_
        filter_upwards [ContinuousLinearMap.coeFn_compLp' Complex.reCLM
            (Complex.ofRealCLM.compLp g₁ + Complex.I • Complex.ofRealCLM.compLp g₂),
          Lp.coeFn_add (Complex.ofRealCLM.compLp g₁)
            (Complex.I • Complex.ofRealCLM.compLp g₂),
          Lp.coeFn_smul Complex.I (Complex.ofRealCLM.compLp g₂),
          ContinuousLinearMap.coeFn_compLp' Complex.ofRealCLM g₁,
          ContinuousLinearMap.coeFn_compLp' Complex.ofRealCLM g₂] with x e1 e2 e3 e4 e5
        rw [e1, e2, Pi.add_apply, e3, Pi.smul_apply, e4, e5]
        simp
      · refine Lp.ext_iff.mpr ?_
        filter_upwards [ContinuousLinearMap.coeFn_compLp' Complex.imCLM
            (Complex.ofRealCLM.compLp g₁ + Complex.I • Complex.ofRealCLM.compLp g₂),
          Lp.coeFn_add (Complex.ofRealCLM.compLp g₁)
            (Complex.I • Complex.ofRealCLM.compLp g₂),
          Lp.coeFn_smul Complex.I (Complex.ofRealCLM.compLp g₂),
          ContinuousLinearMap.coeFn_compLp' Complex.ofRealCLM g₁,
          ContinuousLinearMap.coeFn_compLp' Complex.ofRealCLM g₂] with x e1 e2 e3 e4 e5
        rw [e1, e2, Pi.add_apply, e3, Pi.smul_apply, e4, e5]
        simp
    -- STEP 2.5: localization
    obtain ⟨-, h25⟩ := ComplexTransformedLocalization
      (Complex.exp ((θ : ℂ) * Complex.I) • v) w g₁ g₂ u₁ u₂ hu₁ hu₂ hdec₁ hdec₂
      hw₁ hw₂ t (Ω₁ ∪ Ω₂) hlocΩ₁ hlocΩ₂
    -- STEP 2.6: Chebyshev on the good part
    have h26 : ENNReal.ofReal t * GaussMeasure n {x : EuclideanSpace ℝ (Fin n) |
          t < ‖(ComplexRieszTransform w :
            EuclideanSpace ℝ (Fin n) → EuclideanSpace ℂ (Fin n)) x‖}
        ≤ ENNReal.ofReal (‖ToL1 (Complex.reCLM.compLp
              (Complex.exp ((θ : ℂ) * Complex.I) • v))‖
            + ‖ToL1 (Complex.imCLM.compLp (Complex.exp ((θ : ℂ) * Complex.I) • v))‖) := by
      have hnorm : ‖ComplexRieszTransform w‖ ^ 2 ≤ t *
          (‖ToL1 (Complex.reCLM.compLp (Complex.exp ((θ : ℂ) * Complex.I) • v))‖
            + ‖ToL1 (Complex.imCLM.compLp (Complex.exp ((θ : ℂ) * Complex.I) • v))‖) := by
        have hid := (ComplexRieszL2Identity w).1
        rw [hw₁, hw₂] at hid
        have hr1 := (RieszL2Identity g₁).2
        have hr2 := (RieszL2Identity g₂).2
        have n1 := norm_nonneg (RieszTransform g₁)
        have n2 := norm_nonneg (RieszTransform g₂)
        nlinarith [hid, hr1, hr2, hL2₁, hL2₂, n1, n2, norm_nonneg g₁, norm_nonneg g₂]
      have hstep := hcheb (ComplexRieszTransform w)
      have hcancel : ENNReal.ofReal t * (ENNReal.ofReal t * GaussMeasure n
            {x : EuclideanSpace ℝ (Fin n) | t < ‖(ComplexRieszTransform w :
              EuclideanSpace ℝ (Fin n) → EuclideanSpace ℂ (Fin n)) x‖})
          ≤ ENNReal.ofReal t * ENNReal.ofReal
              (‖ToL1 (Complex.reCLM.compLp (Complex.exp ((θ : ℂ) * Complex.I) • v))‖
                + ‖ToL1 (Complex.imCLM.compLp
                    (Complex.exp ((θ : ℂ) * Complex.I) • v))‖) := by
        rw [← ENNReal.ofReal_mul ht.le, ← mul_assoc, ← ENNReal.ofReal_mul ht.le,
          show t * t = t ^ 2 from by ring]
        exact le_trans hstep (ENNReal.ofReal_le_ofReal hnorm)
      exact (ENNReal.mul_le_mul_iff_right
        (by simp [ENNReal.ofReal_eq_zero, not_le, ht]) ENNReal.ofReal_ne_top).1 hcancel
    -- STEPS 2.7 and 2.8
    have h28 : GaussMeasure n {x : EuclideanSpace ℝ (Fin n) |
          t < ‖(ComplexRieszTransform (Complex.exp ((θ : ℂ) * Complex.I) • v) :
            EuclideanSpace ℝ (Fin n) → EuclideanSpace ℂ (Fin n)) x‖}
        = GaussMeasure n {x : EuclideanSpace ℝ (Fin n) |
            t < ‖(ComplexRieszTransform v :
              EuclideanSpace ℝ (Fin n) → EuclideanSpace ℂ (Fin n)) x‖} := by
      refine measure_congr ?_
      filter_upwards [(ComplexRieszTransformLinear (n := n)).2.2
        (Complex.exp ((θ : ℂ) * Complex.I)) v hcn] with x hx
      exact congrArg (fun r : ℝ => t < r) hx
    have h27 : ENNReal.ofReal t * GaussMeasure n {x : EuclideanSpace ℝ (Fin n) |
          t < ‖(ComplexRieszTransform v :
            EuclideanSpace ℝ (Fin n) → EuclideanSpace ℂ (Fin n)) x‖}
        ≤ ENNReal.ofReal (2 *
            (‖ToL1 (Complex.reCLM.compLp (Complex.exp ((θ : ℂ) * Complex.I) • v))‖
              + ‖ToL1 (Complex.imCLM.compLp
                  (Complex.exp ((θ : ℂ) * Complex.I) • v))‖)) := by
      rw [← h28, show (2:ℝ) * (‖ToL1 (Complex.reCLM.compLp
            (Complex.exp ((θ : ℂ) * Complex.I) • v))‖
          + ‖ToL1 (Complex.imCLM.compLp (Complex.exp ((θ : ℂ) * Complex.I) • v))‖)
        = (‖ToL1 (Complex.reCLM.compLp (Complex.exp ((θ : ℂ) * Complex.I) • v))‖
            + ‖ToL1 (Complex.imCLM.compLp (Complex.exp ((θ : ℂ) * Complex.I) • v))‖)
          + (‖ToL1 (Complex.reCLM.compLp (Complex.exp ((θ : ℂ) * Complex.I) • v))‖
            + ‖ToL1 (Complex.imCLM.compLp
                (Complex.exp ((θ : ℂ) * Complex.I) • v))‖) from by ring,
        ENNReal.ofReal_add (by positivity) (by positivity)]
      calc ENNReal.ofReal t * GaussMeasure n {x : EuclideanSpace ℝ (Fin n) |
            t < ‖(ComplexRieszTransform (Complex.exp ((θ : ℂ) * Complex.I) • v) :
              EuclideanSpace ℝ (Fin n) → EuclideanSpace ℂ (Fin n)) x‖}
          ≤ ENNReal.ofReal t * (GaussMeasure n (Ω₁ ∪ Ω₂)
              + GaussMeasure n {x : EuclideanSpace ℝ (Fin n) |
                t < ‖(ComplexRieszTransform w :
                  EuclideanSpace ℝ (Fin n) → EuclideanSpace ℂ (Fin n)) x‖}) :=
            mul_le_mul' le_rfl h25
        _ = ENNReal.ofReal t * GaussMeasure n (Ω₁ ∪ Ω₂)
              + ENNReal.ofReal t * GaussMeasure n {x : EuclideanSpace ℝ (Fin n) |
                t < ‖(ComplexRieszTransform w :
                  EuclideanSpace ℝ (Fin n) → EuclideanSpace ℂ (Fin n)) x‖} := by ring
        _ ≤ _ := add_le_add h23a h26
    refine (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 ?_
    rw [ENNReal.ofReal_mul ht.le, ENNReal.ofReal_toReal hEtop]
    exact h27
  -- STEP 2.9: averaging over the rotation
  obtain ⟨hSint, hSval⟩ := RotationAverageL1 v
  have hmono := intervalIntegral.integral_mono (μ := volume)
    (f := fun _ : ℝ => t * (GaussMeasure n {x : EuclideanSpace ℝ (Fin n) |
      t < ‖(ComplexRieszTransform v :
        EuclideanSpace ℝ (Fin n) → EuclideanSpace ℂ (Fin n)) x‖}).toReal)
    (g := fun θ : ℝ => 2 *
      (‖ToL1 (Complex.reCLM.compLp (Complex.exp ((θ : ℂ) * Complex.I) • v))‖
        + ‖ToL1 (Complex.imCLM.compLp (Complex.exp ((θ : ℂ) * Complex.I) • v))‖))
    (by positivity) intervalIntegrable_const (hSint.const_mul 2) hper
  rw [intervalIntegral.integral_const, intervalIntegral.integral_const_mul,
    smul_eq_mul] at hmono
  have hI : (∫ θ in (0:ℝ)..(2 * Real.pi),
      (‖ToL1 (Complex.reCLM.compLp (Complex.exp ((θ : ℂ) * Complex.I) • v))‖
        + ‖ToL1 (Complex.imCLM.compLp (Complex.exp ((θ : ℂ) * Complex.I) • v))‖))
      = 8 * ∫ x, ‖(v : EuclideanSpace ℝ (Fin n) → ℂ) x‖ ∂(GaussMeasure n) := by
    have hpine : Real.pi ≠ 0 := ne_of_gt hpi
    have hstep : (1 / (2 * Real.pi)) *
        (∫ θ in (0:ℝ)..(2 * Real.pi),
          (‖ToL1 (Complex.reCLM.compLp (Complex.exp ((θ : ℂ) * Complex.I) • v))‖
            + ‖ToL1 (Complex.imCLM.compLp (Complex.exp ((θ : ℂ) * Complex.I) • v))‖))
          * (2 * Real.pi)
        = ((4 / Real.pi) * ∫ x, ‖(v : EuclideanSpace ℝ (Fin n) → ℂ) x‖ ∂(GaussMeasure n))
          * (2 * Real.pi) := by rw [hSval]
    have hl : (1 / (2 * Real.pi)) *
        (∫ θ in (0:ℝ)..(2 * Real.pi),
          (‖ToL1 (Complex.reCLM.compLp (Complex.exp ((θ : ℂ) * Complex.I) • v))‖
            + ‖ToL1 (Complex.imCLM.compLp (Complex.exp ((θ : ℂ) * Complex.I) • v))‖))
          * (2 * Real.pi)
        = ∫ θ in (0:ℝ)..(2 * Real.pi),
          (‖ToL1 (Complex.reCLM.compLp (Complex.exp ((θ : ℂ) * Complex.I) • v))‖
            + ‖ToL1 (Complex.imCLM.compLp (Complex.exp ((θ : ℂ) * Complex.I) • v))‖) := by
      have h2pine : (2 * Real.pi) ≠ 0 := by positivity
      have hrw : (1 / (2 * Real.pi)) *
          (∫ θ in (0:ℝ)..(2 * Real.pi),
            (‖ToL1 (Complex.reCLM.compLp (Complex.exp ((θ : ℂ) * Complex.I) • v))‖
              + ‖ToL1 (Complex.imCLM.compLp (Complex.exp ((θ : ℂ) * Complex.I) • v))‖))
            * (2 * Real.pi)
          = (∫ θ in (0:ℝ)..(2 * Real.pi),
            (‖ToL1 (Complex.reCLM.compLp (Complex.exp ((θ : ℂ) * Complex.I) • v))‖
              + ‖ToL1 (Complex.imCLM.compLp (Complex.exp ((θ : ℂ) * Complex.I) • v))‖))
            * ((2 * Real.pi) / (2 * Real.pi)) := by ring
      rw [hrw, div_self h2pine, mul_one]
    have hr : ((4 / Real.pi) * ∫ x, ‖(v : EuclideanSpace ℝ (Fin n) → ℂ) x‖
          ∂(GaussMeasure n)) * (2 * Real.pi)
        = 8 * ∫ x, ‖(v : EuclideanSpace ℝ (Fin n) → ℂ) x‖ ∂(GaussMeasure n) := by
      have hc : (4 / Real.pi) * (2 * Real.pi) = 8 := by
        have hrw : (4 / Real.pi) * (2 * Real.pi) = 8 * (Real.pi / Real.pi) := by ring
        rw [hrw, div_self hpine, mul_one]
      calc ((4 / Real.pi) * ∫ x, ‖(v : EuclideanSpace ℝ (Fin n) → ℂ) x‖ ∂(GaussMeasure n))
            * (2 * Real.pi)
          = ((4 / Real.pi) * (2 * Real.pi))
              * ∫ x, ‖(v : EuclideanSpace ℝ (Fin n) → ℂ) x‖ ∂(GaussMeasure n) := by ring
        _ = 8 * ∫ x, ‖(v : EuclideanSpace ℝ (Fin n) → ℂ) x‖ ∂(GaussMeasure n) := by rw [hc]
    rw [← hl, hstep, hr]
  rw [hI] at hmono
  rw [sub_zero] at hmono
  rw [div_mul_eq_mul_div, le_div_iff₀ hpi]
  nlinarith [hmono, hpi]
