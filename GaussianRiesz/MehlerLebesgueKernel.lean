module

public import GaussianRiesz.MehlerFormula

@[expose] public section
open MeasureTheory
theorem MehlerLebesgueKernel {n : ℕ} (s : ℝ) (hs : 0 < s) (v : Lp ℝ 2 (GaussMeasure n)) :
    (∀ᵐ x ∂(GaussMeasure n), Integrable (fun y : EuclideanSpace ℝ (Fin n) =>
        Real.pi ^ (-(n : ℝ) / 2) * (1 - Real.exp (-2 * s)) ^ (-(n : ℝ) / 2)
            * Real.exp (-‖Real.exp (-s) • x - y‖ ^ 2 / (1 - Real.exp (-2 * s)))
          * (v : EuclideanSpace ℝ (Fin n) → ℝ) y) volume)
      ∧ (∀ᵐ x ∂(GaussMeasure n),
          (OUSemigroup s v : EuclideanSpace ℝ (Fin n) → ℝ) x
            = ∫ y : EuclideanSpace ℝ (Fin n),
                Real.pi ^ (-(n : ℝ) / 2) * (1 - Real.exp (-2 * s)) ^ (-(n : ℝ) / 2)
                    * Real.exp (-‖Real.exp (-s) • x - y‖ ^ 2 / (1 - Real.exp (-2 * s)))
                  * (v : EuclideanSpace ℝ (Fin n) → ℝ) y) := by
  classical
  obtain ⟨hM1, hM2, -⟩ := MehlerFormula s hs v
  -- the spreading factor `σ = 1 - e^{-2s}` and `τ = √σ` are positive
  have hσpos : (0 : ℝ) < 1 - Real.exp (-2 * s) := by
    have h : Real.exp (-2 * s) < 1 := by
      rw [Real.exp_lt_one_iff]
      linarith
    linarith
  set σ : ℝ := 1 - Real.exp (-2 * s) with hσdef
  set τ : ℝ := Real.sqrt σ with hτdef
  have hτpos : (0 : ℝ) < τ := Real.sqrt_pos.mpr hσpos
  have hτ2 : τ ^ 2 = σ := Real.sq_sqrt hσpos.le
  -- `τ^{-n} = σ^{-n/2}`
  have hτn : (τ ^ n)⁻¹ = σ ^ (-(n : ℝ) / 2) := by
    rw [hτdef, Real.sqrt_eq_rpow, ← Real.rpow_natCast (σ ^ ((1 : ℝ) / 2)) n,
      ← Real.rpow_mul hσpos.le, ← Real.rpow_neg hσpos.le]
    congr 1
    ring
  have hfr : Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) = n := by simp
  -- the Gaussian density, as `GaussMeasure` writes it
  have hdm : Measurable (fun z : EuclideanSpace ℝ (Fin n) =>
      ENNReal.ofReal (Real.pi ^ (-(n : ℝ) / 2) * Real.exp (-‖z‖ ^ 2))) := by fun_prop
  have hfin : ∀ᵐ z ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
      ENNReal.ofReal (Real.pi ^ (-(n : ℝ) / 2) * Real.exp (-‖z‖ ^ 2)) < ⊤ :=
    Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top
  have key : ∀ᵐ x ∂(GaussMeasure n),
      Integrable (fun y : EuclideanSpace ℝ (Fin n) =>
          Real.pi ^ (-(n : ℝ) / 2) * σ ^ (-(n : ℝ) / 2)
              * Real.exp (-‖Real.exp (-s) • x - y‖ ^ 2 / σ)
            * (v : EuclideanSpace ℝ (Fin n) → ℝ) y) volume
        ∧ (OUSemigroup s v : EuclideanSpace ℝ (Fin n) → ℝ) x
            = ∫ y : EuclideanSpace ℝ (Fin n),
                Real.pi ^ (-(n : ℝ) / 2) * σ ^ (-(n : ℝ) / 2)
                    * Real.exp (-‖Real.exp (-s) • x - y‖ ^ 2 / σ)
                  * (v : EuclideanSpace ℝ (Fin n) → ℝ) y := by
    filter_upwards [hM1, hM2] with x h1 h2
    set a : EuclideanSpace ℝ (Fin n) := Real.exp (-s) • x with hadef
    -- the Lebesgue-kernel integrand, and its translate
    set G : EuclideanSpace ℝ (Fin n) → ℝ := fun y =>
      Real.pi ^ (-(n : ℝ) / 2) * Real.exp (-‖y - a‖ ^ 2 / σ)
        * (v : EuclideanSpace ℝ (Fin n) → ℝ) y with hGdef
    set F : EuclideanSpace ℝ (Fin n) → ℝ := fun w => G (a + w) with hFdef
    -- STEP 2: unfold `γₙ` in both clauses of `MehlerFormula`.  The rewrite cannot be done
    -- in place: `v` has a `GaussMeasure n`-dependent type, so `rw [GaussMeasure] at h1`
    -- has an ill-typed motive.  Unfolding happens by `exact` up to delta instead.
    have h1' : Integrable (fun z : EuclideanSpace ℝ (Fin n) =>
        (v : EuclideanSpace ℝ (Fin n) → ℝ) (a + τ • z)
          * (ENNReal.ofReal (Real.pi ^ (-(n : ℝ) / 2)
              * Real.exp (-‖z‖ ^ 2))).toReal) volume :=
      (integrable_withDensity_iff hdm hfin).mp h1
    have h2' : (OUSemigroup s v : EuclideanSpace ℝ (Fin n) → ℝ) x
        = ∫ z : EuclideanSpace ℝ (Fin n),
            (ENNReal.ofReal (Real.pi ^ (-(n : ℝ) / 2)
              * Real.exp (-‖z‖ ^ 2))).toReal
              • (v : EuclideanSpace ℝ (Fin n) → ℝ) (a + τ • z) := by
      rw [h2]
      exact integral_withDensity_eq_integral_toReal_smul hdm hfin
        (fun z => (v : EuclideanSpace ℝ (Fin n) → ℝ) (a + τ • z))
    -- the averaging integrand is `F (τ • z)`
    have hpt : ∀ z : EuclideanSpace ℝ (Fin n),
        (v : EuclideanSpace ℝ (Fin n) → ℝ) (a + τ • z)
            * (ENNReal.ofReal (Real.pi ^ (-(n : ℝ) / 2) * Real.exp (-‖z‖ ^ 2))).toReal
          = F (τ • z) := by
      intro z
      have hnorm : ‖(a + τ • z) - a‖ ^ 2 = σ * ‖z‖ ^ 2 := by
        rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos hτpos, mul_pow, hτ2]
      have hpi : (0 : ℝ) ≤ Real.pi ^ (-(n : ℝ) / 2) * Real.exp (-‖z‖ ^ 2) := by positivity
      rw [hFdef, hGdef, ENNReal.toReal_ofReal hpi]
      simp only []
      rw [hnorm, show -(σ * ‖z‖ ^ 2) / σ = -‖z‖ ^ 2 by field_simp]
      ring
    -- STEP 3: the dilation and the translation
    have hFt : Integrable (fun z : EuclideanSpace ℝ (Fin n) => F (τ • z)) volume :=
      h1'.congr (Filter.Eventually.of_forall hpt)
    have hF : Integrable F volume := (integrable_comp_smul_iff volume F hτpos.ne').mp hFt
    have hG : Integrable G volume :=
      (((measurePreserving_add_left volume a).integrable_comp_emb
        (MeasurableEquiv.addLeft a).measurableEmbedding)).mp hF
    -- STEP 4: identify the kernel
    have hfinal : ∀ y : EuclideanSpace ℝ (Fin n),
        (τ ^ n)⁻¹ * G y
          = Real.pi ^ (-(n : ℝ) / 2) * σ ^ (-(n : ℝ) / 2)
              * Real.exp (-‖a - y‖ ^ 2 / σ)
            * (v : EuclideanSpace ℝ (Fin n) → ℝ) y := by
      intro y
      rw [hGdef, hτn]
      simp only []
      rw [norm_sub_rev y a]
      ring
    refine ⟨?_, ?_⟩
    · exact (hG.const_mul ((τ ^ n)⁻¹)).congr (Filter.Eventually.of_forall hfinal)
    · calc (OUSemigroup s v : EuclideanSpace ℝ (Fin n) → ℝ) x
          = ∫ z : EuclideanSpace ℝ (Fin n),
              (ENNReal.ofReal (Real.pi ^ (-(n : ℝ) / 2)
                * Real.exp (-‖z‖ ^ 2))).toReal
                • (v : EuclideanSpace ℝ (Fin n) → ℝ) (a + τ • z) := h2'
        _ = ∫ z : EuclideanSpace ℝ (Fin n), F (τ • z) := by
            refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
            simp only [smul_eq_mul]
            rw [mul_comm]
            exact hpt z
        _ = (τ ^ n)⁻¹ • ∫ w : EuclideanSpace ℝ (Fin n), F w := by
            have h := Measure.integral_comp_smul_of_nonneg
              (volume : Measure (EuclideanSpace ℝ (Fin n))) F τ (hR := hτpos.le)
            rwa [hfr] at h
        _ = (τ ^ n)⁻¹ * ∫ y : EuclideanSpace ℝ (Fin n), G y := by
            rw [smul_eq_mul, hFdef]
            congr 1
            exact integral_add_left_eq_self G a
        _ = ∫ y : EuclideanSpace ℝ (Fin n), (τ ^ n)⁻¹ * G y := (integral_const_mul _ _).symm
        _ = ∫ y : EuclideanSpace ℝ (Fin n),
              Real.pi ^ (-(n : ℝ) / 2) * σ ^ (-(n : ℝ) / 2)
                  * Real.exp (-‖Real.exp (-s) • x - y‖ ^ 2 / σ)
                * (v : EuclideanSpace ℝ (Fin n) → ℝ) y := by
            refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
            exact hfinal y
  exact ⟨key.mono fun x h => h.1, key.mono fun x h => h.2⟩
