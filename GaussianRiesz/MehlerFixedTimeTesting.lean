module

public import GaussianRiesz.MehlerFormula
public import GaussianRiesz.LebesgueDilation
public import GaussianRiesz.GaussLebesgueBallComparison
public import GaussianRiesz.SemigroupGradientCommute
public import GaussianRiesz.CompIntegrationByParts
public import GaussianRiesz.FracPowLinear
public import GaussianRiesz.HermiteBasisVectorFacts
public import GaussianRiesz.HermiteL2ZeroAEOne

@[expose] public section
open MeasureTheory
theorem MehlerFixedTimeTesting {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hfc : HasCompactSupport f)
    (hmem : MemLp f 2 (GaussMeasure n))
    (φ : EuclideanSpace ℝ (Fin n) → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφc : HasCompactSupport φ) (i : Fin n) (s : ℝ) (hs : 0 < s) :
    Integrable (fun x : EuclideanSpace ℝ (Fin n) =>
        (OUSemigroup s (FracPow (0 : ℝ) (hmem.toLp f)) : EuclideanSpace ℝ (Fin n) → ℝ) x
          * fderiv ℝ φ x (EuclideanSpace.single i (1 : ℝ))) volume
      ∧ Integrable (fun x : EuclideanSpace ℝ (Fin n) =>
          (∫ z, fderiv ℝ f (Real.exp (-s) • x + Real.sqrt (1 - Real.exp (-2 * s)) • z)
            (EuclideanSpace.single i (1 : ℝ)) ∂(GaussMeasure n)) * φ x) volume
      ∧ ∫ x, (OUSemigroup s (FracPow (0 : ℝ) (hmem.toLp f)) : EuclideanSpace ℝ (Fin n) → ℝ) x
            * fderiv ℝ φ x (EuclideanSpace.single i (1 : ℝ))
          = -(Real.exp (-s)
              * ∫ x, (∫ z, fderiv ℝ f (Real.exp (-s) • x
                    + Real.sqrt (1 - Real.exp (-2 * s)) • z)
                  (EuclideanSpace.single i (1 : ℝ)) ∂(GaussMeasure n)) * φ x) := by
  classical
  set r : ℝ := Real.exp (-s) with hr
  set t : ℝ := Real.sqrt (1 - Real.exp (-2 * s)) with ht
  set u : Lp ℝ 2 (GaussMeasure n) := hmem.toLp f with hu
  set Af : EuclideanSpace ℝ (Fin n) → ℝ :=
    fun x => ∫ z, f (r • x + t • z) ∂(GaussMeasure n) with hAf
  set Adf : EuclideanSpace ℝ (Fin n) → ℝ :=
    fun x => ∫ z, fderiv ℝ f (r • x + t • z) (EuclideanSpace.single i (1 : ℝ))
      ∂(GaussMeasure n) with hAdf
  set dφ : EuclideanSpace ℝ (Fin n) → ℝ :=
    fun x => fderiv ℝ φ x (EuclideanSpace.single i (1 : ℝ)) with hdφ
  -- Step 4 is an existing node: `γₙ` and Lebesgue measure have exactly the same null sets.
  have hnull : ∀ A : Set (EuclideanSpace ℝ (Fin n)),
      GaussMeasure n A = 0 ↔ volume A = 0 := GaussLebesgueBallComparison.2.2.2
  have hconv : ∀ p : EuclideanSpace ℝ (Fin n) → Prop,
      (∀ᵐ x ∂(GaussMeasure n), p x) → ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))), p x := by
    intro p hp
    rw [MeasureTheory.ae_iff] at hp ⊢
    exact (hnull _).mp hp
  -- the spreading factor is nonzero, which is what the dilation step needs
  have ht0 : t ≠ 0 := by
    rw [ht]
    refine ne_of_gt (Real.sqrt_pos.mpr ?_)
    have : Real.exp (-2 * s) < 1 := by
      rw [Real.exp_lt_one_iff]; linarith
    linarith
  -- Step 0': continuity and differentiability of the Mehler averages, from the
  -- fixed-time node.  `hf` and `hfc` are consumed here and nowhere is `fderiv ℝ f`
  -- used as a junk value: removing `hf` stops `hSGC` elaborating, and every bound below
  -- rests on it (pm-0013).
  have hSGC := SemigroupGradientCommute s hs f hf hfc i
  have hAdfc : Continuous Adf := hSGC.2.2.1
  have hAfd : Differentiable ℝ Af := fun x => (hSGC.2.2.2 x).1
  have hAfderiv : ∀ x, fderiv ℝ Af x (EuclideanSpace.single i (1 : ℝ)) = r * Adf x :=
    fun x => (hSGC.2.2.2 x).2
  have hAfc : Continuous Af := hAfd.continuous
  have hdφc : Continuous dφ :=
    (hφ.continuous_fderiv (by simp)).clm_apply continuous_const
  have hdφcs : HasCompactSupport dφ := by
    have h := HasCompactSupport.comp_left (g := fun L : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ =>
      L (EuclideanSpace.single i (1 : ℝ))) (hφc.fderiv ℝ)
      (by simp)
    exact h
  -- Step 5: the Mehler average of the class is the Mehler average of `f`.
  have hNu : (u : EuclideanSpace ℝ (Fin n) → ℝ) =ᵐ[GaussMeasure n] f := by
    rw [hu]; exact hmem.coeFn_toLp
  have hN0 : GaussMeasure n {y | ¬ ((u : EuclideanSpace ℝ (Fin n) → ℝ) y = f y)} = 0 := by
    rw [← MeasureTheory.ae_iff]; exact hNu
  have hNvol : volume {y | ¬ ((u : EuclideanSpace ℝ (Fin n) → ℝ) y = f y)} = 0 :=
    (hnull _).mp hN0
  have hpull : ∀ x : EuclideanSpace ℝ (Fin n),
      GaussMeasure n {z | ¬ ((u : EuclideanSpace ℝ (Fin n) → ℝ) (r • x + t • z)
        = f (r • x + t • z))} = 0 := by
    intro x
    refine (hnull _).mpr ?_
    have h1 : volume ((fun y : EuclideanSpace ℝ (Fin n) => r • x + y) ⁻¹'
        {y | ¬ ((u : EuclideanSpace ℝ (Fin n) → ℝ) y = f y)}) = 0 := by
      rw [measure_preimage_add]; exact hNvol
    exact LebesgueDilation.2 t ht0 _ h1
  have hAeq : ∀ x : EuclideanSpace ℝ (Fin n),
      (∫ z, (u : EuclideanSpace ℝ (Fin n) → ℝ) (r • x + t • z) ∂(GaussMeasure n)) = Af x := by
    intro x
    refine integral_congr_ae ?_
    have hae : ∀ᵐ z ∂(GaussMeasure n),
        (u : EuclideanSpace ℝ (Fin n) → ℝ) (r • x + t • z) = f (r • x + t • z) := by
      rw [MeasureTheory.ae_iff]
      exact hpull x
    exact hae
  have hVae : (OUSemigroup s u : EuclideanSpace ℝ (Fin n) → ℝ) =ᵐ[GaussMeasure n] Af := by
    filter_upwards [(MehlerFormula s hs u).2.1] with x hx
    rw [hx, hAeq x]
  -- Step 8: the projection may be dropped, at the cost of a constant.
  have hc0 : Memℓp (FracPowCoeff (0 : ℝ)
      (fun α => (HermiteBasis n).repr u α)) 2 := (FracPowLinear (0 : ℝ)).1 le_rfl u
  have hprojcoe : ∀ α : Fin n → ℕ,
      (HermiteBasis n).repr (FracPow (0 : ℝ) u) α
        = if α = 0 then 0 else (HermiteBasis n).repr u α := by
    intro α
    have h : (HermiteBasis n).repr (FracPow (0 : ℝ) u) α
        = FracPowCoeff (0 : ℝ) (fun β => (HermiteBasis n).repr u β) α := by
      simp only [FracPow]
      rw [dif_pos hc0, LinearIsometryEquiv.apply_symm_apply]
    rw [h]
    unfold FracPowCoeff
    by_cases hα : α = 0
    · simp [hα]
    · rw [if_neg hα, if_neg hα, Real.rpow_zero, one_mul]
  have hsplit : OUSemigroup s (FracPow (0 : ℝ) u)
      = OUSemigroup s u - (HermiteBasis n).repr u 0 • (HermiteBasis n) 0 := by
    refine (HermiteBasis n).repr.injective (lp.ext (funext fun α => ?_))
    rw [map_sub, map_smul, lp.coeFn_sub, lp.coeFn_smul, Pi.sub_apply, Pi.smul_apply,
      smul_eq_mul, OUSemigroupSpectral s hs.le _ α, OUSemigroupSpectral s hs.le u α,
      hprojcoe α, HermiteBasisVectorFacts n |>.1 0, HermiteBasisVectorFacts n |>.2.1 0 α]
    by_cases hα : α = 0
    · subst hα
      have hz : MultiIndexSum (0 : Fin n → ℕ) = 0 := by simp [MultiIndexSum]
      simp [hz]
    · simp [hα]
  have hb0 : ((HermiteBasis n) 0 : EuclideanSpace ℝ (Fin n) → ℝ)
      =ᵐ[GaussMeasure n] fun _ => (1 : ℝ) := by
    rw [HermiteBasisVectorFacts n |>.1 0]
    exact HermiteL2ZeroAEOne
  have hWae : (OUSemigroup s (FracPow (0 : ℝ) u) : EuclideanSpace ℝ (Fin n) → ℝ)
      =ᵐ[volume] fun x => Af x - (HermiteBasis n).repr u 0 := by
    refine hconv _ ?_
    rw [hsplit]
    filter_upwards [Lp.coeFn_sub (OUSemigroup s u)
        ((HermiteBasis n).repr u 0 • (HermiteBasis n) 0),
      Lp.coeFn_smul ((HermiteBasis n).repr u 0) ((HermiteBasis n) 0), hb0, hVae]
      with x h1 h2 h3 h4
    rw [h1, Pi.sub_apply, h2, Pi.smul_apply, h3, h4, smul_eq_mul, mul_one]
  -- integrability of the three continuous compactly supported products
  have hIAf : Integrable (fun x => Af x * dφ x) volume :=
    (hAfc.mul hdφc).integrable_of_hasCompactSupport (hdφcs.mul_left)
  have hIc : Integrable (fun x => (HermiteBasis n).repr u 0 * dφ x) volume :=
    ((continuous_const).mul hdφc).integrable_of_hasCompactSupport (hdφcs.mul_left)
  have hIAdf : Integrable (fun x => Adf x * φ x) volume :=
    (hAdfc.mul hφ.continuous).integrable_of_hasCompactSupport (hφc.mul_left)
  have hIsub : Integrable (fun x => (Af x - (HermiteBasis n).repr u 0) * dφ x) volume := by
    have : (fun x => (Af x - (HermiteBasis n).repr u 0) * dφ x)
        = fun x => Af x * dφ x - (HermiteBasis n).repr u 0 * dφ x := by
      funext x; ring
    rw [this]
    exact hIAf.sub hIc
  -- clause (1)
  have hI1 : Integrable (fun x =>
      (OUSemigroup s (FracPow (0 : ℝ) u) : EuclideanSpace ℝ (Fin n) → ℝ) x * dφ x) volume := by
    refine hIsub.congr ?_
    filter_upwards [hWae] with x hx
    rw [hx]
  refine ⟨hI1, hIAdf, ?_⟩
  -- Step 9: integration by parts at fixed time
  have hstep9 : ∫ x, Af x * dφ x = -(r * ∫ x, Adf x * φ x) := by
    have hIBP := CompIntegrationByParts id (fun _ => (1 : ℝ))
      (fun y => hasDerivAt_id y) continuous_const Af i hAfd
      (by
        have : (fun x => fderiv ℝ Af x (EuclideanSpace.single i (1 : ℝ)))
            = fun x => r * Adf x := funext hAfderiv
        rw [this]
        exact hAdfc.const_mul r)
      φ hφ hφc
    simp only [id_eq, one_mul] at hIBP
    rw [hIBP]
    have hfun : (fun x => fderiv ℝ Af x (EuclideanSpace.single i (1 : ℝ)) * φ x)
        = fun x => r * (Adf x * φ x) := by
      funext x; rw [hAfderiv x]; ring
    rw [hfun, integral_const_mul]
  -- the constant term integrates to zero
  have hcd : ∀ x : EuclideanSpace ℝ (Fin n),
      fderiv ℝ (fun _ : EuclideanSpace ℝ (Fin n) => (1 : ℝ)) x (EuclideanSpace.single i (1 : ℝ))
        = 0 := by
    intro x; simp
  have hdφzero : ∫ x, dφ x = 0 := by
    have hIBP := CompIntegrationByParts id (fun _ => (1 : ℝ))
      (fun y => hasDerivAt_id y) continuous_const
      (fun _ : EuclideanSpace ℝ (Fin n) => (1 : ℝ)) i (differentiable_const 1)
      (by simp only [hcd]; exact continuous_const) φ hφ hφc
    simp only [id_eq, hcd, one_mul, mul_zero, zero_mul, integral_zero, neg_zero] at hIBP
    exact hIBP
  have hzero : ∫ x, (HermiteBasis n).repr u 0 * dφ x = 0 := by
    rw [integral_const_mul, hdφzero, mul_zero]
  calc ∫ x, (OUSemigroup s (FracPow (0 : ℝ) u) : EuclideanSpace ℝ (Fin n) → ℝ) x * dφ x
      = ∫ x, (Af x - (HermiteBasis n).repr u 0) * dφ x := by
        refine integral_congr_ae ?_
        filter_upwards [hWae] with x hx
        rw [hx]
    _ = (∫ x, Af x * dφ x) - ∫ x, (HermiteBasis n).repr u 0 * dφ x := by
        have heq : (fun x => (Af x - (HermiteBasis n).repr u 0) * dφ x)
            = fun x => Af x * dφ x - (HermiteBasis n).repr u 0 * dφ x := by
          funext x; ring
        rw [heq, integral_sub hIAf hIc]
    _ = -(r * ∫ x, Adf x * φ x) := by rw [hzero, hstep9, sub_zero]
