import GaussianRiesz.CompIntegrationByParts
import GaussianRiesz.PVKernelConstantCancellation
open MeasureTheory
theorem PVSemigroupKernelDerivative {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hfc : HasCompactSupport f) (j : Fin n)
    (x : EuclideanSpace ℝ (Fin n)) (s : ℝ) (hs : 0 < s) :
    Integrable (fun y : EuclideanSpace ℝ (Fin n) =>
        (Real.sqrt 2 * Real.exp (-s) * (y j - Real.exp (-s) * x j) / (1 - Real.exp (-2 * s))
            * (Real.pi ^ (-(n : ℝ) / 2) * (1 - Real.exp (-2 * s)) ^ (-(n : ℝ) / 2)
                * Real.exp (-‖Real.exp (-s) • x - y‖ ^ 2 / (1 - Real.exp (-2 * s)))))
          * f y) volume
      ∧ ∫ y : EuclideanSpace ℝ (Fin n),
            (Real.sqrt 2 * Real.exp (-s) * (y j - Real.exp (-s) * x j) / (1 - Real.exp (-2 * s))
                * (Real.pi ^ (-(n : ℝ) / 2) * (1 - Real.exp (-2 * s)) ^ (-(n : ℝ) / 2)
                    * Real.exp (-‖Real.exp (-s) • x - y‖ ^ 2 / (1 - Real.exp (-2 * s)))))
              * f y
          = Real.exp (-s) * ((Real.sqrt 2)⁻¹ *
              ∫ z, fderiv ℝ f (Real.exp (-s) • x + Real.sqrt (1 - Real.exp (-2 * s)) • z)
                (EuclideanSpace.single j (1 : ℝ)) ∂(GaussMeasure n)) := by
  -- The route is the one the paper names: differentiate Mehler's formula.  Step 4 below
  -- identifies the Mehler average `A_s g` with the Lebesgue-kernel average
  -- `∫ p_s(x,y) g(y) dy` by a translation and a dilation, and Step 3 moves the `j`-th
  -- partial from `f` onto the kernel by integration by parts in `y`.  Together they turn
  -- `∫ D_j^x p_s(x,y) f(y) dy` into `e^{-s}(A_s(D_j f))(x)` with no semigroup theory,
  -- no `L^2` representative and no almost-everywhere statement to upgrade.
  obtain ⟨M, hM⟩ := hfc.exists_bound_of_continuous hf.continuous
  have hDp := ((PVKernelConstantCancellation j x).1 s hs).1
  have hr0 : 0 < Real.exp (-s) := Real.exp_pos _
  have hσ0' : 0 < 1 - Real.exp (-2 * s) := by
    have : Real.exp (-2 * s) < 1 := by rw [Real.exp_lt_one_iff]; linarith
    linarith
  set r : ℝ := Real.exp (-s) with hrdef
  set σ : ℝ := 1 - Real.exp (-2 * s) with hσdef
  have hσ0 : 0 < σ := hσ0'
  set τ : ℝ := Real.sqrt σ with hτdef
  have hτ0 : 0 < τ := by rw [hτdef]; exact Real.sqrt_pos.2 hσ0
  have hτ2 : τ ^ 2 = σ := by rw [hτdef, sq, Real.mul_self_sqrt hσ0.le]
  have hτn : τ ^ n = σ ^ ((n : ℝ) / 2) := by
    rw [hτdef, Real.sqrt_eq_rpow, ← Real.rpow_natCast (σ ^ ((1:ℝ)/2)) n, ← Real.rpow_mul hσ0.le]
    congr 1; ring
  set A : ℝ := Real.pi ^ (-(n : ℝ) / 2) * σ ^ (-(n : ℝ) / 2) with hAdef
  have hAσ : σ ^ ((n : ℝ) / 2) * A = Real.pi ^ (-(n : ℝ) / 2) := by
    rw [hAdef, show (-(n : ℝ) / 2) = -((n : ℝ) / 2) by ring, Real.rpow_neg hσ0.le]
    have : (0:ℝ) < σ ^ ((n : ℝ) / 2) := Real.rpow_pos_of_pos hσ0 _
    field_simp
  -- STEP 1: the clause-(1) integrability, against the bound on f
  have hint : Integrable (fun y : EuclideanSpace ℝ (Fin n) =>
      (Real.sqrt 2 * r * (y j - r * x j) / σ * (A * Real.exp (-‖r • x - y‖ ^ 2 / σ))) * f y)
      volume := by
    have hmaj : Integrable (fun y : EuclideanSpace ℝ (Fin n) => M *
        ‖Real.sqrt 2 * r * (y j - r * x j) / σ
          * (A * Real.exp (-‖r • x - y‖ ^ 2 / σ))‖) volume := hDp.norm.const_mul M
    have hmeas : AEStronglyMeasurable (fun y : EuclideanSpace ℝ (Fin n) =>
        (Real.sqrt 2 * r * (y j - r * x j) / σ * (A * Real.exp (-‖r • x - y‖ ^ 2 / σ))) * f y)
        volume := hDp.aestronglyMeasurable.mul hf.continuous.aestronglyMeasurable
    refine Integrable.mono' hmaj hmeas (Filter.Eventually.of_forall fun y => ?_)
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (hM y) (norm_nonneg _) |>.trans
      (le_of_eq (mul_comm _ _))
  refine ⟨hint, ?_⟩
  -- STEP 2: the kernel exponent, as a function of y, and its j-th partial
  set w : EuclideanSpace ℝ (Fin n) → ℝ := fun y => -σ⁻¹ * ‖r • x - y‖ ^ 2 with hwdef
  have hexp : ∀ y : EuclideanSpace ℝ (Fin n),
      Real.exp (w y) = Real.exp (-‖r • x - y‖ ^ 2 / σ) := by
    intro y; rw [hwdef]; congr 1; field_simp
  have hd1 : ∀ y : EuclideanSpace ℝ (Fin n),
      DifferentiableAt ℝ w y
        ∧ fderiv ℝ w y (EuclideanSpace.single j (1 : ℝ)) = 2 * (r * x j - y j) / σ := by
    intro y
    have hd0 : HasFDerivAt (fun y : EuclideanSpace ℝ (Fin n) => r • x - y)
        (-ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n))) y := by
      simpa using (hasFDerivAt_id y).const_sub (r • x)
    have h := (hd0.norm_sq).const_mul (-σ⁻¹)
    rw [hwdef]
    refine ⟨h.differentiableAt, ?_⟩
    rw [h.fderiv]
    simp [EuclideanSpace.inner_single_right]
    field_simp
    ring
  have hwd : Differentiable ℝ w := fun y => (hd1 y).1
  have hwc : Continuous (fun y : EuclideanSpace ℝ (Fin n) =>
      fderiv ℝ w y (EuclideanSpace.single j (1 : ℝ))) := by
    rw [show (fun y : EuclideanSpace ℝ (Fin n) =>
        fderiv ℝ w y (EuclideanSpace.single j (1 : ℝ)))
      = fun y : EuclideanSpace ℝ (Fin n) => 2 * (r * x j - y j) / σ from
        funext fun y => (hd1 y).2]
    fun_prop
  -- STEP 3: integration by parts in y
  set g : EuclideanSpace ℝ (Fin n) → ℝ :=
    fun y => fderiv ℝ f y (EuclideanSpace.single j (1 : ℝ)) with hgdef
  have hibp := CompIntegrationByParts Real.exp Real.exp (fun t => Real.hasDerivAt_exp t)
    Real.continuous_exp w j hwd hwc f hf hfc
  have hibp2 : ∫ y : EuclideanSpace ℝ (Fin n),
      (Real.exp (w y) * (2 * (y j - r * x j) / σ)) * f y
      = ∫ y : EuclideanSpace ℝ (Fin n), Real.exp (w y) * g y := by
    have h1 : ∫ y : EuclideanSpace ℝ (Fin n),
        (Real.exp (w y) * fderiv ℝ w y (EuclideanSpace.single j (1 : ℝ))) * f y
        = ∫ y : EuclideanSpace ℝ (Fin n), (Real.exp (w y) * (2 * (r * x j - y j) / σ)) * f y :=
      integral_congr_ae (Filter.Eventually.of_forall fun y => by
        show Real.exp (w y) * fderiv ℝ w y (EuclideanSpace.single j (1 : ℝ)) * f y
            = Real.exp (w y) * (2 * (r * x j - y j) / σ) * f y
        rw [(hd1 y).2])
    have h2 : ∫ y : EuclideanSpace ℝ (Fin n),
        (Real.exp (w y) * (2 * (y j - r * x j) / σ)) * f y
        = -∫ y : EuclideanSpace ℝ (Fin n),
            (Real.exp (w y) * (2 * (r * x j - y j) / σ)) * f y := by
      rw [← integral_neg]
      refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
      show Real.exp (w y) * (2 * (y j - r * x j) / σ) * f y
          = -(Real.exp (w y) * (2 * (r * x j - y j) / σ) * f y)
      ring
    rw [h2, ← h1, hibp]
  -- STEP 4: the Mehler average as a Lebesgue kernel average (change of variables)
  have hcov : ∫ z, g (r • x + τ • z) ∂(GaussMeasure n)
      = A * ∫ y : EuclideanSpace ℝ (Fin n), Real.exp (w y) * g y := by
    set Ψ : EuclideanSpace ℝ (Fin n) → ℝ := fun y => A * (Real.exp (w y) * g y) with hΨdef
    have hstep1 : ∫ z, g (r • x + τ • z) ∂(GaussMeasure n)
        = ∫ z : EuclideanSpace ℝ (Fin n),
            (Real.pi ^ (-(n : ℝ) / 2) * Real.exp (-‖z‖ ^ 2)) * g (r • x + τ • z) := by
      rw [GaussMeasure, integral_withDensity_eq_integral_toReal_smul
        (by fun_prop) (Filter.Eventually.of_forall fun z => ENNReal.ofReal_lt_top)]
      refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
      show (ENNReal.ofReal (Real.pi ^ (-(n : ℝ) / 2) * Real.exp (-‖z‖ ^ 2))).toReal
            • g (r • x + τ • z)
          = (Real.pi ^ (-(n : ℝ) / 2) * Real.exp (-‖z‖ ^ 2)) * g (r • x + τ • z)
      rw [smul_eq_mul, ENNReal.toReal_ofReal (by positivity)]
    have hstep2 : ∀ z : EuclideanSpace ℝ (Fin n),
        (Real.pi ^ (-(n : ℝ) / 2) * Real.exp (-‖z‖ ^ 2)) * g (r • x + τ • z)
          = σ ^ ((n : ℝ) / 2) * Ψ (r • x + τ • z) := by
      intro z
      have hn1 : ‖r • x - (r • x + τ • z)‖ ^ 2 = σ * ‖z‖ ^ 2 := by
        have h3 : r • x - (r • x + τ • z) = -(τ • z) := by abel
        rw [h3, norm_neg, norm_smul, Real.norm_eq_abs, abs_of_pos hτ0, mul_pow, hτ2]
      have hw1 : w (r • x + τ • z) = -‖z‖ ^ 2 := by
        rw [hwdef]; simp only; rw [hn1]; field_simp
      rw [hΨdef]
      simp only
      rw [hw1]
      rw [show σ ^ ((n : ℝ) / 2) * (A * (Real.exp (-‖z‖ ^ 2) * g (r • x + τ • z)))
          = (σ ^ ((n : ℝ) / 2) * A) * (Real.exp (-‖z‖ ^ 2) * g (r • x + τ • z)) by ring, hAσ]
      ring
    have hstep3 : ∫ z : EuclideanSpace ℝ (Fin n), Ψ (r • x + τ • z)
        = (σ ^ ((n : ℝ) / 2))⁻¹ * ∫ y : EuclideanSpace ℝ (Fin n), Ψ y := by
      have h4 := MeasureTheory.Measure.integral_comp_smul
        (μ := (volume : Measure (EuclideanSpace ℝ (Fin n)))) (fun v => Ψ (r • x + v)) τ
      rw [finrank_euclideanSpace_fin] at h4
      rw [h4, integral_add_left_eq_self Ψ (r • x), smul_eq_mul, hτn,
        abs_of_pos (by positivity : (0:ℝ) < (σ ^ ((n : ℝ) / 2))⁻¹)]
    rw [hstep1]
    rw [show (∫ z : EuclideanSpace ℝ (Fin n),
          (Real.pi ^ (-(n : ℝ) / 2) * Real.exp (-‖z‖ ^ 2)) * g (r • x + τ • z))
        = ∫ z : EuclideanSpace ℝ (Fin n), σ ^ ((n : ℝ) / 2) * Ψ (r • x + τ • z) from
      integral_congr_ae (Filter.Eventually.of_forall hstep2)]
    rw [integral_const_mul, hstep3, hΨdef]
    have hσp : (0:ℝ) < σ ^ ((n : ℝ) / 2) := Real.rpow_pos_of_pos hσ0 _
    rw [integral_const_mul]
    field_simp
  -- STEP 5: assemble
  rw [hcov]
  have h2s : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have h2p : (0:ℝ) < Real.sqrt 2 := by positivity
  have hne : Real.sqrt 2 ≠ 0 := ne_of_gt h2p
  have hhalf : Real.sqrt 2 / 2 = (Real.sqrt 2)⁻¹ := by
    field_simp
    linarith [h2s]
  calc ∫ y : EuclideanSpace ℝ (Fin n),
        (Real.sqrt 2 * r * (y j - r * x j) / σ * (A * Real.exp (-‖r • x - y‖ ^ 2 / σ))) * f y
      = (Real.sqrt 2 * r / 2 * A)
          * ∫ y : EuclideanSpace ℝ (Fin n), (Real.exp (w y) * (2 * (y j - r * x j) / σ)) * f y := by
        rw [← integral_const_mul]
        refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
        show Real.sqrt 2 * r * (y j - r * x j) / σ
              * (A * Real.exp (-‖r • x - y‖ ^ 2 / σ)) * f y
            = Real.sqrt 2 * r / 2 * A
              * (Real.exp (w y) * (2 * (y j - r * x j) / σ) * f y)
        rw [hexp y]
        field_simp
    _ = (Real.sqrt 2 * r / 2 * A) * ∫ y : EuclideanSpace ℝ (Fin n), Real.exp (w y) * g y := by
        rw [hibp2]
    _ = r * ((Real.sqrt 2)⁻¹ * (A * ∫ y : EuclideanSpace ℝ (Fin n), Real.exp (w y) * g y)) := by
        rw [← hhalf]; ring
