module

public import Mathlib.Analysis.Calculus.BumpFunction.SmoothApprox
public import GaussianRiesz.GaussIsProb
public import GaussianRiesz.GaussLebesgueBallComparison

@[expose] public section
open MeasureTheory
open scoped ENNReal
theorem SmoothCompactDenseL1Gauss {n : ℕ} (g : Lp ℝ 1 (GaussMeasure n))
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ φ : EuclideanSpace ℝ (Fin n) → ℝ,
      ContDiff ℝ (⊤ : ℕ∞) φ ∧ HasCompactSupport φ ∧ MemLp φ 1 (GaussMeasure n)
        ∧ eLpNorm (fun y => (g : EuclideanSpace ℝ (Fin n) → ℝ) y - φ y) 1 (GaussMeasure n)
            < ENNReal.ofReal δ := by
  -- Steps 0 and 1 of the `.tex` are the `withDensity` transport: the `L^1(gamma_n)` seminorm of
  -- `w` is the `L^1(lambda)` seminorm of `rho . w`, with `rho` the Gaussian density, so `g`
  -- becomes `h = rho . g` in `L^1(lambda)`.  Step 2 is Mathlib's density of continuous compactly
  -- supported functions in `L^p` of a regular measure.  Step 3 replaces the `.tex`'s explicit
  -- mollifier construction by Mathlib's smooth approximation of a uniformly continuous function
  -- together with a `ContDiffBump` cut-off: the cut-off is `1` on a ball containing `supp u`, so
  -- multiplying by it costs nothing in the sup bound (where `u` vanishes, `|chi . w| <= |w - u|`)
  -- and restores the compact support the approximation lemma does not provide.  Step 4 transports
  -- back along `phi = pi^{n/2} e^{|y|^2} v`, which is smooth and nowhere zero, so it preserves
  -- smoothness and the support, and `rho . phi = v` by construction.
  have : IsProbabilityMeasure (GaussMeasure n) := GaussIsProb n
  have hρm : Measurable (fun y : EuclideanSpace ℝ (Fin n) =>
      Real.pi ^ (-(n : ℝ) / 2) * Real.exp (-‖y‖ ^ 2)) := by fun_prop
  have hρpos : ∀ y : EuclideanSpace ℝ (Fin n),
      (0:ℝ) < Real.pi ^ (-(n : ℝ) / 2) * Real.exp (-‖y‖ ^ 2) := by
    intro y
    have h1 : (0:ℝ) < Real.pi ^ (-(n : ℝ) / 2) := Real.rpow_pos_of_pos Real.pi_pos _
    positivity
  have hρσ : ∀ y : EuclideanSpace ℝ (Fin n),
      (Real.pi ^ (-(n : ℝ) / 2) * Real.exp (-‖y‖ ^ 2))
        * (Real.pi ^ ((n : ℝ) / 2) * Real.exp (‖y‖ ^ 2)) = 1 := by
    intro y
    have hp : Real.pi ^ (-(n : ℝ) / 2) * Real.pi ^ ((n : ℝ) / 2) = 1 := by
      rw [← Real.rpow_add Real.pi_pos, show (-(n : ℝ) / 2 + (n : ℝ) / 2) = 0 by ring,
        Real.rpow_zero]
    have he : Real.exp (-‖y‖ ^ 2) * Real.exp (‖y‖ ^ 2) = 1 := by
      rw [← Real.exp_add]; simp
    calc (Real.pi ^ (-(n : ℝ) / 2) * Real.exp (-‖y‖ ^ 2))
          * (Real.pi ^ ((n : ℝ) / 2) * Real.exp (‖y‖ ^ 2))
        = (Real.pi ^ (-(n : ℝ) / 2) * Real.pi ^ ((n : ℝ) / 2))
          * (Real.exp (-‖y‖ ^ 2) * Real.exp (‖y‖ ^ 2)) := by ring
      _ = 1 := by rw [hp, he]; ring
  -- STEP 0: γ_n and λ have the same null sets
  have h4 := (GaussLebesgueBallComparison (n := n)).2.2.2
  have hacv : (volume : Measure (EuclideanSpace ℝ (Fin n))) ≪ GaussMeasure n :=
    Measure.AbsolutelyContinuous.mk (fun s _ hs0 => (h4 s).1 hs0)
  -- the transport of the L¹ seminorm through the density
  have htrans : ∀ w : EuclideanSpace ℝ (Fin n) → ℝ, AEMeasurable w volume →
      eLpNorm w 1 (GaussMeasure n)
        = eLpNorm (fun y => (Real.pi ^ (-(n : ℝ) / 2) * Real.exp (-‖y‖ ^ 2)) * w y) 1 volume := by
    intro w hw
    rw [eLpNorm_one_eq_lintegral_enorm (μ := GaussMeasure n)
        (hw.aestronglyMeasurable.mono_ac (withDensity_absolutelyContinuous _ _)),
      eLpNorm_one_eq_lintegral_enorm
        (f := fun y => (Real.pi ^ (-(n : ℝ) / 2) * Real.exp (-‖y‖ ^ 2)) * w y)
        (hρm.aestronglyMeasurable.mul hw.aestronglyMeasurable),
      GaussMeasure,
      lintegral_withDensity_eq_lintegral_mul₀ (by fun_prop) hw.enorm]
    refine lintegral_congr fun y => ?_
    show ENNReal.ofReal (Real.pi ^ (-(n : ℝ) / 2) * Real.exp (-‖y‖ ^ 2)) * ‖w y‖ₑ
        = ‖(Real.pi ^ (-(n : ℝ) / 2) * Real.exp (-‖y‖ ^ 2)) * w y‖ₑ
    rw [enorm_mul, Real.enorm_eq_ofReal (hρpos y).le]
  -- STEP 1: transport g to L¹(λ)
  have hgmem := Lp.memLp g
  have hgaem : AEStronglyMeasurable (fun y => (g : EuclideanSpace ℝ (Fin n) → ℝ) y) volume :=
    hgmem.aestronglyMeasurable.mono_ac hacv
  have hhmem : MemLp (fun y : EuclideanSpace ℝ (Fin n) =>
      (Real.pi ^ (-(n : ℝ) / 2) * Real.exp (-‖y‖ ^ 2))
        * (g : EuclideanSpace ℝ (Fin n) → ℝ) y) 1 volume := by
    unfold MemLp
    rw [← htrans _ hgaem.aemeasurable]
    exact hgmem
  -- STEP 2: a continuous compactly supported approximant in L¹(λ)
  obtain ⟨u, hu_cs, hu_le, hu_cont, hu_mem⟩ :=
    hhmem.exists_hasCompactSupport_eLpNorm_sub_le (by norm_num)
      (ε := ENNReal.ofReal (δ / 3))
      (by simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]; linarith)
  -- STEP 3: a smooth compactly supported approximant to u
  have hu_uc : UniformContinuous u := hu_cs.uniformContinuous_of_continuous hu_cont
  obtain ⟨Rr, hRr0, hRr⟩ : ∃ Rr : ℝ, 0 < Rr ∧ tsupport u ⊆ Metric.closedBall 0 Rr := by
    obtain ⟨R0, hR0⟩ := hu_cs.isBounded.subset_closedBall 0
    exact ⟨max R0 1, lt_of_lt_of_le one_pos (le_max_right _ _),
      hR0.trans (Metric.closedBall_subset_closedBall (le_max_left _ _))⟩
  set χ : ContDiffBump (0 : EuclideanSpace ℝ (Fin n)) := ⟨Rr, Rr + 1, hRr0, by linarith⟩ with hχdef
  obtain ⟨V, hV0, hVeq⟩ : ∃ V : ℝ, 0 ≤ V ∧
      volume (Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) (Rr + 1)) = ENNReal.ofReal V :=
    ⟨(volume (Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) (Rr + 1))).toReal,
      ENNReal.toReal_nonneg,
      (ENNReal.ofReal_toReal (ne_of_lt measure_closedBall_lt_top)).symm⟩
  obtain ⟨η, hη0, hηbd⟩ : ∃ η : ℝ, 0 < η ∧
      ENNReal.ofReal η * volume (Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) (Rr + 1))
        ≤ ENNReal.ofReal (δ / 3) := by
    have hd0 : (0:ℝ) < (δ / 3) / (V + 1) := div_pos (by linarith) (by linarith)
    refine ⟨(δ / 3) / (V + 1), hd0, ?_⟩
    rw [hVeq, ← ENNReal.ofReal_mul hd0.le]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [div_mul_eq_mul_div, div_le_iff₀ (by linarith)]
    nlinarith [hV0, hδ]
  obtain ⟨w, hw_cd, hw_close⟩ := UniformContinuous.exists_contDiff_dist_le hu_uc hη0
  -- the pointwise comparison of v = χ · w with u
  have hvu : ∀ y : EuclideanSpace ℝ (Fin n),
      |u y - (χ : EuclideanSpace ℝ (Fin n) → ℝ) y * w y| ≤ η := by
    intro y
    have hwy : |w y - u y| < η := by
      have h0 := hw_close y
      rwa [Real.dist_eq] at h0
    by_cases hy : y ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) Rr
    · rw [ContDiffBump.one_of_mem_closedBall χ hy, one_mul, abs_sub_comm]
      exact hwy.le
    · have hu0 : u y = 0 := by
        have hns : y ∉ tsupport u := fun hmem => hy (hRr hmem)
        exact image_eq_zero_of_notMem_tsupport hns
      rw [hu0, zero_sub, abs_neg, abs_mul, abs_of_nonneg (ContDiffBump.nonneg (f := χ))]
      calc (χ : EuclideanSpace ℝ (Fin n) → ℝ) y * |w y|
          ≤ 1 * |w y| := mul_le_mul_of_nonneg_right (ContDiffBump.le_one (f := χ)) (abs_nonneg _)
        _ = |w y - u y| := by rw [hu0, sub_zero, one_mul]
        _ ≤ η := hwy.le
  have hvu0 : ∀ y : EuclideanSpace ℝ (Fin n),
      y ∉ Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) (Rr + 1) →
      u y - (χ : EuclideanSpace ℝ (Fin n) → ℝ) y * w y = 0 := by
    intro y hy
    have hu0 : u y = 0 := by
      have hns : y ∉ tsupport u := fun hmem =>
        hy (Metric.closedBall_subset_closedBall (by linarith) (hRr hmem))
      exact image_eq_zero_of_notMem_tsupport hns
    have hχ0 : (χ : EuclideanSpace ℝ (Fin n) → ℝ) y = 0 := by
      by_contra hne
      have hmem : y ∈ Function.support (χ : EuclideanSpace ℝ (Fin n) → ℝ) :=
        Function.mem_support.2 hne
      rw [ContDiffBump.support_eq] at hmem
      exact hy (Metric.ball_subset_closedBall hmem)
    rw [hu0, hχ0, zero_mul, sub_zero]
  have hbd : eLpNorm (fun y => u y - (χ : EuclideanSpace ℝ (Fin n) → ℝ) y * w y) 1 volume
      ≤ ENNReal.ofReal η
        * volume (Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) (Rr + 1)) := by
    rw [eLpNorm_one_eq_lintegral_enorm
      (f := fun y => u y - (χ : EuclideanSpace ℝ (Fin n) → ℝ) y * w y)
      (hu_cont.sub ((ContDiffBump.contDiff χ).mul hw_cd).continuous).aestronglyMeasurable]
    calc ∫⁻ y : EuclideanSpace ℝ (Fin n),
          ‖u y - (χ : EuclideanSpace ℝ (Fin n) → ℝ) y * w y‖ₑ
        ≤ ∫⁻ y : EuclideanSpace ℝ (Fin n),
            (Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) (Rr + 1)).indicator
              (fun _ => ENNReal.ofReal η) y := by
          refine lintegral_mono fun y => ?_
          by_cases hy : y ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) (Rr + 1)
          · rw [Set.indicator_of_mem hy, Real.enorm_eq_ofReal_abs]
            exact ENNReal.ofReal_le_ofReal (hvu y)
          · rw [Set.indicator_of_notMem hy, hvu0 y hy]
            simp
      _ = ENNReal.ofReal η
            * volume (Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) (Rr + 1)) :=
          lintegral_indicator_const measurableSet_closedBall _
  -- STEP 4: transport back
  have hσ_cd : ContDiff ℝ (⊤ : ℕ∞) (fun y : EuclideanSpace ℝ (Fin n) =>
      Real.pi ^ ((n : ℝ) / 2) * Real.exp (‖y‖ ^ 2)) :=
    contDiff_const.mul (Real.contDiff_exp.comp (contDiff_norm_sq ℝ))
  have hv_cd : ContDiff ℝ (⊤ : ℕ∞) (fun y : EuclideanSpace ℝ (Fin n) =>
      (χ : EuclideanSpace ℝ (Fin n) → ℝ) y * w y) := (ContDiffBump.contDiff χ).mul hw_cd
  have hv_cs : HasCompactSupport (fun y : EuclideanSpace ℝ (Fin n) =>
      (χ : EuclideanSpace ℝ (Fin n) → ℝ) y * w y) :=
    (ContDiffBump.hasCompactSupport χ).mul_right
  refine ⟨fun y => Real.pi ^ ((n : ℝ) / 2) * Real.exp (‖y‖ ^ 2)
      * ((χ : EuclideanSpace ℝ (Fin n) → ℝ) y * w y), hσ_cd.mul hv_cd, hv_cs.mul_left, ?_, ?_⟩
  · have hcont : Continuous (fun y : EuclideanSpace ℝ (Fin n) =>
        Real.pi ^ ((n : ℝ) / 2) * Real.exp (‖y‖ ^ 2)
          * ((χ : EuclideanSpace ℝ (Fin n) → ℝ) y * w y)) := (hσ_cd.mul hv_cd).continuous
    obtain ⟨M, hM⟩ := (hv_cs.mul_left).exists_bound_of_continuous hcont
    exact MemLp.of_bound hcont.aestronglyMeasurable M (Filter.Eventually.of_forall hM)
  · have hφaem : AEMeasurable (fun y : EuclideanSpace ℝ (Fin n) =>
        (g : EuclideanSpace ℝ (Fin n) → ℝ) y - Real.pi ^ ((n : ℝ) / 2) * Real.exp (‖y‖ ^ 2)
          * ((χ : EuclideanSpace ℝ (Fin n) → ℝ) y * w y)) volume :=
      hgaem.aemeasurable.sub (hσ_cd.mul hv_cd).continuous.measurable.aemeasurable
    rw [htrans _ hφaem]
    have hid : ∀ y : EuclideanSpace ℝ (Fin n),
        (Real.pi ^ (-(n : ℝ) / 2) * Real.exp (-‖y‖ ^ 2))
            * ((g : EuclideanSpace ℝ (Fin n) → ℝ) y
              - Real.pi ^ ((n : ℝ) / 2) * Real.exp (‖y‖ ^ 2)
                * ((χ : EuclideanSpace ℝ (Fin n) → ℝ) y * w y))
          = ((Real.pi ^ (-(n : ℝ) / 2) * Real.exp (-‖y‖ ^ 2))
                * (g : EuclideanSpace ℝ (Fin n) → ℝ) y - u y)
            + (u y - (χ : EuclideanSpace ℝ (Fin n) → ℝ) y * w y) := by
      intro y
      linear_combination (-((χ : EuclideanSpace ℝ (Fin n) → ℝ) y * w y)) * hρσ y
    calc eLpNorm (fun y : EuclideanSpace ℝ (Fin n) =>
            (Real.pi ^ (-(n : ℝ) / 2) * Real.exp (-‖y‖ ^ 2))
              * ((g : EuclideanSpace ℝ (Fin n) → ℝ) y
                - Real.pi ^ ((n : ℝ) / 2) * Real.exp (‖y‖ ^ 2)
                  * ((χ : EuclideanSpace ℝ (Fin n) → ℝ) y * w y))) 1 volume
        = eLpNorm (fun y : EuclideanSpace ℝ (Fin n) =>
            ((Real.pi ^ (-(n : ℝ) / 2) * Real.exp (-‖y‖ ^ 2))
                * (g : EuclideanSpace ℝ (Fin n) → ℝ) y - u y)
              + (u y - (χ : EuclideanSpace ℝ (Fin n) → ℝ) y * w y)) 1 volume :=
          eLpNorm_congr_ae (Filter.Eventually.of_forall hid)
      _ ≤ eLpNorm (fun y : EuclideanSpace ℝ (Fin n) =>
              (Real.pi ^ (-(n : ℝ) / 2) * Real.exp (-‖y‖ ^ 2))
                * (g : EuclideanSpace ℝ (Fin n) → ℝ) y - u y) 1 volume
            + eLpNorm (fun y : EuclideanSpace ℝ (Fin n) =>
              u y - (χ : EuclideanSpace ℝ (Fin n) → ℝ) y * w y) 1 volume :=
          eLpNorm_add_le le_rfl
      _ ≤ ENNReal.ofReal (δ / 3) + ENNReal.ofReal (δ / 3) :=
          add_le_add hu_le (hbd.trans hηbd)
      _ < ENNReal.ofReal δ := by
          rw [← ENNReal.ofReal_add (by linarith) (by linarith)]
          exact (ENNReal.ofReal_lt_ofReal_iff hδ).2 (by linarith)
