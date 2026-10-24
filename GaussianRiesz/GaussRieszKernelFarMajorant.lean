import GaussianRiesz.GaussRieszKernel
import GaussianRiesz.GaussLebesgueBallComparison
import GaussianRiesz.GaussRieszKernelFarSliceMajorant
open MeasureTheory
open scoped ENNReal
theorem GaussRieszKernelFarMajorant {n : ℕ} (j : Fin n) :
    (∀ R ρ : ℝ, 0 < R → 0 < ρ → ∃ C : ℝ, 0 < C ∧
        (∀ x y : EuclideanSpace ℝ (Fin n), ‖x‖ ≤ R → ρ ≤ ‖x - y‖ →
            IntegrableOn (fun r : ℝ =>
                (y j - r * x j) / ((1 - r ^ 2) ^ ((n : ℝ) / 2 + 1) * Real.sqrt (-Real.log r))
                  * Real.exp (-‖r • x - y‖ ^ 2 / (1 - r ^ 2))) (Set.Ioo (0 : ℝ) 1) volume
              ∧ |GaussRieszKernel j x y| ≤ C * Real.exp (-‖y‖ ^ 2))
          ∧ (∀ f : EuclideanSpace ℝ (Fin n) → ℝ, MemLp f 1 (GaussMeasure n) →
              ∀ x : EuclideanSpace ℝ (Fin n), ‖x‖ ≤ R →
                IntegrableOn (fun y => GaussRieszKernel j x y * f y)
                    {y : EuclideanSpace ℝ (Fin n) | ρ < ‖x - y‖} volume
                  ∧ |∫ y in {y : EuclideanSpace ℝ (Fin n) | ρ < ‖x - y‖},
                        GaussRieszKernel j x y * f y|
                      ≤ C * ∫ y, |f y| ∂(GaussMeasure n)))
      ∧ (∀ f : EuclideanSpace ℝ (Fin n) → ℝ, MemLp f 1 (GaussMeasure n) → ∀ ε : ℝ, 0 < ε →
          Measurable (fun x : EuclideanSpace ℝ (Fin n) =>
            ∫ y in {y : EuclideanSpace ℝ (Fin n) | ε < ‖x - y‖}, GaussRieszKernel j x y * f y))
      ∧ (∀ f : EuclideanSpace ℝ (Fin n) → ℝ, MemLp f 1 (GaussMeasure n) →
          ∀ x : EuclideanSpace ℝ (Fin n),
            ContinuousOn (fun ε : ℝ =>
                ∫ y in {y : EuclideanSpace ℝ (Fin n) | ε < ‖x - y‖}, GaussRieszKernel j x y * f y)
              (Set.Ioi (0 : ℝ))) := by
  -- Clause (1)(a) -- the `.tex`'s Steps 0 through 4, i.e. the splitting identity, the
  -- reduction to `R >= 1`, `rho <= 1`, and the two `r`-ranges -- is
  -- `GaussRieszKernelFarSliceMajorant`, whose own `[1/2,1)` range is
  -- `GaussRieszKernelEndpointSliceBound`.  What is assembled here is Step 5 (joint
  -- measurability of the kernel in `(x,y)`, which is the measurability half of the Fubini
  -- package applied to the continuous `r`-integrand), Step 6 (clause (1)(b): the far
  -- majorant pairs with the Gaussian density, so the truncated kernel integral is
  -- dominated by `||f||_{L^1(gamma)}`), Step 7 (clause (2): the same measurability half,
  -- now integrating out `y`, after replacing `f` by a Borel representative -- legitimate
  -- because `gamma_n` and Lebesgue measure have the same null sets, clause (4) of
  -- `GaussLebesgueBallComparison`), and Step 8 (clause (3): dominated convergence in
  -- `epsilon`, whose only non-routine input is that the sphere `{|x-y| = epsilon}` is
  -- Lebesgue-null).
  -- STEP 5 of the `.tex`, inlined: the kernel is jointly measurable in `(x,y)`
  have hKjoint : Measurable (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
      GaussRieszKernel j p.1 p.2) := by
    have h1 : Measurable (fun q : (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) × ℝ =>
        (q.1.2 j - q.2 * q.1.1 j)
            / ((1 - q.2 ^ 2) ^ ((n : ℝ) / 2 + 1) * Real.sqrt (-Real.log q.2))
          * Real.exp (-‖q.2 • q.1.1 - q.1.2‖ ^ 2 / (1 - q.2 ^ 2))) := by fun_prop
    have h2 := h1.stronglyMeasurable.integral_prod_right'
      (ν := volume.restrict (Set.Ioo (0:ℝ) 1))
    exact h2.measurable.const_mul (Real.sqrt 2 * Real.pi ^ (-((n : ℝ) + 1) / 2))
  have hKmeas : ∀ x : EuclideanSpace ℝ (Fin n),
      Measurable (fun y : EuclideanSpace ℝ (Fin n) => GaussRieszKernel j x y) :=
    fun x => hKjoint.comp (measurable_const.prodMk measurable_id)
  -- the truncation regions are measurable
  have hregm : ∀ (x : EuclideanSpace ℝ (Fin n)) (ε : ℝ),
      MeasurableSet {y : EuclideanSpace ℝ (Fin n) | ε < ‖x - y‖} :=
    fun x ε => measurableSet_lt measurable_const (by fun_prop)
  -- γ_n and λ have the same null sets, so λ-a.e. statements follow from γ_n-a.e. ones
  have h4 := (GaussLebesgueBallComparison (n := n)).2.2.2
  have hac : (volume : Measure (EuclideanSpace ℝ (Fin n))) ≪ GaussMeasure n :=
    Measure.AbsolutelyContinuous.mk (fun s _ hs0 => (h4 s).1 hs0)
  have hfmeas : ∀ f : EuclideanSpace ℝ (Fin n) → ℝ, MemLp f 1 (GaussMeasure n) →
      AEStronglyMeasurable f volume := fun f hf => (hf.1).mono_ac hac
  -- the density pairing
  have hpi3 : (0:ℝ) < Real.pi ^ ((n : ℝ) / 2) := Real.rpow_pos_of_pos Real.pi_pos _
  have hpiinv : Real.pi ^ ((n : ℝ) / 2) * Real.pi ^ (-(n : ℝ) / 2) = 1 := by
    rw [← Real.rpow_add Real.pi_pos, show ((n : ℝ) / 2 + -(n : ℝ) / 2) = 0 by ring,
      Real.rpow_zero]
  have hdens : ∀ g : EuclideanSpace ℝ (Fin n) → ℝ,
      ∫ y, g y ∂(GaussMeasure n)
        = Real.pi ^ (-(n : ℝ) / 2)
          * ∫ y : EuclideanSpace ℝ (Fin n), Real.exp (-‖y‖ ^ 2) * g y := by
    intro g
    rw [GaussMeasure, integral_withDensity_eq_integral_toReal_smul (by fun_prop)
      (Filter.Eventually.of_forall fun z => ENNReal.ofReal_lt_top), ← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    show (ENNReal.ofReal (Real.pi ^ (-(n : ℝ) / 2) * Real.exp (-‖z‖ ^ 2))).toReal • g z
        = Real.pi ^ (-(n : ℝ) / 2) * (Real.exp (-‖z‖ ^ 2) * g z)
    rw [smul_eq_mul, ENNReal.toReal_ofReal (by positivity), mul_assoc]
  -- for f ∈ L¹(γ_n) the Gaussian-weighted modulus is λ-integrable
  have hfint : ∀ f : EuclideanSpace ℝ (Fin n) → ℝ, MemLp f 1 (GaussMeasure n) →
      Integrable (fun y : EuclideanSpace ℝ (Fin n) => Real.exp (-‖y‖ ^ 2) * |f y|) volume := by
    intro f hf
    have h1 : Integrable (fun y => |f y|) (GaussMeasure n) :=
      (memLp_one_iff_integrable.1 hf).abs
    rw [GaussMeasure, integrable_withDensity_iff_integrable_smul' (by fun_prop)
      (Filter.Eventually.of_forall fun z => ENNReal.ofReal_lt_top)] at h1
    have h2 : Integrable (fun z : EuclideanSpace ℝ (Fin n) =>
        Real.pi ^ (-(n : ℝ) / 2) * (Real.exp (-‖z‖ ^ 2) * |f z|)) volume := by
      refine h1.congr (Filter.Eventually.of_forall fun z => ?_)
      show (ENNReal.ofReal (Real.pi ^ (-(n : ℝ) / 2) * Real.exp (-‖z‖ ^ 2))).toReal • |f z|
          = Real.pi ^ (-(n : ℝ) / 2) * (Real.exp (-‖z‖ ^ 2) * |f z|)
      rw [smul_eq_mul, ENNReal.toReal_ofReal (by positivity), mul_assoc]
    refine (h2.const_mul (Real.pi ^ ((n : ℝ) / 2))).congr
      (Filter.Eventually.of_forall fun z => ?_)
    show Real.pi ^ ((n : ℝ) / 2) * (Real.pi ^ (-(n : ℝ) / 2) * (Real.exp (-‖z‖ ^ 2) * |f z|))
        = Real.exp (-‖z‖ ^ 2) * |f z|
    rw [← mul_assoc, hpiinv, one_mul]
  -- the pairing identity in the form the bound needs
  have hpair : ∀ f : EuclideanSpace ℝ (Fin n) → ℝ,
      ∫ y : EuclideanSpace ℝ (Fin n), Real.exp (-‖y‖ ^ 2) * |f y|
        = Real.pi ^ ((n : ℝ) / 2) * ∫ y, |f y| ∂(GaussMeasure n) := by
    intro f
    rw [hdens (fun y => |f y|), ← mul_assoc, hpiinv, one_mul]
  refine ⟨fun R ρ hR hρ => ?_, ?_, ?_⟩
  · -- CLAUSE (1)
    obtain ⟨Cm, hCm0, hCmbd⟩ := GaussRieszKernelFarSliceMajorant j R ρ hR hρ
    have hpi1 : (1:ℝ) ≤ Real.pi ^ ((n : ℝ) / 2) := by
      have h0 : Real.pi ^ (0:ℝ) ≤ Real.pi ^ ((n : ℝ) / 2) :=
        Real.rpow_le_rpow_of_exponent_le (by linarith [Real.two_le_pi]) (by positivity)
      rwa [Real.rpow_zero] at h0
    refine ⟨Cm * Real.pi ^ ((n : ℝ) / 2), mul_pos hCm0 hpi3, fun x y hx hxy => ?_, ?_⟩
    · refine ⟨(hCmbd x y hx hxy).1, ?_⟩
      exact le_trans (hCmbd x y hx hxy).2
        (mul_le_mul_of_nonneg_right (le_mul_of_one_le_right hCm0.le hpi1)
          (Real.exp_pos _).le)
    · intro f hf x hx
      have hΩm := hregm x ρ
      have hmf : AEStronglyMeasurable f
          (volume.restrict {y : EuclideanSpace ℝ (Fin n) | ρ < ‖x - y‖}) :=
        (hfmeas f hf).mono_measure Measure.restrict_le_self
      have hprod : AEStronglyMeasurable (fun y => GaussRieszKernel j x y * f y)
          (volume.restrict {y : EuclideanSpace ℝ (Fin n) | ρ < ‖x - y‖}) :=
        ((hKmeas x).aestronglyMeasurable).mul hmf
      have hbint : Integrable (fun y : EuclideanSpace ℝ (Fin n) =>
          Cm * (Real.exp (-‖y‖ ^ 2) * |f y|)) volume := (hfint f hf).const_mul Cm
      have hptw : ∀ y ∈ {y : EuclideanSpace ℝ (Fin n) | ρ < ‖x - y‖},
          ‖GaussRieszKernel j x y * f y‖ ≤ Cm * (Real.exp (-‖y‖ ^ 2) * |f y|) := by
        intro y hy
        have h6 := (hCmbd x y hx (le_of_lt hy)).2
        rw [Real.norm_eq_abs, abs_mul]
        calc |GaussRieszKernel j x y| * |f y|
            ≤ (Cm * Real.exp (-‖y‖ ^ 2)) * |f y| :=
              mul_le_mul_of_nonneg_right h6 (abs_nonneg _)
          _ = Cm * (Real.exp (-‖y‖ ^ 2) * |f y|) := by ring
      have hae : ∀ᵐ y ∂(volume.restrict {y : EuclideanSpace ℝ (Fin n) | ρ < ‖x - y‖}),
          ‖GaussRieszKernel j x y * f y‖ ≤ Cm * (Real.exp (-‖y‖ ^ 2) * |f y|) :=
        (ae_restrict_iff' hΩm).2 (Filter.Eventually.of_forall hptw)
      refine ⟨Integrable.mono' hbint.integrableOn hprod hae, ?_⟩
      have hb1 : |∫ y in {y : EuclideanSpace ℝ (Fin n) | ρ < ‖x - y‖},
            GaussRieszKernel j x y * f y|
          ≤ ∫ y in {y : EuclideanSpace ℝ (Fin n) | ρ < ‖x - y‖},
            ‖GaussRieszKernel j x y * f y‖ := by
        have h0 := norm_integral_le_integral_norm
          (μ := volume.restrict {y : EuclideanSpace ℝ (Fin n) | ρ < ‖x - y‖})
          (fun y => GaussRieszKernel j x y * f y)
        simp only [Real.norm_eq_abs] at h0
        exact h0
      have hb2 : ∫ y in {y : EuclideanSpace ℝ (Fin n) | ρ < ‖x - y‖},
            ‖GaussRieszKernel j x y * f y‖
          ≤ ∫ y in {y : EuclideanSpace ℝ (Fin n) | ρ < ‖x - y‖},
            Cm * (Real.exp (-‖y‖ ^ 2) * |f y|) :=
        integral_mono_of_nonneg (Filter.Eventually.of_forall fun y => norm_nonneg _)
          hbint.integrableOn hae
      have hb3 : ∫ y in {y : EuclideanSpace ℝ (Fin n) | ρ < ‖x - y‖},
            Cm * (Real.exp (-‖y‖ ^ 2) * |f y|)
          ≤ ∫ y : EuclideanSpace ℝ (Fin n), Cm * (Real.exp (-‖y‖ ^ 2) * |f y|) :=
        setIntegral_le_integral hbint (Filter.Eventually.of_forall fun y =>
          mul_nonneg hCm0.le (mul_nonneg (Real.exp_pos _).le (abs_nonneg _)))
      have hb4 : ∫ y : EuclideanSpace ℝ (Fin n), Cm * (Real.exp (-‖y‖ ^ 2) * |f y|)
          = Cm * Real.pi ^ ((n : ℝ) / 2) * ∫ y, |f y| ∂(GaussMeasure n) := by
        rw [integral_const_mul, hpair f, mul_assoc]
      linarith [hb1, hb2, hb3, hb4]
  · -- CLAUSE (2)
    intro f hf ε hε
    obtain ⟨g, hgm, hgae⟩ := hfmeas f hf
    have hsetm : MeasurableSet {q : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) |
        ε < ‖q.1 - q.2‖} := measurableSet_lt measurable_const (by fun_prop)
    have heq : ∀ x : EuclideanSpace ℝ (Fin n),
        (∫ y in {y : EuclideanSpace ℝ (Fin n) | ε < ‖x - y‖}, GaussRieszKernel j x y * f y)
          = ∫ y : EuclideanSpace ℝ (Fin n),
            Set.indicator {q : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) |
              ε < ‖q.1 - q.2‖} (fun q => GaussRieszKernel j q.1 q.2 * g q.2) (x, y) := by
      intro x
      rw [← integral_indicator (hregm x ε)]
      refine integral_congr_ae ?_
      filter_upwards [hgae] with y hy
      by_cases hmem : ε < ‖x - y‖
      · rw [Set.indicator_of_mem
            (show y ∈ {y : EuclideanSpace ℝ (Fin n) | ε < ‖x - y‖} from hmem),
          Set.indicator_of_mem
            (show (x, y) ∈ {q : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) |
              ε < ‖q.1 - q.2‖} from hmem), hy]
      · rw [Set.indicator_of_notMem
            (show y ∉ {y : EuclideanSpace ℝ (Fin n) | ε < ‖x - y‖} from hmem),
          Set.indicator_of_notMem
            (show (x, y) ∉ {q : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) |
              ε < ‖q.1 - q.2‖} from hmem)]
    rw [funext heq]
    have hindm : Measurable (Set.indicator
        {q : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) | ε < ‖q.1 - q.2‖}
        (fun q => GaussRieszKernel j q.1 q.2 * g q.2)) :=
      (hKjoint.mul (hgm.measurable.comp measurable_snd)).indicator hsetm
    exact (hindm.stronglyMeasurable.integral_prod_right').measurable
  · -- CLAUSE (3)
    intro f hf x e he
    have he0 : (0:ℝ) < e := he
    obtain ⟨Cm, hCm0, hCmbd⟩ := GaussRieszKernelFarSliceMajorant j (max ‖x‖ 1) (e/2)
      (lt_of_lt_of_le one_pos (le_max_right _ _)) (by linarith)
    have hxR : ‖x‖ ≤ max ‖x‖ 1 := le_max_left _ _
    have hbint : Integrable (fun y : EuclideanSpace ℝ (Fin n) =>
        Cm * (Real.exp (-‖y‖ ^ 2) * |f y|)) volume := (hfint f hf).const_mul Cm
    have hsph : (volume : Measure (EuclideanSpace ℝ (Fin n))) {y | ‖x - y‖ = e} = 0 := by
      have hs : {y : EuclideanSpace ℝ (Fin n) | ‖x - y‖ = e} = Metric.sphere x e := by
        ext y
        simp only [Set.mem_ofPred_eq, Metric.mem_sphere, dist_eq_norm]
        constructor
        · intro h; rw [← h, norm_sub_rev]
        · intro h; rw [← h, norm_sub_rev]
      rw [hs]
      exact Measure.addHaar_sphere_of_ne_zero volume x (ne_of_gt he0)
    have hane : ∀ᵐ y ∂(volume : Measure (EuclideanSpace ℝ (Fin n))), ‖x - y‖ ≠ e := by
      rw [MeasureTheory.ae_iff]
      simpa using hsph
    have hdct := tendsto_integral_filter_of_dominated_convergence
      (μ := (volume : Measure (EuclideanSpace ℝ (Fin n))))
      (l := nhdsWithin e (Set.Ioi (0:ℝ)))
      (F := fun (ε : ℝ) => Set.indicator {y : EuclideanSpace ℝ (Fin n) | ε < ‖x - y‖}
        (fun y => GaussRieszKernel j x y * f y))
      (f := Set.indicator {y : EuclideanSpace ℝ (Fin n) | e < ‖x - y‖}
        (fun y => GaussRieszKernel j x y * f y))
      (fun y => Cm * (Real.exp (-‖y‖ ^ 2) * |f y|))
      (Filter.Eventually.of_forall fun ε =>
        (((hKmeas x).aestronglyMeasurable).mul (hfmeas f hf)).indicator (hregm x ε))
      ?_ hbint ?_
    · have hconv : ∀ ε : ℝ,
          (∫ y : EuclideanSpace ℝ (Fin n),
            Set.indicator {y : EuclideanSpace ℝ (Fin n) | ε < ‖x - y‖}
              (fun y => GaussRieszKernel j x y * f y) y)
            = ∫ y in {y : EuclideanSpace ℝ (Fin n) | ε < ‖x - y‖},
              GaussRieszKernel j x y * f y := fun ε => integral_indicator (hregm x ε)
      have hgoal : Filter.Tendsto
          (fun ε : ℝ => ∫ y in {y : EuclideanSpace ℝ (Fin n) | ε < ‖x - y‖},
            GaussRieszKernel j x y * f y)
          (nhdsWithin e (Set.Ioi (0:ℝ)))
          (nhds (∫ y in {y : EuclideanSpace ℝ (Fin n) | e < ‖x - y‖},
            GaussRieszKernel j x y * f y)) := by
        simpa only [hconv] using hdct
      exact hgoal
    · have hev : ∀ᶠ ε in nhdsWithin e (Set.Ioi (0:ℝ)), e/2 < ε :=
        Filter.Eventually.filter_mono nhdsWithin_le_nhds (lt_mem_nhds (by linarith))
      filter_upwards [hev] with ε hεe
      refine Filter.Eventually.of_forall fun y => ?_
      by_cases hmem : ε < ‖x - y‖
      · rw [Set.indicator_of_mem
            (show y ∈ {y : EuclideanSpace ℝ (Fin n) | ε < ‖x - y‖} from hmem),
          Real.norm_eq_abs, abs_mul]
        have h6 := (hCmbd x y hxR (by linarith : e/2 ≤ ‖x - y‖)).2
        calc |GaussRieszKernel j x y| * |f y|
            ≤ (Cm * Real.exp (-‖y‖ ^ 2)) * |f y| :=
              mul_le_mul_of_nonneg_right h6 (abs_nonneg _)
          _ = Cm * (Real.exp (-‖y‖ ^ 2) * |f y|) := by ring
      · rw [Set.indicator_of_notMem
            (show y ∉ {y : EuclideanSpace ℝ (Fin n) | ε < ‖x - y‖} from hmem), norm_zero]
        exact mul_nonneg hCm0.le (mul_nonneg (Real.exp_pos _).le (abs_nonneg _))
    · filter_upwards [hane] with y hy
      rcases lt_or_gt_of_ne hy with hlt | hgt
      · rw [Set.indicator_of_notMem
            (show y ∉ {y : EuclideanSpace ℝ (Fin n) | e < ‖x - y‖} from by
              simp only [Set.mem_ofPred_eq]; linarith)]
        refine Filter.Tendsto.congr' ?_ tendsto_const_nhds
        filter_upwards [Filter.Eventually.filter_mono nhdsWithin_le_nhds
          (lt_mem_nhds hlt)] with ε hε'
        exact (Set.indicator_of_notMem
          (show y ∉ {y : EuclideanSpace ℝ (Fin n) | ε < ‖x - y‖} from by
            simp only [Set.mem_ofPred_eq]; linarith)
          (fun y => GaussRieszKernel j x y * f y)).symm
      · rw [Set.indicator_of_mem
            (show y ∈ {y : EuclideanSpace ℝ (Fin n) | e < ‖x - y‖} from hgt)]
        refine Filter.Tendsto.congr' ?_ tendsto_const_nhds
        filter_upwards [Filter.Eventually.filter_mono nhdsWithin_le_nhds
          (gt_mem_nhds hgt)] with ε hε'
        exact (Set.indicator_of_mem
          (show y ∈ {y : EuclideanSpace ℝ (Fin n) | ε < ‖x - y‖} from hε')
          (fun y => GaussRieszKernel j x y * f y)).symm
