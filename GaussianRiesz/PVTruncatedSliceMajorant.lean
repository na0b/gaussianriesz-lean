import GaussianRiesz.MehlerKernelSliceVanishing
import GaussianRiesz.GaussFirstMomentTranslationL1Bound
open MeasureTheory
theorem PVTruncatedSliceMajorant {n : ℕ} (j : Fin n) (x : EuclideanSpace ℝ (Fin n)) :
    (∃ C : ℝ, 0 ≤ C ∧ ∀ ε s : ℝ, 0 < ε → 0 < s →
        |∫ y in {y : EuclideanSpace ℝ (Fin n) | ε < ‖x - y‖},
            Real.sqrt 2 * Real.exp (-s) * (y j - Real.exp (-s) * x j) / (1 - Real.exp (-2 * s))
              * (Real.pi ^ (-(n : ℝ) / 2) * (1 - Real.exp (-2 * s)) ^ (-(n : ℝ) / 2)
                  * Real.exp (-‖Real.exp (-s) • x - y‖ ^ 2 / (1 - Real.exp (-2 * s))))|
          ≤ C * ‖x‖ * Real.exp (-s))
      ∧ (∀ s : ℝ, 0 < s →
          Filter.Tendsto
            (fun ε : ℝ => ∫ y in {y : EuclideanSpace ℝ (Fin n) | ε < ‖x - y‖},
              Real.sqrt 2 * Real.exp (-s) * (y j - Real.exp (-s) * x j)
                  / (1 - Real.exp (-2 * s))
                * (Real.pi ^ (-(n : ℝ) / 2) * (1 - Real.exp (-2 * s)) ^ (-(n : ℝ) / 2)
                    * Real.exp (-‖Real.exp (-s) • x - y‖ ^ 2 / (1 - Real.exp (-2 * s)))))
            (nhdsWithin 0 (Set.Ioi 0)) (nhds 0)) := by
  classical
  -- the L¹ translation-difference bound, by a single pointwise majorant
  have diffbound := GaussFirstMomentTranslationL1Bound j

  have hSmeas : ∀ ε : ℝ, MeasurableSet {y : EuclideanSpace ℝ (Fin n) | ε < ‖x - y‖} := by
    intro ε
    have hcty : Continuous (fun y : EuclideanSpace ℝ (Fin n) => ‖x - y‖) := by fun_prop
    exact measurableSet_lt measurable_const hcty.measurable
  refine ⟨⟨Real.sqrt 2 * (5 + 24 * (8 : ℝ) ^ ((n : ℝ) / 2)), by positivity, ?_⟩, ?_⟩
  · intro ε s hε hs
    set r : ℝ := Real.exp (-s) with hr
    set σ : ℝ := 1 - Real.exp (-2 * s) with hσ
    have hr0 : 0 < r := Real.exp_pos _
    have hr1 : r < 1 := by rw [hr, Real.exp_lt_one_iff]; linarith
    have hσ0 : 0 < σ := by
      rw [hσ]
      have h : Real.exp (-2 * s) < 1 := by rw [Real.exp_lt_one_iff]; linarith
      linarith
    have hrσ : σ = (1 - r) * (1 + r) := by
      rw [hσ, hr, show (-2 : ℝ) * s = -s + -s by ring, Real.exp_add]; ring
    set b : ℝ := 1 / σ with hb
    have hb0 : 0 < b := by rw [hb]; positivity
    set c : ℝ := Real.sqrt 2 * r
      * (Real.pi ^ (-(n : ℝ) / 2) * σ ^ (-(n : ℝ) / 2)) / σ with hc
    have hc0 : 0 ≤ c := by
      rw [hc]
      have h1 : (0:ℝ) < Real.pi ^ (-(n : ℝ) / 2) := Real.rpow_pos_of_pos Real.pi_pos _
      have h2 : (0:ℝ) < σ ^ (-(n : ℝ) / 2) := Real.rpow_pos_of_pos hσ0 _
      positivity
    set d : EuclideanSpace ℝ (Fin n) := (1 - r) • x with hd
    have hdn : ‖d‖ = (1 - r) * ‖x‖ := by
      rw [hd, norm_smul, Real.norm_eq_abs, abs_of_pos (by linarith)]
    set F : EuclideanSpace ℝ (Fin n) → ℝ := fun y =>
      Real.sqrt 2 * r * (y j - r * x j) / σ
        * (Real.pi ^ (-(n : ℝ) / 2) * σ ^ (-(n : ℝ) / 2)
            * Real.exp (-‖r • x - y‖ ^ 2 / σ)) with hF
    set W : EuclideanSpace ℝ (Fin n) → ℝ := fun w =>
      c * (w j) * Real.exp (-b * ‖w‖ ^ 2) with hW
    have hFW : ∀ w : EuclideanSpace ℝ (Fin n), F (r • x + w) = W w := by
      intro w
      have h1 : ((r • x + w) j - r * x j) = w j := by simp
      have h2 : r • x - (r • x + w) = -w := by abel
      have h3 : -‖w‖ ^ 2 / σ = -b * ‖w‖ ^ 2 := by rw [hb]; field_simp
      simp only [hF, hW, hc]
      rw [h1, h2, norm_neg, h3]
      ring
    -- Step 1: translate by `r • x`
    have hWmeas : MeasurableSet {w : EuclideanSpace ℝ (Fin n) | ε < ‖d - w‖} := by
      have hcty : Continuous (fun w : EuclideanSpace ℝ (Fin n) => ‖d - w‖) := by fun_prop
      exact measurableSet_lt measurable_const hcty.measurable
    have hpre1 : (fun w : EuclideanSpace ℝ (Fin n) => r • x + w) ⁻¹'
        {y : EuclideanSpace ℝ (Fin n) | ε < ‖x - y‖}
          = {w : EuclideanSpace ℝ (Fin n) | ε < ‖d - w‖} := by
      ext w
      have hxx : x - (r • x + w) = d - w := by
        rw [hd, sub_smul, one_smul]; abel
      simp only [Set.mem_preimage, Set.mem_ofPred_eq, hxx]
    have hT1 : ∫ w in {w : EuclideanSpace ℝ (Fin n) | ε < ‖d - w‖}, W w
        = ∫ y in {y : EuclideanSpace ℝ (Fin n) | ε < ‖x - y‖}, F y := by
      have h := ((measurePreserving_add_left
        (volume : Measure (EuclideanSpace ℝ (Fin n))) (r • x)).restrict_preimage
        (hSmeas ε)).integral_comp (measurableEmbedding_addLeft (r • x)) F
      rw [hpre1] at h
      rw [← h]
      exact setIntegral_congr_fun hWmeas fun w _ => (hFW w).symm
    -- Step 2: translate by `d`
    have hpre2 : (fun z : EuclideanSpace ℝ (Fin n) => z + d) ⁻¹'
        {w : EuclideanSpace ℝ (Fin n) | ε < ‖d - w‖}
          = {z : EuclideanSpace ℝ (Fin n) | ε < ‖z‖} := by
      ext z
      have hzz : d - (z + d) = -z := by abel
      simp only [Set.mem_preimage, Set.mem_ofPred_eq, hzz, norm_neg]
    have hT2 : ∫ z in {z : EuclideanSpace ℝ (Fin n) | ε < ‖z‖}, W (z + d)
        = ∫ w in {w : EuclideanSpace ℝ (Fin n) | ε < ‖d - w‖}, W w := by
      have h := ((measurePreserving_add_right
        (volume : Measure (EuclideanSpace ℝ (Fin n))) d).restrict_preimage
        hWmeas).integral_comp (measurableEmbedding_addRight d) W
      rwa [hpre2] at h
    -- Step 3: oddness on the neg-invariant exterior region
    have hSneg : (fun z : EuclideanSpace ℝ (Fin n) => -z) ⁻¹'
        {z : EuclideanSpace ℝ (Fin n) | ε < ‖z‖}
          = {z : EuclideanSpace ℝ (Fin n) | ε < ‖z‖} := by
      ext z; simp
    have hZmeas : MeasurableSet {z : EuclideanSpace ℝ (Fin n) | ε < ‖z‖} := by
      have hcty : Continuous (fun z : EuclideanSpace ℝ (Fin n) => ‖z‖) := by fun_prop
      exact measurableSet_lt measurable_const hcty.measurable
    have hWodd : ∀ z : EuclideanSpace ℝ (Fin n), W (-z) = -W z := by
      intro z
      have h1 : ((-z : EuclideanSpace ℝ (Fin n)) j) = -(z j) := by simp
      have h2 : ‖(-z : EuclideanSpace ℝ (Fin n))‖ = ‖z‖ := norm_neg z
      simp only [hW, h1, h2]; ring
    have hWzero : ∫ z in {z : EuclideanSpace ℝ (Fin n) | ε < ‖z‖}, W z = 0 := by
      have hmp : MeasurePreserving (fun z : EuclideanSpace ℝ (Fin n) => -z)
          (volume.restrict {z : EuclideanSpace ℝ (Fin n) | ε < ‖z‖})
          (volume.restrict {z : EuclideanSpace ℝ (Fin n) | ε < ‖z‖}) := by
        have h := (Measure.measurePreserving_neg
          (volume : Measure (EuclideanSpace ℝ (Fin n)))).restrict_preimage hZmeas
        rwa [hSneg] at h
      have h1 : ∫ z in {z : EuclideanSpace ℝ (Fin n) | ε < ‖z‖}, W (-z)
          = ∫ z in {z : EuclideanSpace ℝ (Fin n) | ε < ‖z‖}, W z :=
        hmp.integral_comp measurableEmbedding_neg W
      have h2 : ∫ z in {z : EuclideanSpace ℝ (Fin n) | ε < ‖z‖}, W (-z)
          = -∫ z in {z : EuclideanSpace ℝ (Fin n) | ε < ‖z‖}, W z := by
        rw [show (fun z : EuclideanSpace ℝ (Fin n) => W (-z)) = fun z => -W z from
          funext hWodd, integral_neg]
      rw [h2] at h1
      linarith
    -- integrability of the translated integrand
    have hIF : Integrable F volume := (MehlerKernelSliceVanishing j x s hs).1
    have hIW : Integrable W volume := by
      have h := ((measurePreserving_add_left
        (volume : Measure (EuclideanSpace ℝ (Fin n))) (r • x)).integrable_comp_emb
        (measurableEmbedding_addLeft (r • x))).mpr hIF
      have heq : (F ∘ fun w : EuclideanSpace ℝ (Fin n) => r • x + w) = W := by
        funext w; simpa [Function.comp_def] using hFW w
      rwa [heq] at h
    have hIWd : Integrable (fun z : EuclideanSpace ℝ (Fin n) => W (z + d)) volume := by
      have h := ((measurePreserving_add_right
        (volume : Measure (EuclideanSpace ℝ (Fin n))) d).integrable_comp_emb
        (measurableEmbedding_addRight d)).mpr hIW
      simpa [Function.comp_def] using h
    -- Step 4: the difference bound
    have hdiff : |∫ y in {y : EuclideanSpace ℝ (Fin n) | ε < ‖x - y‖}, F y|
        ≤ c * ‖d‖ * ((Real.pi / b) ^ ((n : ℝ) / 2)
            * (5 + 24 * (8 : ℝ) ^ ((n : ℝ) / 2))) := by
      rw [← hT1, ← hT2]
      have hsub : ∫ z in {z : EuclideanSpace ℝ (Fin n) | ε < ‖z‖}, W (z + d)
          = ∫ z in {z : EuclideanSpace ℝ (Fin n) | ε < ‖z‖}, (W (z + d) - W z) := by
        rw [integral_sub hIWd.restrict hIW.restrict, hWzero, sub_zero]
      rw [hsub]
      calc |∫ z in {z : EuclideanSpace ℝ (Fin n) | ε < ‖z‖}, (W (z + d) - W z)|
          ≤ ∫ z in {z : EuclideanSpace ℝ (Fin n) | ε < ‖z‖}, |W (z + d) - W z| := by
            simpa [Real.norm_eq_abs] using norm_integral_le_integral_norm
              (μ := volume.restrict {z : EuclideanSpace ℝ (Fin n) | ε < ‖z‖})
              (fun z => W (z + d) - W z)
        _ ≤ ∫ z : EuclideanSpace ℝ (Fin n), |W (z + d) - W z| :=
            setIntegral_le_integral (hIWd.sub hIW).abs
              (Filter.Eventually.of_forall fun z => abs_nonneg _)
        _ ≤ c * ‖d‖ * ((Real.pi / b) ^ ((n : ℝ) / 2)
              * (5 + 24 * (8 : ℝ) ^ ((n : ℝ) / 2))) := by
            simpa [hW] using diffbound b c hb0 hc0 d
    -- Step 5: the constant chase
    have hpib : Real.pi / b = Real.pi * σ := by rw [hb]; field_simp
    have hcancel : c * ((Real.pi / b) ^ ((n : ℝ) / 2)) = Real.sqrt 2 * r / σ := by
      have e1 : Real.pi ^ (-(n : ℝ) / 2) * Real.pi ^ ((n : ℝ) / 2) = 1 := by
        rw [← Real.rpow_add Real.pi_pos, show -(n : ℝ) / 2 + (n : ℝ) / 2 = 0 from by ring,
          Real.rpow_zero]
      have e2 : σ ^ (-(n : ℝ) / 2) * σ ^ ((n : ℝ) / 2) = 1 := by
        rw [← Real.rpow_add hσ0, show -(n : ℝ) / 2 + (n : ℝ) / 2 = 0 from by ring,
          Real.rpow_zero]
      rw [hpib, Real.mul_rpow Real.pi_pos.le hσ0.le, hc]
      calc Real.sqrt 2 * r * (Real.pi ^ (-(n : ℝ) / 2) * σ ^ (-(n : ℝ) / 2)) / σ
            * (Real.pi ^ ((n : ℝ) / 2) * σ ^ ((n : ℝ) / 2))
          = Real.sqrt 2 * r / σ
              * ((Real.pi ^ (-(n : ℝ) / 2) * Real.pi ^ ((n : ℝ) / 2))
                * (σ ^ (-(n : ℝ) / 2) * σ ^ ((n : ℝ) / 2))) := by ring
        _ = Real.sqrt 2 * r / σ := by rw [e1, e2]; ring
    -- Step 6: r ‖d‖ / σ ≤ ‖x‖ r
    have hrd : Real.sqrt 2 * r / σ * ‖d‖ ≤ Real.sqrt 2 * ‖x‖ * r := by
      have h1 : (0 : ℝ) < 1 - r := by linarith
      have h1' : (0 : ℝ) < 1 + r := by linarith
      have h2 : (0 : ℝ) ≤ ‖x‖ := norm_nonneg _
      have heq : Real.sqrt 2 * r / σ * ‖d‖ = (Real.sqrt 2 * ‖x‖ * r) * (1 / (1 + r)) := by
        rw [hdn, hrσ]; field_simp
      rw [heq]
      have h4 : 1 / (1 + r) ≤ 1 := by rw [div_le_one h1']; linarith
      have h5 : (0 : ℝ) ≤ Real.sqrt 2 * ‖x‖ * r := by positivity
      exact mul_le_of_le_one_right h5 h4
    have hfinal : c * ‖d‖ * ((Real.pi / b) ^ ((n : ℝ) / 2)
          * (5 + 24 * (8 : ℝ) ^ ((n : ℝ) / 2)))
        ≤ Real.sqrt 2 * (5 + 24 * (8 : ℝ) ^ ((n : ℝ) / 2)) * ‖x‖ * r := by
      have hrw : c * ‖d‖ * ((Real.pi / b) ^ ((n : ℝ) / 2)
            * (5 + 24 * (8 : ℝ) ^ ((n : ℝ) / 2)))
          = (Real.sqrt 2 * r / σ * ‖d‖) * (5 + 24 * (8 : ℝ) ^ ((n : ℝ) / 2)) := by
        rw [← hcancel]; ring
      have hcoef : (0 : ℝ) ≤ 5 + 24 * (8 : ℝ) ^ ((n : ℝ) / 2) := by positivity
      rw [hrw]
      calc Real.sqrt 2 * r / σ * ‖d‖ * (5 + 24 * (8 : ℝ) ^ ((n : ℝ) / 2))
          ≤ Real.sqrt 2 * ‖x‖ * r * (5 + 24 * (8 : ℝ) ^ ((n : ℝ) / 2)) :=
            mul_le_mul_of_nonneg_right hrd hcoef
        _ = Real.sqrt 2 * (5 + 24 * (8 : ℝ) ^ ((n : ℝ) / 2)) * ‖x‖ * r := by ring
    exact le_trans hdiff hfinal
  · -- the fixed-s limit, by dominated convergence along `𝓝[>] 0`
    intro s hs
    have hslice := MehlerKernelSliceVanishing j x s hs
    set F : EuclideanSpace ℝ (Fin n) → ℝ := fun y =>
      Real.sqrt 2 * Real.exp (-s) * (y j - Real.exp (-s) * x j) / (1 - Real.exp (-2 * s))
        * (Real.pi ^ (-(n : ℝ) / 2) * (1 - Real.exp (-2 * s)) ^ (-(n : ℝ) / 2)
            * Real.exp (-‖Real.exp (-s) • x - y‖ ^ 2 / (1 - Real.exp (-2 * s)))) with hF
    have hIF : Integrable F volume := hslice.1
    have hzero : ∫ y, F y = 0 := hslice.2
    have hsplit : ∀ ε : ℝ, ∫ y in {y : EuclideanSpace ℝ (Fin n) | ε < ‖x - y‖}, F y
        = -∫ y in {y : EuclideanSpace ℝ (Fin n) | ε < ‖x - y‖}ᶜ, F y := by
      intro ε
      have h := integral_add_compl (hSmeas ε) hIF
      rw [hzero] at h
      linarith
    have hsing : volume ({x} : Set (EuclideanSpace ℝ (Fin n))) = 0 := by
      have hnt : Nontrivial (EuclideanSpace ℝ (Fin n)) := by
        have h : 0 < Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) := by
          rw [finrank_euclideanSpace_fin]; exact Fin.pos j
        exact Module.nontrivial_of_finrank_pos h
      exact measure_singleton x
    have hlim : Filter.Tendsto
        (fun ε : ℝ => ∫ y in {y : EuclideanSpace ℝ (Fin n) | ε < ‖x - y‖}ᶜ, F y)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
      have hind : ∀ ε : ℝ, ∫ y in {y : EuclideanSpace ℝ (Fin n) | ε < ‖x - y‖}ᶜ, F y
          = ∫ y, Set.indicator {y : EuclideanSpace ℝ (Fin n) | ε < ‖x - y‖}ᶜ F y := by
        intro ε
        rw [integral_indicator ((hSmeas ε).compl)]
      rw [show (fun ε : ℝ => ∫ y in {y : EuclideanSpace ℝ (Fin n) | ε < ‖x - y‖}ᶜ, F y)
          = fun ε : ℝ => ∫ y, Set.indicator {y : EuclideanSpace ℝ (Fin n) | ε < ‖x - y‖}ᶜ F y
        from funext hind]
      have hdct : Filter.Tendsto
          (fun ε : ℝ => ∫ y, Set.indicator {y : EuclideanSpace ℝ (Fin n) | ε < ‖x - y‖}ᶜ F y)
          (nhdsWithin 0 (Set.Ioi 0))
          (nhds (∫ _y : EuclideanSpace ℝ (Fin n), (0 : ℝ))) := by
        refine tendsto_integral_filter_of_dominated_convergence (fun y => |F y|) ?_ ?_ hIF.abs ?_
        · exact Filter.Eventually.of_forall fun ε =>
          hIF.aestronglyMeasurable.indicator ((hSmeas ε).compl)
        · refine Filter.Eventually.of_forall fun ε => Filter.Eventually.of_forall fun y => ?_
          rw [Real.norm_eq_abs]
          by_cases hy : y ∈ {y : EuclideanSpace ℝ (Fin n) | ε < ‖x - y‖}ᶜ
          · rw [Set.indicator_of_mem hy]
          · rw [Set.indicator_of_notMem hy, abs_zero]; exact abs_nonneg _
        · have hae : ∀ᵐ y ∂(volume : Measure (EuclideanSpace ℝ (Fin n))), y ≠ x := by
            rw [MeasureTheory.ae_iff]
            have hset : {y : EuclideanSpace ℝ (Fin n) | ¬ y ≠ x} = {x} := by
              ext y; simp
            rw [hset]; exact hsing
          filter_upwards [hae] with y hy
          have hyx : 0 < ‖x - y‖ := by
            rw [norm_pos_iff, sub_ne_zero]
            exact fun h => hy h.symm
          have hev : (fun ε : ℝ =>
                Set.indicator {y : EuclideanSpace ℝ (Fin n) | ε < ‖x - y‖}ᶜ F y)
              =ᶠ[nhdsWithin 0 (Set.Ioi 0)] fun _ => (0 : ℝ) := by
            have hmem : {ε : ℝ | ε < ‖x - y‖} ∈ nhdsWithin (0 : ℝ) (Set.Ioi 0) :=
              nhdsWithin_le_nhds (gt_mem_nhds hyx)
            filter_upwards [hmem] with ε hεy
            refine Set.indicator_of_notMem ?_ _
            simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, not_not]
            exact hεy
          exact Filter.Tendsto.congr' hev.symm tendsto_const_nhds
      simpa using hdct
    have hneg : Filter.Tendsto
        (fun ε : ℝ => -∫ y in {y : EuclideanSpace ℝ (Fin n) | ε < ‖x - y‖}ᶜ, F y)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
      have h := hlim.neg
      rwa [neg_zero] at h
    exact hneg.congr fun ε => (hsplit ε).symm
