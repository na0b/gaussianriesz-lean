module

public import GaussianRiesz.ComplexRieszL1Limit

@[expose] public section
open MeasureTheory
theorem ComplexL1Extension {n : ℕ} :
    ∃ T : Lp ℂ 1 (GaussMeasure n) →ₗ[ℂ]
        (EuclideanSpace ℝ (Fin n) →ₘ[GaussMeasure n] EuclideanSpace ℂ (Fin n)),
      (∀ v : Lp ℂ 2 (GaussMeasure n),
          T (ComplexToL1 v) = (ComplexRieszTransform v : EuclideanSpace ℝ (Fin n)
            →ₘ[GaussMeasure n] EuclideanSpace ℂ (Fin n)))
        ∧ ∀ (f : Lp ℂ 1 (GaussMeasure n)) (t : ℝ), 0 < t →
            ENNReal.ofReal t * GaussMeasure n {x | t < ‖T f x‖}
              ≤ ENNReal.ofReal ((8 / Real.pi) * ‖f‖) := by
  classical
  -- Step 1a: a limit in measure is unique up to a null set.  If `A_k → A` and
  -- `A_k → A'` in measure then for every `ε > 0` the set `{ε ≤ edist A A'}` is
  -- contained in `{ε/2 ≤ edist A_k A} ∪ {ε/2 ≤ edist A_k A'}`, whose measure
  -- tends to `0`; and `{A ≠ A'}` is the countable union of the sets
  -- `{(j : ℝ≥0∞)⁻¹ ≤ edist A A'}`.
  have huniq : ∀ (u : ℕ → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℂ (Fin n))
      (A A' : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℂ (Fin n)),
      TendstoInMeasure (GaussMeasure n) u Filter.atTop A →
      TendstoInMeasure (GaussMeasure n) u Filter.atTop A' →
      A =ᵐ[GaussMeasure n] A' := by
    intro u A A' h h'
    have key : ∀ ε : ENNReal, 0 < ε →
        GaussMeasure n {x | ε ≤ edist (A x) (A' x)} = 0 := by
      intro ε hε
      have hε2 : 0 < ε / 2 := ENNReal.div_pos hε.ne' (by norm_num)
      have hb : ∀ k : ℕ, GaussMeasure n {x | ε ≤ edist (A x) (A' x)}
          ≤ GaussMeasure n {x | ε / 2 ≤ edist (u k x) (A x)}
            + GaussMeasure n {x | ε / 2 ≤ edist (u k x) (A' x)} := by
        intro k
        refine (measure_mono ?_).trans (measure_union_le _ _)
        intro x hx
        by_contra hcon
        simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_le] at hcon
        have h1 : edist (A x) (A' x) ≤ edist (u k x) (A x) + edist (u k x) (A' x) := by
          rw [edist_comm (u k x) (A x)]
          exact edist_triangle _ _ _
        have h2 : edist (u k x) (A x) + edist (u k x) (A' x) < ε := by
          have h3 := ENNReal.add_lt_add hcon.1 hcon.2
          rwa [ENNReal.add_halves] at h3
        exact absurd hx (not_le.2 (lt_of_le_of_lt h1 h2))
      have htend := (h (ε / 2) hε2).add (h' (ε / 2) hε2)
      rw [add_zero] at htend
      exact nonpos_iff_eq_zero.mp (ge_of_tendsto htend (Filter.Eventually.of_forall hb))
    have hU : GaussMeasure n
        (⋃ j : ℕ, {x | ((j : ENNReal))⁻¹ ≤ edist (A x) (A' x)}) = 0 :=
      measure_iUnion_null fun j => key _ (ENNReal.inv_pos.2 (ENNReal.natCast_ne_top j))
    have hN : GaussMeasure n {x | A x ≠ A' x} = 0 := by
      refine measure_mono_null (fun x hx => ?_) hU
      obtain ⟨j, hj⟩ := ENNReal.exists_inv_nat_lt (edist_pos.2 hx).ne'
      exact Set.mem_iUnion.2 ⟨j, hj.le⟩
    exact ae_iff.mpr hN
  -- Step 1b: `T_ℂ f := g_f`, together with the sequence `(v^f_k)`.
  choose G V hV1 hV2 hV3 hV4 using fun f : Lp ℂ 1 (GaussMeasure n) => ComplexRieszL1Limit f
  -- Step 1c: property (⋆) determines `G f`.
  have hstar : ∀ (f : Lp ℂ 1 (GaussMeasure n)) (w : ℕ → Lp ℂ 2 (GaussMeasure n))
      (A : EuclideanSpace ℝ (Fin n) →ₘ[GaussMeasure n] EuclideanSpace ℂ (Fin n)),
      Filter.Tendsto (fun k => ComplexToL1 (w k)) Filter.atTop (nhds f) →
      TendstoInMeasure (GaussMeasure n)
          (fun k => (ComplexRieszTransform (w k) : EuclideanSpace ℝ (Fin n)
            → EuclideanSpace ℂ (Fin n))) Filter.atTop
          (A : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℂ (Fin n)) →
        G f = A :=
    fun f w A hw hA => AEEqFun.ext (huniq _ _ _ (hV4 f w hw) hA)
  -- the inclusion `ι_ℂ` is ℂ-linear, and its `L¹` norm is the integral of the modulus
  have hcoe : ∀ u : Lp ℂ 2 (GaussMeasure n),
      (ComplexToL1 u : EuclideanSpace ℝ (Fin n) → ℂ) =ᵐ[GaussMeasure n]
        (u : EuclideanSpace ℝ (Fin n) → ℂ) := by
    intro u
    rw [ComplexToL1]
    exact MemLp.coeFn_toLp (p := 1) ((Lp.memLp u).mono_exponent (by norm_num))
  have hCL1add : ∀ u w : Lp ℂ 2 (GaussMeasure n),
      ComplexToL1 (u + w) = ComplexToL1 u + ComplexToL1 w := by
    intro u w
    refine Lp.ext_iff.mpr ?_
    filter_upwards [hcoe (u + w), hcoe u, hcoe w, Lp.coeFn_add u w,
      Lp.coeFn_add (ComplexToL1 u) (ComplexToL1 w)] with x e1 e2 e3 e4 e5
    rw [e1, e4, e5, Pi.add_apply, Pi.add_apply, e2, e3]
  have hCL1smul : ∀ (c : ℂ) (u : Lp ℂ 2 (GaussMeasure n)),
      ComplexToL1 (c • u) = c • ComplexToL1 u := by
    intro c u
    refine Lp.ext_iff.mpr ?_
    filter_upwards [hcoe (c • u), hcoe u, Lp.coeFn_smul c u,
      Lp.coeFn_smul c (ComplexToL1 u)] with x e1 e2 e3 e4
    rw [e1, e3, e4, Pi.smul_apply, Pi.smul_apply, e2]
  have hCL1norm : ∀ u : Lp ℂ 2 (GaussMeasure n),
      ‖ComplexToL1 u‖ = ∫ x, ‖(u : EuclideanSpace ℝ (Fin n) → ℂ) x‖ ∂(GaussMeasure n) := by
    intro u
    rw [L1.norm_eq_integral_norm]
    refine integral_congr_ae ?_
    filter_upwards [hcoe u] with x hx
    rw [hx]
  -- Step 2: a.e. pointwise convergence of the transforms gives convergence in
  -- measure, so the vector operations are handled by `Tendsto.add` / `.const_smul`.
  have hmeasof : ∀ (w : ℕ → Lp ℂ 2 (GaussMeasure n))
      (A : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℂ (Fin n)),
      (∀ᵐ x ∂(GaussMeasure n), Filter.Tendsto
          (fun k => (ComplexRieszTransform (w k) : EuclideanSpace ℝ (Fin n)
            → EuclideanSpace ℂ (Fin n)) x) Filter.atTop (nhds (A x))) →
      TendstoInMeasure (GaussMeasure n)
        (fun k => (ComplexRieszTransform (w k) : EuclideanSpace ℝ (Fin n)
          → EuclideanSpace ℂ (Fin n))) Filter.atTop A :=
    fun w A h => tendstoInMeasure_of_tendsto_ae (fun k => Lp.aestronglyMeasurable _) h
  have hCRTadd := (ComplexRieszTransformLinear (n := n)).1
  have hCRTsmul := (ComplexRieszTransformLinear (n := n)).2.1
  -- Step 3: ℂ-linearity of `G`.
  have hadd : ∀ f h : Lp ℂ 1 (GaussMeasure n), G (f + h) = G f + G h := by
    intro f h
    refine hstar (f + h) (fun k => V f k + V h k) (G f + G h) ?_ (hmeasof _ _ ?_)
    · simp only [hCL1add]
      exact (hV2 f).add (hV2 h)
    · have hpt : ∀ᵐ x ∂(GaussMeasure n), ∀ k,
          (ComplexRieszTransform (V f k + V h k) : EuclideanSpace ℝ (Fin n)
            → EuclideanSpace ℂ (Fin n)) x
            = (ComplexRieszTransform (V f k) : EuclideanSpace ℝ (Fin n)
                → EuclideanSpace ℂ (Fin n)) x
              + (ComplexRieszTransform (V h k) : EuclideanSpace ℝ (Fin n)
                → EuclideanSpace ℂ (Fin n)) x := by
        refine ae_all_iff.2 fun k => ?_
        filter_upwards [Lp.coeFn_add (ComplexRieszTransform (V f k))
          (ComplexRieszTransform (V h k))] with x e
        rw [hCRTadd (V f k) (V h k), e, Pi.add_apply]
      filter_upwards [hV3 f, hV3 h, hpt, AEEqFun.coeFn_add (G f) (G h)] with x e1 e2 e3 e4
      rw [e4, Pi.add_apply]
      exact Filter.Tendsto.congr (fun k => (e3 k).symm) (e1.add e2)
  have hsmul : ∀ (c : ℂ) (f : Lp ℂ 1 (GaussMeasure n)), G (c • f) = c • G f := by
    intro c f
    refine hstar (c • f) (fun k => c • V f k) (c • G f) ?_ (hmeasof _ _ ?_)
    · simp only [hCL1smul]
      exact (hV2 f).const_smul c
    · have hpt : ∀ᵐ x ∂(GaussMeasure n), ∀ k,
          (ComplexRieszTransform (c • V f k) : EuclideanSpace ℝ (Fin n)
            → EuclideanSpace ℂ (Fin n)) x
            = c • (ComplexRieszTransform (V f k) : EuclideanSpace ℝ (Fin n)
                → EuclideanSpace ℂ (Fin n)) x := by
        refine ae_all_iff.2 fun k => ?_
        filter_upwards [Lp.coeFn_smul c (ComplexRieszTransform (V f k))] with x e
        rw [hCRTsmul c (V f k), e, Pi.smul_apply]
      filter_upwards [hV3 f, hpt, AEEqFun.coeFn_smul c (G f)] with x e1 e3 e4
      rw [e4, Pi.smul_apply]
      exact Filter.Tendsto.congr (fun k => (e3 k).symm) (e1.const_smul c)
  refine ⟨{ toFun := G, map_add' := hadd, map_smul' := hsmul }, ?_, ?_⟩
  · -- Step 4: clause (1), agreement on `L²`, via the constant sequence
    intro v
    simp only [LinearMap.coe_mk, AddHom.coe_mk]
    exact hstar (ComplexToL1 v) (fun _ => v) _ tendsto_const_nhds
      (hmeasof (fun _ => v) _ (Filter.Eventually.of_forall fun x => tendsto_const_nhds))
  · -- Step 5: clause (2), the weak bound, by Fatou on the level-set indicators
    intro f t ht
    simp only [LinearMap.coe_mk, AddHom.coe_mk]
    have hofne0 : ENNReal.ofReal t ≠ 0 := by
      simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]
      exact ht
    obtain ⟨S, hS⟩ : ∃ S : ℕ → Set (EuclideanSpace ℝ (Fin n)),
        ∀ k, S k = {x | t < ‖(ComplexRieszTransform (V f k) : EuclideanSpace ℝ (Fin n)
          → EuclideanSpace ℂ (Fin n)) x‖} := ⟨_, fun _ => rfl⟩
    have hSnull : ∀ k, NullMeasurableSet (S k) (GaussMeasure n) := by
      intro k
      rw [hS k]
      exact nullMeasurableSet_lt aemeasurable_const
        (Lp.aestronglyMeasurable _).norm.aemeasurable
    have hSg : NullMeasurableSet
        {x | t < ‖(G f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℂ (Fin n)) x‖}
        (GaussMeasure n) :=
      nullMeasurableSet_lt aemeasurable_const
        (AEEqFun.aestronglyMeasurable (G f)).norm.aemeasurable
    have hfatou : GaussMeasure n
          {x | t < ‖(G f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℂ (Fin n)) x‖}
        ≤ Filter.liminf (fun k => GaussMeasure n (S k)) Filter.atTop := by
      have hind : ∀ᵐ x ∂(GaussMeasure n),
          Set.indicator {x | t < ‖(G f : EuclideanSpace ℝ (Fin n)
              → EuclideanSpace ℂ (Fin n)) x‖} (1 : EuclideanSpace ℝ (Fin n) → ENNReal) x
            ≤ Filter.liminf (fun k => Set.indicator (S k)
                (1 : EuclideanSpace ℝ (Fin n) → ENNReal) x) Filter.atTop := by
        filter_upwards [hV3 f] with x hx
        by_cases hmem : x ∈ {y | t < ‖(G f : EuclideanSpace ℝ (Fin n)
            → EuclideanSpace ℂ (Fin n)) y‖}
        · have hmem' : t < ‖(G f : EuclideanSpace ℝ (Fin n)
              → EuclideanSpace ℂ (Fin n)) x‖ := hmem
          rw [Set.indicator_of_mem hmem]
          refine le_trans (le_of_eq (Pi.one_apply x)) ?_
          have hev : ∀ᶠ k in Filter.atTop,
              (1 : ENNReal) ≤ Set.indicator (S k)
                (1 : EuclideanSpace ℝ (Fin n) → ENNReal) x := by
            filter_upwards [hx.norm.eventually_const_lt hmem'] with k hk
            have hxk : x ∈ S k := by rw [hS k]; exact hk
            rw [Set.indicator_of_mem hxk]
            exact le_rfl
          calc (1 : ENNReal)
              = Filter.liminf (fun _ : ℕ => (1 : ENNReal)) Filter.atTop :=
                (Filter.liminf_const _).symm
            _ ≤ _ := Filter.liminf_le_liminf hev
        · rw [Set.indicator_of_notMem hmem]
          simp
      calc GaussMeasure n
            {x | t < ‖(G f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℂ (Fin n)) x‖}
          = ∫⁻ x, Set.indicator {x | t < ‖(G f : EuclideanSpace ℝ (Fin n)
              → EuclideanSpace ℂ (Fin n)) x‖}
              (1 : EuclideanSpace ℝ (Fin n) → ENNReal) x ∂(GaussMeasure n) :=
            (lintegral_indicator_one₀ hSg).symm
        _ ≤ ∫⁻ x, Filter.liminf (fun k => Set.indicator (S k)
              (1 : EuclideanSpace ℝ (Fin n) → ENNReal) x) Filter.atTop ∂(GaussMeasure n) :=
            lintegral_mono_ae hind
        _ ≤ Filter.liminf (fun k => ∫⁻ x, Set.indicator (S k)
              (1 : EuclideanSpace ℝ (Fin n) → ENNReal) x ∂(GaussMeasure n)) Filter.atTop :=
            lintegral_liminf_le' fun k => measurable_const.aemeasurable.indicator₀ (hSnull k)
        _ = Filter.liminf (fun k => GaussMeasure n (S k)) Filter.atTop := by
            refine congrArg (fun u => Filter.liminf u Filter.atTop) ?_
            funext k
            exact lintegral_indicator_one₀ (hSnull k)
    have hbd : ∀ k, GaussMeasure n (S k)
        ≤ ENNReal.ofReal ((8 / Real.pi) * ‖f‖) / ENNReal.ofReal t := by
      intro k
      have hmain := ComplexMainBound (V f k) t ht
      have h2 : ∫ x, ‖(V f k : EuclideanSpace ℝ (Fin n) → ℂ) x‖ ∂(GaussMeasure n) ≤ ‖f‖ := by
        rw [← hCL1norm (V f k)]
        exact hV1 f k
      have h3 : ENNReal.ofReal ((8 / Real.pi)
            * ∫ x, ‖(V f k : EuclideanSpace ℝ (Fin n) → ℂ) x‖ ∂(GaussMeasure n))
          ≤ ENNReal.ofReal ((8 / Real.pi) * ‖f‖) :=
        ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left h2 (by positivity))
      have hfin : GaussMeasure n {x | t < ‖(ComplexRieszTransform (V f k) :
            EuclideanSpace ℝ (Fin n) → EuclideanSpace ℂ (Fin n)) x‖}
          * ENNReal.ofReal t ≤ ENNReal.ofReal ((8 / Real.pi) * ‖f‖) := by
        rw [mul_comm]
        exact hmain.trans h3
      rw [hS k, ENNReal.le_div_iff_mul_le (Or.inl hofne0) (Or.inl ENNReal.ofReal_ne_top)]
      exact hfin
    have hlim : Filter.liminf (fun k => GaussMeasure n (S k)) Filter.atTop
        ≤ ENNReal.ofReal ((8 / Real.pi) * ‖f‖) / ENNReal.ofReal t := by
      calc Filter.liminf (fun k => GaussMeasure n (S k)) Filter.atTop
          ≤ Filter.liminf (fun _ : ℕ =>
              ENNReal.ofReal ((8 / Real.pi) * ‖f‖) / ENNReal.ofReal t) Filter.atTop :=
            Filter.liminf_le_liminf (Filter.Eventually.of_forall hbd)
        _ = _ := Filter.liminf_const _
    rw [mul_comm, ← ENNReal.le_div_iff_mul_le (Or.inl hofne0) (Or.inl ENNReal.ofReal_ne_top)]
    exact hfatou.trans hlim
