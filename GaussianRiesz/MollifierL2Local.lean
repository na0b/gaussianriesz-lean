module

public import GaussianRiesz.Preamble
public import GaussianRiesz.YoungL2Contraction

@[expose] public section
open MeasureTheory
open scoped ENNReal
theorem MollifierL2Local {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (hf : ∀ K : Set (EuclideanSpace ℝ (Fin n)), IsCompact K →
      MemLp f 2 (volume.restrict K))
    (ρ : ℝ → EuclideanSpace ℝ (Fin n) → ℝ)
    (hsmooth : ∀ ε : ℝ, 0 < ε → ContDiff ℝ (⊤ : ℕ∞) (ρ ε))
    (hsupport : ∀ ε : ℝ, 0 < ε → Function.support (ρ ε) ⊆ Metric.closedBall 0 ε)
    (hnonneg : ∀ ε : ℝ, 0 < ε → ∀ x : EuclideanSpace ℝ (Fin n), 0 ≤ ρ ε x)
    (hmass : ∀ ε : ℝ, 0 < ε → ∫ x, ρ ε x = 1)
    (K : Set (EuclideanSpace ℝ (Fin n))) (hK : IsCompact K) :
    Filter.Tendsto
        (fun ε : ℝ => eLpNorm
          (fun x => convolution (ρ ε) f (ContinuousLinearMap.lsmul ℝ ℝ) volume x - f x)
          2 (volume.restrict K))
        (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
  -- Step 2: the continuous compactly supported case, via the sup-norm estimate.
  have contCase : ∀ g : EuclideanSpace ℝ (Fin n) → ℝ, Continuous g → HasCompactSupport g →
      ∀ b : ℝ, 0 < b →
      ∀ᶠ ε in nhdsWithin (0:ℝ) (Set.Ioi 0),
        eLpNorm (fun x => convolution (ρ ε) g (ContinuousLinearMap.lsmul ℝ ℝ) volume x - g x) 2
          (volume.restrict K) ≤ ENNReal.ofReal b := by
    intro g hgc hgs b hb
    have hKt : ((volume : Measure (EuclideanSpace ℝ (Fin n))) K) ^ ((2:ℝ≥0∞).toReal⁻¹) ≠ ⊤ :=
      ENNReal.rpow_ne_top_of_nonneg (by norm_num) (hK.measure_lt_top).ne
    set A : ℝ := (((volume : Measure (EuclideanSpace ℝ (Fin n))) K) ^ ((2:ℝ≥0∞).toReal⁻¹)).toReal
      with hAdef
    have hA0 : 0 ≤ A := ENNReal.toReal_nonneg
    set c : ℝ := b / (A + 1) with hcdef
    have hc0 : 0 < c := div_pos hb (by linarith)
    have hAc : A * c ≤ b := by
      rw [hcdef]
      rw [mul_div_assoc'] at *
      rw [div_le_iff₀ (by linarith : (0:ℝ) < A + 1)]
      nlinarith
    have hunif : UniformContinuous g :=
      hgc.uniformContinuous_of_tendsto_cocompact (HasCompactSupport.is_zero_at_infty hgs)
    obtain ⟨δ, hδ0, hδ⟩ := Metric.uniformContinuous_iff.mp hunif c hc0
    filter_upwards [Ioo_mem_nhdsGT (show (0:ℝ) < δ/2 by positivity)] with ε hε
    obtain ⟨hε0, hεδ⟩ := hε
    have hsupp' : Function.support (ρ ε) ⊆ Metric.ball 0 (δ/2) :=
      (hsupport ε hε0).trans (Metric.closedBall_subset_ball hεδ)
    have hbound : ∀ x₀ : EuclideanSpace ℝ (Fin n),
        ‖convolution (ρ ε) g (ContinuousLinearMap.lsmul ℝ ℝ) volume x₀ - g x₀‖ ≤ c := by
      intro x₀
      have hb2 := dist_convolution_le (x₀ := x₀) (z₀ := g x₀) hc0.le hsupp'
        (hnonneg ε hε0) (hmass ε hε0) hgc.aestronglyMeasurable (fun x hx => le_of_lt (hδ ?_))
      · rwa [dist_eq_norm] at hb2
      · rw [Metric.mem_ball] at hx
        linarith
    calc eLpNorm (fun x => convolution (ρ ε) g (ContinuousLinearMap.lsmul ℝ ℝ) volume x - g x) 2
          (volume.restrict K)
        ≤ ((volume.restrict K) Set.univ) ^ ((2:ℝ≥0∞).toReal⁻¹) * ENNReal.ofReal c :=
          eLpNorm_le_of_ae_bound
            ((((hsmooth ε hε0).continuous.aestronglyMeasurable.convolution_integrand
              (ContinuousLinearMap.lsmul ℝ ℝ) hgc.aestronglyMeasurable).integral_prod_right').sub
              hgc.aestronglyMeasurable).restrict
            (Filter.Eventually.of_forall hbound)
      _ = ENNReal.ofReal A * ENNReal.ofReal c := by
          rw [Measure.restrict_apply_univ, hAdef, ENNReal.ofReal_toReal hKt]
      _ = ENNReal.ofReal (A * c) := (ENNReal.ofReal_mul hA0).symm
      _ ≤ ENNReal.ofReal b := ENNReal.ofReal_le_ofReal hAc

  -- Steps 0 and 3: the 3-ε assembly.
  classical
  have hKm : MeasurableSet K := hK.measurableSet
  have hρc : ∀ ε : ℝ, 0 < ε → Continuous (ρ ε) := fun ε hε => (hsmooth ε hε).continuous
  have hρcs : ∀ ε : ℝ, 0 < ε → HasCompactSupport (ρ ε) := by
    intro ε hε
    refine HasCompactSupport.intro
      (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin n)) ε) ?_
    intro x hx
    by_contra hne
    exact hx (hsupport ε hε hne)
  have hρint : ∀ ε : ℝ, 0 < ε → Integrable (ρ ε) volume := fun ε hε =>
    (hρc ε hε).integrable_of_hasCompactSupport (hρcs ε hε)
  -- the thickened compact set and the truncation of `f`
  have hK2c : IsCompact (Metric.cthickening 2 K) := hK.cthickening
  have hK2m : MeasurableSet (Metric.cthickening 2 K) := Metric.isClosed_cthickening.measurableSet
  have hf1 : MemLp (Set.indicator (Metric.cthickening 2 K) f) 2
      (volume : Measure (EuclideanSpace ℝ (Fin n))) :=
    (memLp_indicator_iff_restrict hK2m).2 (hf _ hK2c)
  rw [ENNReal.tendsto_nhds_zero]
  intro η hη
  obtain ⟨b, hb0, hbη⟩ : ∃ b : ℝ, 0 < b ∧ ENNReal.ofReal b ≤ η := by
    by_cases htop : η = ⊤
    · exact ⟨1, one_pos, by rw [htop]; exact le_top⟩
    · exact ⟨η.toReal, ENNReal.toReal_pos hη.ne' htop, by rw [ENNReal.ofReal_toReal htop]⟩
  have hb3 : (0:ℝ) < b / 3 := by positivity
  obtain ⟨g, hgs, hgsub, hgc, hgLp⟩ :=
    MemLp.exists_hasCompactSupport_eLpNorm_sub_le (p := 2) (by norm_num) hf1
      (ε := ENNReal.ofReal (b/3))
      (by simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]; exact hb3)
  have hfg : MemLp (Set.indicator (Metric.cthickening 2 K) f - g) 2
      (volume : Measure (EuclideanSpace ℝ (Fin n))) := hf1.sub hgLp
  filter_upwards [contCase g hgc hgs (b/3) hb3,
    Ioo_mem_nhdsGT (show (0:ℝ) < 1 by norm_num)] with ε hεB hε
  obtain ⟨hε0, hε1⟩ := hε
  -- name the three pieces so the assembly does not re-elaborate them
  obtain ⟨A, hAdef⟩ : ∃ A : EuclideanSpace ℝ (Fin n) → ℝ, A = fun x =>
      convolution (ρ ε) (Set.indicator (Metric.cthickening 2 K) f - g)
        (ContinuousLinearMap.lsmul ℝ ℝ) volume x := ⟨_, rfl⟩
  obtain ⟨B, hBdef⟩ : ∃ B : EuclideanSpace ℝ (Fin n) → ℝ, B = fun x =>
      convolution (ρ ε) g (ContinuousLinearMap.lsmul ℝ ℝ) volume x - g x := ⟨_, rfl⟩
  obtain ⟨C, hCdef⟩ : ∃ C : EuclideanSpace ℝ (Fin n) → ℝ, C = fun x =>
      g x - Set.indicator (Metric.cthickening 2 K) f x := ⟨_, rfl⟩
  -- the pointwise decomposition on `K`
  have hptid : ∀ x ∈ K,
      convolution (ρ ε) f (ContinuousLinearMap.lsmul ℝ ℝ) volume x - f x
        = A x + B x + C x := by
    intro x hx
    simp only [hAdef, hBdef, hCdef]
    have htrunc : convolution (ρ ε) f (ContinuousLinearMap.lsmul ℝ ℝ) volume x
        = convolution (ρ ε) (Set.indicator (Metric.cthickening 2 K) f)
            (ContinuousLinearMap.lsmul ℝ ℝ) volume x := by
      rw [convolution_def, convolution_def]
      refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
      by_cases ht : ρ ε t = 0
      · simp only [ContinuousLinearMap.lsmul_apply, ht, zero_smul]
      · have htb : t ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) ε := hsupport ε hε0 ht
        have hxt : x - t ∈ Metric.cthickening 2 K := by
          refine Metric.mem_cthickening_of_dist_le _ x 2 K hx ?_
          rw [Metric.mem_closedBall, dist_zero_right] at htb
          rw [dist_eq_norm]
          simp only [sub_sub_cancel_left, norm_neg]
          linarith
        simp only [ContinuousLinearMap.lsmul_apply, Set.indicator_of_mem hxt]
    have hex1 : ConvolutionExistsAt (ρ ε) (Set.indicator (Metric.cthickening 2 K) f - g) x
        (ContinuousLinearMap.lsmul ℝ ℝ) volume :=
      HasCompactSupport.convolutionExists_left _ (hρcs ε hε0) (hρc ε hε0)
        (hfg.locallyIntegrable (by norm_num)) x
    have hex2 : ConvolutionExistsAt (ρ ε) g x (ContinuousLinearMap.lsmul ℝ ℝ) volume :=
      HasCompactSupport.convolutionExists_left _ (hρcs ε hε0) (hρc ε hε0)
        (hgLp.locallyIntegrable (by norm_num)) x
    have hsplit : convolution (ρ ε) (Set.indicator (Metric.cthickening 2 K) f)
          (ContinuousLinearMap.lsmul ℝ ℝ) volume x
        = convolution (ρ ε) (Set.indicator (Metric.cthickening 2 K) f - g)
              (ContinuousLinearMap.lsmul ℝ ℝ) volume x
            + convolution (ρ ε) g (ContinuousLinearMap.lsmul ℝ ℝ) volume x := by
      have hd := hex1.distrib_add hex2
      rwa [sub_add_cancel] at hd
    have hfx : f x = Set.indicator (Metric.cthickening 2 K) f x :=
      (Set.indicator_of_mem (Metric.self_subset_cthickening K hx) f).symm
    rw [htrunc, hsplit, hfx]
    ring
  -- continuity and measurability of the three pieces
  have hcA : Continuous A := by
    rw [hAdef]
    exact HasCompactSupport.continuous_convolution_left _ (hρcs ε hε0) (hρc ε hε0)
      (hfg.locallyIntegrable (by norm_num))
  have hcB : Continuous B := by
    rw [hBdef]
    exact (HasCompactSupport.continuous_convolution_left _ (hρcs ε hε0) (hρc ε hε0)
      (hgLp.locallyIntegrable (by norm_num))).sub hgc
  have hmC : AEStronglyMeasurable C
      ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict K) := by
    rw [hCdef]
    exact (hgc.aestronglyMeasurable.sub hf1.aestronglyMeasurable).restrict
  -- the three bounds
  have hA : eLpNorm A 2 (volume.restrict K) ≤ ENNReal.ofReal (b/3) := by
    rw [hAdef]
    refine le_trans (eLpNorm_mono_measure _ Measure.restrict_le_self) ?_
    exact le_trans (YoungL2Contraction (ρ ε) (hρc ε hε0).measurable (hnonneg ε hε0)
      (hρint ε hε0) (hmass ε hε0) _ hfg.aestronglyMeasurable) hgsub
  have hB : eLpNorm B 2 (volume.restrict K) ≤ ENNReal.ofReal (b/3) := by
    rw [hBdef]; exact hεB
  have hC : eLpNorm C 2 (volume.restrict K) ≤ ENNReal.ofReal (b/3) := by
    rw [hCdef]
    refine le_trans (eLpNorm_mono_measure _ Measure.restrict_le_self) ?_
    rw [show (fun x => g x - Set.indicator (Metric.cthickening 2 K) f x)
        = g - Set.indicator (Metric.cthickening 2 K) f from rfl,
      eLpNorm_sub_comm]
    exact hgsub
  -- assemble
  rw [eLpNorm_congr_ae (ae_restrict_of_forall_mem hKm hptid)]
  have hAB : eLpNorm (fun x => A x + B x) 2 (volume.restrict K)
      ≤ ENNReal.ofReal (b/3) + ENNReal.ofReal (b/3) :=
    le_trans (eLpNorm_add_le (by norm_num)) (add_le_add hA hB)
  refine le_trans (eLpNorm_add_le (by norm_num)) ?_
  refine le_trans (add_le_add hAB hC) ?_
  rw [← ENNReal.ofReal_add hb3.le hb3.le, ← ENNReal.ofReal_add (by positivity) hb3.le]
  refine le_trans (ENNReal.ofReal_le_ofReal ?_) hbη
  linarith
