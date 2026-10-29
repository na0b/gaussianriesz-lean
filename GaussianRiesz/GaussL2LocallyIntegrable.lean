module

public import GaussianRiesz.GaussIsProb

@[expose] public section
open MeasureTheory
open scoped ENNReal
theorem GaussL2LocallyIntegrable {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (hf : MemLp f 2 (GaussMeasure n)) :
    LocallyIntegrable f volume
      ∧ (∀ K : Set (EuclideanSpace ℝ (Fin n)), IsCompact K →
          MemLp f 2 (volume.restrict K))
      ∧ (∀ K : Set (EuclideanSpace ℝ (Fin n)), IsCompact K →
          ∃ C : ℝ, 0 ≤ C ∧ ∀ g : EuclideanSpace ℝ (Fin n) → ℝ,
            MemLp g 2 (GaussMeasure n) →
              IntegrableOn g K volume
                ∧ ∫ x in K, |g x| ≤ C * (eLpNorm g 2 (GaussMeasure n)).toReal) := by
  classical
  -- (A) On every compact set the Gaussian density is bounded below by a positive constant,
  -- so Lebesgue measure restricted to that set is dominated by a multiple of `GaussMeasure n`.
  have hdom : ∀ K : Set (EuclideanSpace ℝ (Fin n)), IsCompact K →
      ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ⊤ ∧ volume.restrict K ≤ c • GaussMeasure n := by
    intro K hK
    rcases K.eq_empty_or_nonempty with rfl | hne
    · refine ⟨1, one_ne_zero, ENNReal.one_ne_top, ?_⟩
      rw [Measure.restrict_empty]
      exact Measure.zero_le _
    · -- the extreme value theorem for the continuous, strictly positive density
      have hmin : ∃ c : ℝ, 0 < c ∧ ∀ x ∈ K,
          c ≤ Real.pi ^ (-(n : ℝ) / 2) * Real.exp (-‖x‖ ^ 2) := by
        have hcont : ContinuousOn (fun x : EuclideanSpace ℝ (Fin n) =>
            Real.pi ^ (-(n : ℝ) / 2) * Real.exp (-‖x‖ ^ 2)) K := by fun_prop
        obtain ⟨x₀, hx₀K, hm⟩ := hK.exists_isMinOn hne hcont
        refine ⟨Real.pi ^ (-(n : ℝ) / 2) * Real.exp (-‖x₀‖ ^ 2), ?_, fun x hx => hm hx⟩
        have : (0:ℝ) < Real.pi ^ (-(n : ℝ) / 2) := Real.rpow_pos_of_pos Real.pi_pos _
        positivity
      obtain ⟨c, hc0, hcle⟩ := hmin
      have hz : ENNReal.ofReal c ≠ 0 := by
        simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]
        exact hc0
      have ht : ENNReal.ofReal c ≠ ⊤ := ENNReal.ofReal_ne_top
      refine ⟨(ENNReal.ofReal c)⁻¹, ENNReal.inv_ne_zero.2 ht, ENNReal.inv_ne_top.2 hz, ?_⟩
      have hKm : MeasurableSet K := hK.measurableSet
      have step1 : (ENNReal.ofReal c) • (volume.restrict K) ≤ GaussMeasure n := by
        calc (ENNReal.ofReal c) • (volume.restrict K)
            = (volume.restrict K).withDensity (fun _ => ENNReal.ofReal c) :=
              (withDensity_const _).symm
          _ ≤ (volume.restrict K).withDensity
                (fun x => ENNReal.ofReal (Real.pi ^ (-(n : ℝ) / 2) * Real.exp (-‖x‖ ^ 2))) := by
              refine withDensity_mono ?_
              rw [Filter.EventuallyLE, ae_restrict_iff' hKm]
              exact Filter.Eventually.of_forall fun x hx =>
                ENNReal.ofReal_le_ofReal (hcle x hx)
          _ = (GaussMeasure n).restrict K := by
              rw [GaussMeasure, restrict_withDensity hKm]
          _ ≤ GaussMeasure n := Measure.restrict_le_self
      refine Measure.le_iff.2 fun s hs => ?_
      have h2 := Measure.le_iff.1 step1 s hs
      simp only [Measure.smul_apply, smul_eq_mul] at h2 ⊢
      calc (volume.restrict K) s
          = (ENNReal.ofReal c)⁻¹ * ((ENNReal.ofReal c) * (volume.restrict K) s) := by
            rw [← mul_assoc, ENNReal.inv_mul_cancel hz ht, one_mul]
        _ ≤ (ENNReal.ofReal c)⁻¹ * GaussMeasure n s := mul_le_mul_right h2 _
  -- (B) consequently every `L²(γ_n)` function is in `L²` of Lebesgue measure on a compact set
  have key2 : ∀ K : Set (EuclideanSpace ℝ (Fin n)), IsCompact K →
      ∀ g : EuclideanSpace ℝ (Fin n) → ℝ, MemLp g 2 (GaussMeasure n) →
        MemLp g 2 (volume.restrict K) := by
    intro K hK g hg
    obtain ⟨c, hc0, hct, hle⟩ := hdom K hK
    exact MemLp.mono_measure hle (hg.smul_measure hct)
  -- (C) the quantitative `L¹(K, λ)` bound, with a constant depending only on `K` and `n`
  have key3 : ∀ K : Set (EuclideanSpace ℝ (Fin n)), IsCompact K →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ g : EuclideanSpace ℝ (Fin n) → ℝ, MemLp g 2 (GaussMeasure n) →
        IntegrableOn g K volume
          ∧ ∫ x in K, |g x| ≤ C * (eLpNorm g 2 (GaussMeasure n)).toReal := by
    intro K hK
    obtain ⟨c, hc0, hct, hle⟩ := hdom K hK
    have hKt : volume K ≠ ⊤ := (hK.measure_lt_top).ne
    have hfin : IsFiniteMeasure (volume.restrict K) :=
      ⟨by rw [Measure.restrict_apply_univ]; exact hK.measure_lt_top⟩
    refine ⟨(c ^ ((2:ℝ)⁻¹) * volume K ^ ((2:ℝ)⁻¹)).toReal, ENNReal.toReal_nonneg, ?_⟩
    intro g hg
    have hmem : MemLp g 2 (volume.restrict K) := key2 K hK g hg
    have hint : IntegrableOn g K volume := hmem.integrable (by norm_num)
    refine ⟨hint, ?_⟩
    have e1 : eLpNorm g 1 (volume.restrict K)
        ≤ eLpNorm g 2 (volume.restrict K) * (volume.restrict K) Set.univ ^
            (1/(1:ℝ≥0∞).toReal - 1/(2:ℝ≥0∞).toReal) :=
      eLpNorm_le_eLpNorm_mul_rpow_measure_univ (by norm_num) hmem.aestronglyMeasurable
    have e2 : eLpNorm g 2 (volume.restrict K)
        ≤ c ^ ((2:ℝ)⁻¹) * eLpNorm g 2 (GaussMeasure n) := by
      refine (eLpNorm_mono_measure g hle).trans ?_
      rw [eLpNorm_smul_measure_of_ne_top (by norm_num) g c hg.aestronglyMeasurable]
      norm_num
    have hQ : eLpNorm g 1 (volume.restrict K)
        ≤ (c ^ ((2:ℝ)⁻¹) * volume K ^ ((2:ℝ)⁻¹)) * eLpNorm g 2 (GaussMeasure n) := by
      calc eLpNorm g 1 (volume.restrict K)
          ≤ eLpNorm g 2 (volume.restrict K) * (volume K) ^ ((2:ℝ)⁻¹) := by
            refine e1.trans_eq ?_
            rw [Measure.restrict_apply_univ]
            norm_num
        _ ≤ (c ^ ((2:ℝ)⁻¹) * eLpNorm g 2 (GaussMeasure n)) * (volume K) ^ ((2:ℝ)⁻¹) :=
            mul_le_mul_left e2 _
        _ = (c ^ ((2:ℝ)⁻¹) * volume K ^ ((2:ℝ)⁻¹)) * eLpNorm g 2 (GaussMeasure n) := by
            ring
    have hfin1 : (c ^ ((2:ℝ)⁻¹) * volume K ^ ((2:ℝ)⁻¹))
        * eLpNorm g 2 (GaussMeasure n) ≠ ⊤ := by
      refine ENNReal.mul_ne_top (ENNReal.mul_ne_top ?_ ?_) hg.eLpNorm_ne_top
      · exact ENNReal.rpow_ne_top_of_nonneg (by norm_num) hct
      · exact ENNReal.rpow_ne_top_of_nonneg (by norm_num) hKt
    have h2 : ENNReal.ofReal (∫ x in K, |g x|) = eLpNorm g 1 (volume.restrict K) := by
      rw [eLpNorm_one_eq_lintegral_enorm hmem.aestronglyMeasurable]
      simpa only [Real.norm_eq_abs] using ofReal_integral_norm_eq_lintegral_enorm hint
    have h3 : ∫ x in K, |g x| = (eLpNorm g 1 (volume.restrict K)).toReal := by
      rw [← h2, ENNReal.toReal_ofReal (integral_nonneg (fun x => abs_nonneg _))]
    rw [h3]
    refine (ENNReal.toReal_mono hfin1 hQ).trans_eq ?_
    rw [ENNReal.toReal_mul]
  refine ⟨?_, fun K hK => key2 K hK f hf, key3⟩
  rw [locallyIntegrable_iff]
  intro K hK
  obtain ⟨C, hC0, hCg⟩ := key3 K hK
  exact (hCg f hf).1
