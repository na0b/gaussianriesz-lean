import GaussianRiesz.HasGaussWeakGrad
import GaussianRiesz.GaussL2LocallyIntegrable
import GaussianRiesz.MollifierL2Local
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import GaussianRiesz.ConvolutionFDerivOfWeakGrad
import GaussianRiesz.CompIntegrationByParts
import GaussianRiesz.NormIntegralLeOfProductDomination
open MeasureTheory
open scoped ENNReal
theorem GaussWeakGradChainRule {n : ℕ} (q q' : ℝ → ℝ) (Lq : ℝ) (hLq : 0 ≤ Lq)
    (hq : ∀ t, HasDerivAt q (q' t) t) (hq'c : Continuous q')
    (hq'b : ∀ t, |q' t| ≤ 1) (hqLip : ∀ s t, |q s - q t| ≤ |s - t|)
    (hq'Lip : ∀ s t, |q' s - q' t| ≤ Lq * |s - t|) (hq0 : q 0 = 0)
    (U : EuclideanSpace ℝ (Fin n) → ℝ)
    (G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (hUL2 : MemLp U 2 (GaussMeasure n))
    (hGL2 : ∀ i : Fin n, MemLp (fun x => G x i) 2 (GaussMeasure n))
    (hwg : HasGaussWeakGrad U G) :
    HasGaussWeakGrad (fun x => q (U x)) (fun x => q' (U x) • G x) := by
  -- A mollifier family: smooth, nonnegative, supported in `B(0,ε)`, of unit mass.
  have bumpFamily : ∃ ρ : ℝ → EuclideanSpace ℝ (Fin n) → ℝ,
      ∀ ε : ℝ, 0 < ε →
        ContDiff ℝ (⊤ : ℕ∞) (ρ ε) ∧ HasCompactSupport (ρ ε)
          ∧ Function.support (ρ ε) ⊆ Metric.closedBall 0 ε
          ∧ (∀ x, 0 ≤ ρ ε x) ∧ ∫ x, ρ ε x = 1 := by
    classical
    have hex : ∀ ε : ℝ, ∃ r : EuclideanSpace ℝ (Fin n) → ℝ, 0 < ε →
        (ContDiff ℝ (⊤ : ℕ∞) r ∧ HasCompactSupport r
          ∧ Function.support r ⊆ Metric.closedBall 0 ε
          ∧ (∀ x, 0 ≤ r x) ∧ ∫ x, r x = 1) := by
      intro ε
      by_cases hε : 0 < ε
      · set b : ContDiffBump (0 : EuclideanSpace ℝ (Fin n)) :=
          ⟨ε / 2, ε, by positivity, by linarith⟩ with hbdef
        refine ⟨b.normed (volume : Measure (EuclideanSpace ℝ (Fin n))), fun _ =>
          ⟨b.contDiff_normed, b.hasCompactSupport_normed, ?_, b.nonneg_normed,
            b.integral_normed⟩⟩
        rw [b.support_normed_eq]
        exact Metric.ball_subset_closedBall
      · exact ⟨0, fun h => absurd h hε⟩
    choose ρ hρ using hex
    exact ⟨ρ, fun ε hε => hρ ε hε⟩
  obtain ⟨ρ, hρ⟩ := bumpFamily
  have hqc : Continuous q := continuous_iff_continuousAt.2 fun t => (hq t).continuousAt
  have hqb : ∀ t : ℝ, |q t| ≤ |t| := by
    intro t
    have h := hqLip t 0
    rw [hq0, sub_zero, sub_zero] at h
    exact h
  have hUloc : LocallyIntegrable U volume := (GaussL2LocallyIntegrable U hUL2).1
  have hUcpt : ∀ K' : Set (EuclideanSpace ℝ (Fin n)), IsCompact K' →
      MemLp U 2 (volume.restrict K') := (GaussL2LocallyIntegrable U hUL2).2.1
  have hsm : ∀ ε : ℝ, 0 < ε → ContDiff ℝ (⊤ : ℕ∞) (ρ ε) := fun ε hε => (hρ ε hε).1
  have hcsρ : ∀ ε : ℝ, 0 < ε → HasCompactSupport (ρ ε) := fun ε hε => (hρ ε hε).2.1
  have hsu : ∀ ε : ℝ, 0 < ε → Function.support (ρ ε) ⊆ Metric.closedBall 0 ε :=
    fun ε hε => (hρ ε hε).2.2.1
  have hnn : ∀ ε : ℝ, 0 < ε → ∀ x, 0 ≤ ρ ε x := fun ε hε => (hρ ε hε).2.2.2.1
  have hms : ∀ ε : ℝ, 0 < ε → ∫ x, ρ ε x = 1 := fun ε hε => (hρ ε hε).2.2.2.2
  have hsmulapp : ∀ (c : ℝ) (y : EuclideanSpace ℝ (Fin n)) (i : Fin n),
      (c • y) i = c * y i := by intro c y i; simp
  intro j φ hφ hφcs
  have hGjloc : LocallyIntegrable (fun x => G x j) volume :=
    (GaussL2LocallyIntegrable _ (hGL2 j)).1
  have hGjcpt : ∀ K' : Set (EuclideanSpace ℝ (Fin n)), IsCompact K' →
      MemLp (fun x => G x j) 2 (volume.restrict K') :=
    (GaussL2LocallyIntegrable _ (hGL2 j)).2.1
  have hψc : Continuous (fun x => fderiv ℝ φ x (EuclideanSpace.single j (1:ℝ))) :=
    (hφ.continuous_fderiv (by simp)).clm_apply continuous_const
  have hψcs : HasCompactSupport (fun x => fderiv ℝ φ x (EuclideanSpace.single j (1:ℝ))) :=
    hφcs.fderiv_apply ℝ _
  -- the compact set carrying both `φ` and `∂ⱼφ`
  obtain ⟨K, hKdef⟩ : ∃ K : Set (EuclideanSpace ℝ (Fin n)),
      K = tsupport φ ∪ tsupport (fun x => fderiv ℝ φ x (EuclideanSpace.single j (1:ℝ))) :=
    ⟨_, rfl⟩
  have hKc : IsCompact K := by rw [hKdef]; exact hφcs.union hψcs
  have hKm : MeasurableSet K := hKc.measurableSet
  have hfin : IsFiniteMeasure (volume.restrict K) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact hKc.measure_lt_top⟩
  have hφ0 : ∀ x ∉ K, φ x = 0 := by
    intro x hx
    by_contra hne
    rw [hKdef] at hx
    exact hx (Or.inl (subset_tsupport φ hne))
  have hψ0 : ∀ x ∉ K, fderiv ℝ φ x (EuclideanSpace.single j (1:ℝ)) = 0 := by
    intro x hx
    by_contra hne
    rw [hKdef] at hx
    exact hx (Or.inr (subset_tsupport _ hne))
  obtain ⟨Mφ, hMφ⟩ := hφ.continuous.bounded_above_of_compact_support hφcs
  have hMφ0 : (0:ℝ) ≤ Mφ := le_trans (norm_nonneg _) (hMφ 0)
  -- the `L²(K, λ)` data
  have mU : MemLp U 2 (volume.restrict K) := hUcpt K hKc
  have mGj : MemLp (fun x => G x j) 2 (volume.restrict K) := hGjcpt K hKc
  have mφ : MemLp φ 2 (volume.restrict K) :=
    MemLp.of_bound hφ.continuous.aestronglyMeasurable Mφ
      (Filter.Eventually.of_forall hMφ)
  have mψ : MemLp (fun x => fderiv ℝ φ x (EuclideanSpace.single j (1:ℝ))) 2
      (volume.restrict K) := by
    obtain ⟨Mψ, hMψ⟩ := hψc.bounded_above_of_compact_support hψcs
    exact MemLp.of_bound hψc.aestronglyMeasurable Mψ (Filter.Eventually.of_forall hMψ)
  -- a single integrability criterion for all the integrands that appear
  have hInt : ∀ (a b h : EuclideanSpace ℝ (Fin n) → ℝ) (C : ℝ), 0 ≤ C →
      MemLp a 2 (volume.restrict K) → MemLp b 2 (volume.restrict K) →
      AEStronglyMeasurable h (volume.restrict K) →
      (∀ x, |h x| ≤ C * (|a x| * |b x|)) → Integrable h (volume.restrict K) := by
    intro a b h C hC ha hb hhm hbd
    have hab : MemLp (fun x => C * (a x * b x)) 1 (volume.restrict K) :=
      (hb.mul' ha).const_mul C
    refine memLp_one_iff_integrable.1
      (MemLp.of_le hab hhm (Filter.Eventually.of_forall fun x => ?_))
    show ‖h x‖ ≤ ‖C * (a x * b x)‖
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_of_nonneg hC, abs_mul]
    exact hbd x
  -- the mollifications
  have hcU : ∀ ε : ℝ, 0 < ε → ContDiff ℝ (⊤ : ℕ∞)
      (convolution (ρ ε) U (ContinuousLinearMap.lsmul ℝ ℝ) volume) := fun ε hε =>
    (hcsρ ε hε).contDiff_convolution_left (ContinuousLinearMap.lsmul ℝ ℝ) (hsm ε hε) hUloc
  have hcG : ∀ ε : ℝ, 0 < ε → Continuous
      (convolution (ρ ε) (fun y => G y j) (ContinuousLinearMap.lsmul ℝ ℝ) volume) :=
    fun ε hε => (hcsρ ε hε).continuous_convolution_left
      (ContinuousLinearMap.lsmul ℝ ℝ) (hsm ε hε).continuous hGjloc
  have hD : ∀ ε : ℝ, 0 < ε → ∀ x,
      fderiv ℝ (convolution (ρ ε) U (ContinuousLinearMap.lsmul ℝ ℝ) volume) x
          (EuclideanSpace.single j 1)
        = convolution (ρ ε) (fun y => G y j) (ContinuousLinearMap.lsmul ℝ ℝ) volume x :=
    fun ε hε x => ConvolutionFDerivOfWeakGrad (ρ ε) (hsm ε hε) (hcsρ ε hε) U G hUloc hwg j x
  have mUE : ∀ ε : ℝ, 0 < ε →
      MemLp (convolution (ρ ε) U (ContinuousLinearMap.lsmul ℝ ℝ) volume) 2
        (volume.restrict K) := by
    intro ε hε
    obtain ⟨C, hC⟩ := hKc.exists_bound_of_continuousOn (hcU ε hε).continuous.continuousOn
    refine MemLp.of_bound (hcU ε hε).continuous.aestronglyMeasurable C ?_
    rw [ae_restrict_iff' hKm]
    exact Filter.Eventually.of_forall hC
  have mGE : ∀ ε : ℝ, 0 < ε →
      MemLp (convolution (ρ ε) (fun y => G y j) (ContinuousLinearMap.lsmul ℝ ℝ) volume) 2
        (volume.restrict K) := by
    intro ε hε
    obtain ⟨C, hC⟩ := hKc.exists_bound_of_continuousOn (hcG ε hε).continuousOn
    refine MemLp.of_bound (hcG ε hε).aestronglyMeasurable C ?_
    rw [ae_restrict_iff' hKm]
    exact Filter.Eventually.of_forall hC
  -- the two `L²(K)` convergences
  have TU := MollifierL2Local U hUcpt ρ hsm hsu hnn hms K hKc
  have TG := MollifierL2Local (fun x => G x j) hGjcpt ρ hsm hsu hnn hms K hKc
  have TUr : Filter.Tendsto (fun ε : ℝ => (eLpNorm (fun x =>
        convolution (ρ ε) U (ContinuousLinearMap.lsmul ℝ ℝ) volume x - U x) 2
        (volume.restrict K)).toReal) (nhdsWithin (0:ℝ) (Set.Ioi 0)) (nhds 0) := by
    simpa [Function.comp_def] using (ENNReal.tendsto_toReal (by simp : (0:ℝ≥0∞) ≠ ⊤)).comp TU
  have TGr : Filter.Tendsto (fun ε : ℝ => (eLpNorm (fun x =>
        convolution (ρ ε) (fun y => G y j) (ContinuousLinearMap.lsmul ℝ ℝ) volume x
          - G x j) 2 (volume.restrict K)).toReal)
      (nhdsWithin (0:ℝ) (Set.Ioi 0)) (nhds 0) := by
    simpa [Function.comp_def] using (ENNReal.tendsto_toReal (by simp : (0:ℝ≥0∞) ≠ ⊤)).comp TG
  -- a single criterion for passing to the limit in an integral over `K`
  have hLim : ∀ (F : ℝ → EuclideanSpace ℝ (Fin n) → ℝ)
      (Fl : EuclideanSpace ℝ (Fin n) → ℝ) (g : ℝ → ℝ),
      Filter.Tendsto g (nhdsWithin (0:ℝ) (Set.Ioi 0)) (nhds 0) →
      (∀ᶠ ε in nhdsWithin (0:ℝ) (Set.Ioi 0),
        ‖(∫ x in K, F ε x) - ∫ x in K, Fl x‖ ≤ g ε) →
      Filter.Tendsto (fun ε => ∫ x in K, F ε x) (nhdsWithin (0:ℝ) (Set.Ioi 0))
        (nhds (∫ x in K, Fl x)) := by
    intro F Fl g hg hbd
    rw [tendsto_iff_norm_sub_tendsto_zero]
    exact squeeze_zero' (Filter.Eventually.of_forall fun ε => norm_nonneg _) hbd hg
  -- integrability of the five integrands that occur
  have iAe : ∀ ε : ℝ, 0 < ε → Integrable
      (fun x => q (convolution (ρ ε) U (ContinuousLinearMap.lsmul ℝ ℝ) volume x) * fderiv ℝ φ x (EuclideanSpace.single j (1:ℝ))) (volume.restrict K) := by
    intro ε hε
    refine hInt (fun x => convolution (ρ ε) U (ContinuousLinearMap.lsmul ℝ ℝ) volume x) (fun x => fderiv ℝ φ x (EuclideanSpace.single j (1:ℝ))) _ 1 zero_le_one (mUE ε hε) mψ
      (((hqc.comp (hcU ε hε).continuous).mul hψc).aestronglyMeasurable) (fun x => ?_)
    rw [abs_mul, one_mul]
    exact mul_le_mul_of_nonneg_right (hqb _) (abs_nonneg _)
  have iAi : Integrable (fun x => q (U x) * fderiv ℝ φ x (EuclideanSpace.single j (1:ℝ))) (volume.restrict K) := by
    refine hInt U (fun x => fderiv ℝ φ x (EuclideanSpace.single j (1:ℝ))) _ 1 zero_le_one mU mψ
      ((hqc.comp_aestronglyMeasurable mU.1).mul hψc.aestronglyMeasurable) (fun x => ?_)
    rw [abs_mul, one_mul]
    exact mul_le_mul_of_nonneg_right (hqb _) (abs_nonneg _)
  have iBe : ∀ ε : ℝ, 0 < ε → Integrable
      (fun x => (q' (convolution (ρ ε) U (ContinuousLinearMap.lsmul ℝ ℝ) volume x) * convolution (ρ ε) (fun y => G y j) (ContinuousLinearMap.lsmul ℝ ℝ) volume x) * φ x) (volume.restrict K) := by
    intro ε hε
    refine hInt (fun x => convolution (ρ ε) (fun y => G y j) (ContinuousLinearMap.lsmul ℝ ℝ) volume x) φ _ 1 zero_le_one (mGE ε hε) mφ
      ((((hq'c.comp (hcU ε hε).continuous).mul (hcG ε hε)).mul
        hφ.continuous).aestronglyMeasurable) (fun x => ?_)
    rw [abs_mul, abs_mul, one_mul]
    exact mul_le_mul_of_nonneg_right
      (le_trans (mul_le_mul_of_nonneg_right (hq'b _) (abs_nonneg _)) (by rw [one_mul]))
      (abs_nonneg _)
  have iBi : Integrable (fun x => (q' (U x) * G x j) * φ x) (volume.restrict K) := by
    refine hInt (fun x => G x j) φ _ 1 zero_le_one mGj mφ
      (((hq'c.comp_aestronglyMeasurable mU.1).mul mGj.1).mul
        hφ.continuous.aestronglyMeasurable) (fun x => ?_)
    rw [abs_mul, abs_mul, one_mul]
    exact mul_le_mul_of_nonneg_right
      (le_trans (mul_le_mul_of_nonneg_right (hq'b _) (abs_nonneg _)) (by rw [one_mul]))
      (abs_nonneg _)
  have iB1 : ∀ ε : ℝ, 0 < ε → Integrable
      (fun x => (q' (convolution (ρ ε) U (ContinuousLinearMap.lsmul ℝ ℝ) volume x) * (convolution (ρ ε) (fun y => G y j) (ContinuousLinearMap.lsmul ℝ ℝ) volume x - G x j)) * φ x) (volume.restrict K) := by
    intro ε hε
    refine hInt (fun x => convolution (ρ ε) (fun y => G y j) (ContinuousLinearMap.lsmul ℝ ℝ) volume x - G x j) φ _ 1 zero_le_one
      ((mGE ε hε).sub mGj) mφ
      (((hq'c.comp (hcU ε hε).continuous).aestronglyMeasurable.mul
        ((hcG ε hε).aestronglyMeasurable.sub mGj.1)).mul
        hφ.continuous.aestronglyMeasurable) (fun x => ?_)
    rw [abs_mul, abs_mul, one_mul]
    exact mul_le_mul_of_nonneg_right
      (le_trans (mul_le_mul_of_nonneg_right (hq'b _) (abs_nonneg _)) (by rw [one_mul]))
      (abs_nonneg _)
  have iB2 : ∀ ε : ℝ, 0 < ε → Integrable
      (fun x => ((q' (convolution (ρ ε) U (ContinuousLinearMap.lsmul ℝ ℝ) volume x) - q' (U x)) * G x j) * φ x) (volume.restrict K) := by
    intro ε hε
    refine hInt (fun x => G x j) φ _ 2 (by norm_num) mGj mφ
      ((((hq'c.comp (hcU ε hε).continuous).aestronglyMeasurable.sub
        (hq'c.comp_aestronglyMeasurable mU.1)).mul mGj.1).mul
        hφ.continuous.aestronglyMeasurable) (fun x => ?_)
    have hb2 : |q' (convolution (ρ ε) U (ContinuousLinearMap.lsmul ℝ ℝ) volume x) - q' (U x)| ≤ 2 := by
      have h1 := hq'b (convolution (ρ ε) U (ContinuousLinearMap.lsmul ℝ ℝ) volume x)
      have h2 := hq'b (U x)
      rw [abs_le] at h1 h2 ⊢
      constructor <;> [linarith [h1.1, h2.2]; linarith [h1.2, h2.1]]
    rw [abs_mul, abs_mul]
    calc |q' (convolution (ρ ε) U (ContinuousLinearMap.lsmul ℝ ℝ) volume x) - q' (U x)| * |G x j| * |φ x|
        ≤ 2 * |G x j| * |φ x| :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right hb2 (abs_nonneg _)) (abs_nonneg _)
      _ = 2 * (|G x j| * |φ x|) := by ring
  -- Term A: the left-hand sides converge
  have LA : Filter.Tendsto (fun ε : ℝ => ∫ x in K, q (convolution (ρ ε) U (ContinuousLinearMap.lsmul ℝ ℝ) volume x) * fderiv ℝ φ x (EuclideanSpace.single j (1:ℝ)))
      (nhdsWithin (0:ℝ) (Set.Ioi 0)) (nhds (∫ x in K, q (U x) * fderiv ℝ φ x (EuclideanSpace.single j (1:ℝ)))) := by
    refine hLim (fun ε x => q (convolution (ρ ε) U (ContinuousLinearMap.lsmul ℝ ℝ) volume x) * fderiv ℝ φ x (EuclideanSpace.single j (1:ℝ))) (fun x => q (U x) * fderiv ℝ φ x (EuclideanSpace.single j (1:ℝ)))
      (fun ε => 1 * ((eLpNorm (fun x => convolution (ρ ε) U (ContinuousLinearMap.lsmul ℝ ℝ) volume x - U x) 2 (volume.restrict K)).toReal * (eLpNorm (fun x => fderiv ℝ φ x (EuclideanSpace.single j (1:ℝ))) 2 (volume.restrict K)).toReal)) ?_ ?_
    · simpa using (TUr.mul_const (eLpNorm (fun x => fderiv ℝ φ x (EuclideanSpace.single j (1:ℝ))) 2 (volume.restrict K)).toReal).const_mul 1
    · filter_upwards [self_mem_nhdsWithin] with ε hε
      have hε0 : (0:ℝ) < ε := hε
      have hsub : (∫ x in K, q (convolution (ρ ε) U (ContinuousLinearMap.lsmul ℝ ℝ) volume x) * fderiv ℝ φ x (EuclideanSpace.single j (1:ℝ)))
            - ∫ x in K, q (U x) * fderiv ℝ φ x (EuclideanSpace.single j (1:ℝ))
          = ∫ x in K, (q (convolution (ρ ε) U (ContinuousLinearMap.lsmul ℝ ℝ) volume x) - q (U x)) * fderiv ℝ φ x (EuclideanSpace.single j (1:ℝ)) := by
        rw [← integral_sub (iAe ε hε0) iAi]
        refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
        show (q (convolution (ρ ε) U (ContinuousLinearMap.lsmul ℝ ℝ) volume x) * fderiv ℝ φ x (EuclideanSpace.single j (1:ℝ))) - q (U x) * fderiv ℝ φ x (EuclideanSpace.single j (1:ℝ))
            = (q (convolution (ρ ε) U (ContinuousLinearMap.lsmul ℝ ℝ) volume x) - q (U x)) * fderiv ℝ φ x (EuclideanSpace.single j (1:ℝ))
        ring
      rw [hsub]
      refine NormIntegralLeOfProductDomination K _ (fun x => convolution (ρ ε) U (ContinuousLinearMap.lsmul ℝ ℝ) volume x - U x)
        (fun x => fderiv ℝ φ x (EuclideanSpace.single j (1:ℝ))) 1 zero_le_one ((mUE ε hε0).sub mU) mψ (fun x => ?_)
      show |(q (convolution (ρ ε) U (ContinuousLinearMap.lsmul ℝ ℝ) volume x) - q (U x)) * fderiv ℝ φ x (EuclideanSpace.single j (1:ℝ))|
          ≤ 1 * (|convolution (ρ ε) U (ContinuousLinearMap.lsmul ℝ ℝ) volume x - U x| * |fderiv ℝ φ x (EuclideanSpace.single j (1:ℝ))|)
      rw [abs_mul, one_mul]
      exact mul_le_mul_of_nonneg_right (hqLip _ _) (abs_nonneg _)
  -- Term B: the right-hand sides converge
  have LB : Filter.Tendsto (fun ε : ℝ => ∫ x in K, (q' (convolution (ρ ε) U (ContinuousLinearMap.lsmul ℝ ℝ) volume x) * convolution (ρ ε) (fun y => G y j) (ContinuousLinearMap.lsmul ℝ ℝ) volume x) * φ x)
      (nhdsWithin (0:ℝ) (Set.Ioi 0))
      (nhds (∫ x in K, (q' (U x) * G x j) * φ x)) := by
    refine hLim (fun ε x => (q' (convolution (ρ ε) U (ContinuousLinearMap.lsmul ℝ ℝ) volume x) * convolution (ρ ε) (fun y => G y j) (ContinuousLinearMap.lsmul ℝ ℝ) volume x) * φ x)
      (fun x => (q' (U x) * G x j) * φ x)
      (fun ε => 1 * ((eLpNorm (fun x => convolution (ρ ε) (fun y => G y j) (ContinuousLinearMap.lsmul ℝ ℝ) volume x - G x j) 2 (volume.restrict K)).toReal * (eLpNorm φ 2 (volume.restrict K)).toReal) + (Lq * Mφ) * ((eLpNorm (fun x => convolution (ρ ε) U (ContinuousLinearMap.lsmul ℝ ℝ) volume x - U x) 2 (volume.restrict K)).toReal * (eLpNorm (fun x => G x j) 2 (volume.restrict K)).toReal)) ?_ ?_
    · have h1 := (TGr.mul_const (eLpNorm φ 2 (volume.restrict K)).toReal).const_mul 1
      have h2 := (TUr.mul_const (eLpNorm (fun x => G x j) 2 (volume.restrict K)).toReal).const_mul (Lq * Mφ)
      simpa using h1.add h2
    · filter_upwards [self_mem_nhdsWithin] with ε hε
      have hε0 : (0:ℝ) < ε := hε
      have hsub : (∫ x in K, (q' (convolution (ρ ε) U (ContinuousLinearMap.lsmul ℝ ℝ) volume x) * convolution (ρ ε) (fun y => G y j) (ContinuousLinearMap.lsmul ℝ ℝ) volume x) * φ x)
            - ∫ x in K, (q' (U x) * G x j) * φ x
          = (∫ x in K, (q' (convolution (ρ ε) U (ContinuousLinearMap.lsmul ℝ ℝ) volume x) * (convolution (ρ ε) (fun y => G y j) (ContinuousLinearMap.lsmul ℝ ℝ) volume x - G x j)) * φ x)
            + ∫ x in K, ((q' (convolution (ρ ε) U (ContinuousLinearMap.lsmul ℝ ℝ) volume x) - q' (U x)) * G x j) * φ x := by
        rw [← integral_add (iB1 ε hε0) (iB2 ε hε0), ← integral_sub (iBe ε hε0) iBi]
        refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
        show ((q' (convolution (ρ ε) U (ContinuousLinearMap.lsmul ℝ ℝ) volume x) * convolution (ρ ε) (fun y => G y j) (ContinuousLinearMap.lsmul ℝ ℝ) volume x) * φ x) - (q' (U x) * G x j) * φ x
            = ((q' (convolution (ρ ε) U (ContinuousLinearMap.lsmul ℝ ℝ) volume x) * (convolution (ρ ε) (fun y => G y j) (ContinuousLinearMap.lsmul ℝ ℝ) volume x - G x j)) * φ x)
              + ((q' (convolution (ρ ε) U (ContinuousLinearMap.lsmul ℝ ℝ) volume x) - q' (U x)) * G x j) * φ x
        ring
      rw [hsub]
      refine le_trans (norm_add_le _ _) (add_le_add ?_ ?_)
      · refine NormIntegralLeOfProductDomination K _ (fun x => convolution (ρ ε) (fun y => G y j) (ContinuousLinearMap.lsmul ℝ ℝ) volume x - G x j) (fun x => φ x) 1 zero_le_one
          ((mGE ε hε0).sub mGj) mφ (fun x => ?_)
        show |(q' (convolution (ρ ε) U (ContinuousLinearMap.lsmul ℝ ℝ) volume x) * (convolution (ρ ε) (fun y => G y j) (ContinuousLinearMap.lsmul ℝ ℝ) volume x - G x j)) * φ x|
            ≤ 1 * (|convolution (ρ ε) (fun y => G y j) (ContinuousLinearMap.lsmul ℝ ℝ) volume x - G x j| * |φ x|)
        rw [abs_mul, abs_mul, one_mul]
        refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
        exact le_trans (mul_le_mul_of_nonneg_right (hq'b _) (abs_nonneg _)) (by rw [one_mul])
      · refine NormIntegralLeOfProductDomination K _ (fun x => convolution (ρ ε) U (ContinuousLinearMap.lsmul ℝ ℝ) volume x - U x) (fun x => G x j) (Lq * Mφ)
          (by positivity) ((mUE ε hε0).sub mU) mGj (fun x => ?_)
        show |((q' (convolution (ρ ε) U (ContinuousLinearMap.lsmul ℝ ℝ) volume x) - q' (U x)) * G x j) * φ x|
            ≤ (Lq * Mφ) * (|convolution (ρ ε) U (ContinuousLinearMap.lsmul ℝ ℝ) volume x - U x| * |G x j|)
        rw [abs_mul, abs_mul]
        have e1 : |q' (convolution (ρ ε) U (ContinuousLinearMap.lsmul ℝ ℝ) volume x) - q' (U x)| ≤ Lq * |convolution (ρ ε) U (ContinuousLinearMap.lsmul ℝ ℝ) volume x - U x| := hq'Lip _ _
        have e2 : |φ x| ≤ Mφ := by
          have hb := hMφ x
          rwa [Real.norm_eq_abs] at hb
        calc |q' (convolution (ρ ε) U (ContinuousLinearMap.lsmul ℝ ℝ) volume x) - q' (U x)| * |G x j| * |φ x|
            ≤ (Lq * |convolution (ρ ε) U (ContinuousLinearMap.lsmul ℝ ℝ) volume x - U x|) * |G x j| * Mφ := by
              refine mul_le_mul (mul_le_mul_of_nonneg_right e1 (abs_nonneg _)) e2
                (abs_nonneg _) (by positivity)
          _ = (Lq * Mφ) * (|convolution (ρ ε) U (ContinuousLinearMap.lsmul ℝ ℝ) volume x - U x| * |G x j|) := by ring
  -- the integration-by-parts identity at each positive `ε`
  have EQ : ∀ᶠ ε in nhdsWithin (0:ℝ) (Set.Ioi 0),
      (∫ x in K, q (convolution (ρ ε) U (ContinuousLinearMap.lsmul ℝ ℝ) volume x) * fderiv ℝ φ x (EuclideanSpace.single j (1:ℝ)))
        = -(∫ x in K, (q' (convolution (ρ ε) U (ContinuousLinearMap.lsmul ℝ ℝ) volume x) * convolution (ρ ε) (fun y => G y j) (ContinuousLinearMap.lsmul ℝ ℝ) volume x) * φ x) := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    have hε0 : (0:ℝ) < ε := hε
    have h1 := CompIntegrationByParts q q' hq hq'c _ j ((hcU ε hε0).differentiable (by simp))
      (((hcU ε hε0).continuous_fderiv (by simp)).clm_apply continuous_const) φ hφ hφcs
    have h2 : (∫ x, (q' (convolution (ρ ε) U (ContinuousLinearMap.lsmul ℝ ℝ) volume x) * fderiv ℝ (convolution (ρ ε) U (ContinuousLinearMap.lsmul ℝ ℝ) volume) x (EuclideanSpace.single j 1)) * φ x)
        = ∫ x, (q' (convolution (ρ ε) U (ContinuousLinearMap.lsmul ℝ ℝ) volume x) * convolution (ρ ε) (fun y => G y j) (ContinuousLinearMap.lsmul ℝ ℝ) volume x) * φ x := by
      refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      show (q' (convolution (ρ ε) U (ContinuousLinearMap.lsmul ℝ ℝ) volume x) * fderiv ℝ (convolution (ρ ε) U (ContinuousLinearMap.lsmul ℝ ℝ) volume) x (EuclideanSpace.single j 1)) * φ x
          = (q' (convolution (ρ ε) U (ContinuousLinearMap.lsmul ℝ ℝ) volume x) * convolution (ρ ε) (fun y => G y j) (ContinuousLinearMap.lsmul ℝ ℝ) volume x) * φ x
      rw [hD ε hε0 x]
    rw [h2] at h1
    have c1 : (∫ x in K, q (convolution (ρ ε) U (ContinuousLinearMap.lsmul ℝ ℝ) volume x) * fderiv ℝ φ x (EuclideanSpace.single j (1:ℝ)))
        = ∫ x, q (convolution (ρ ε) U (ContinuousLinearMap.lsmul ℝ ℝ) volume x) * fderiv ℝ φ x (EuclideanSpace.single j (1:ℝ)) :=
      setIntegral_eq_integral_of_forall_compl_eq_zero
        (fun x hx => by rw [hψ0 x hx, mul_zero])
    have c2 : (∫ x in K, (q' (convolution (ρ ε) U (ContinuousLinearMap.lsmul ℝ ℝ) volume x) * convolution (ρ ε) (fun y => G y j) (ContinuousLinearMap.lsmul ℝ ℝ) volume x) * φ x)
        = ∫ x, (q' (convolution (ρ ε) U (ContinuousLinearMap.lsmul ℝ ℝ) volume x) * convolution (ρ ε) (fun y => G y j) (ContinuousLinearMap.lsmul ℝ ℝ) volume x) * φ x :=
      setIntegral_eq_integral_of_forall_compl_eq_zero
        (fun x hx => by rw [hφ0 x hx, mul_zero])
    rw [c1, c2]
    exact h1
  -- reduce the goal to integrals over `K` and conclude by uniqueness of limits
  simp only [hsmulapp]
  have g1 : (∫ x in K, q (U x) * fderiv ℝ φ x (EuclideanSpace.single j (1:ℝ))) = ∫ x, q (U x) * fderiv ℝ φ x (EuclideanSpace.single j (1:ℝ)) :=
    setIntegral_eq_integral_of_forall_compl_eq_zero
      (fun x hx => by rw [hψ0 x hx, mul_zero])
  have g2 : (∫ x in K, (q' (U x) * G x j) * φ x) = ∫ x, (q' (U x) * G x j) * φ x :=
    setIntegral_eq_integral_of_forall_compl_eq_zero
      (fun x hx => by rw [hφ0 x hx, mul_zero])
  rw [← g1, ← g2]
  exact tendsto_nhds_unique (Filter.Tendsto.congr' EQ LA) LB.neg
