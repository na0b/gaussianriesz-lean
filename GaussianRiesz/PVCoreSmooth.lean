import GaussianRiesz.PVKernelConstantCancellation
import GaussianRiesz.RieszSemigroupPointwise
import GaussianRiesz.MehlerLebesgueKernel
import GaussianRiesz.PVSubtractedSliceBound
import GaussianRiesz.PVSemigroupKernelDerivative
import GaussianRiesz.PVKernelTimeIntegral
import GaussianRiesz.SubordinationWeightIntegral
open MeasureTheory
theorem PVCoreSmooth {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hfc : HasCompactSupport f) (j : Fin n)
    (x : EuclideanSpace ℝ (Fin n)) :
    (∀ ε : ℝ, 0 < ε →
        IntegrableOn (fun y : EuclideanSpace ℝ (Fin n) => GaussRieszKernel j x y * f y)
          {y : EuclideanSpace ℝ (Fin n) | ε < ‖x - y‖} volume)
      ∧ Filter.Tendsto
          (fun ε : ℝ => ∫ y in {y : EuclideanSpace ℝ (Fin n) | ε < ‖x - y‖},
            GaussRieszKernel j x y * f y)
          (nhdsWithin 0 (Set.Ioi 0))
          (nhds ((Real.sqrt Real.pi)⁻¹ * ∫ s in Set.Ioi (0 : ℝ), (Real.sqrt s)⁻¹ *
            (Real.exp (-s) * ((Real.sqrt 2)⁻¹ *
              ∫ z, fderiv ℝ f (Real.exp (-s) • x + Real.sqrt (1 - Real.exp (-2 * s)) • z)
                (EuclideanSpace.single j (1 : ℝ)) ∂(GaussMeasure n))))) := by
  -- The Lean route takes the paper's two sentences for this lemma one block at a time.
  -- Step 3 of the `.tex`, the subtracted bound (6), is `PVSubtractedSliceBound`; Step 2,
  -- the kernel form `∫ D_j^x p_s(x,y) f(y) dy = e^{-s}(A_s(D_j f))(x)` together with its
  -- absolute convergence, is `PVSemigroupKernelDerivative`; Step 5's time-integral
  -- representation of the kernel is `PVKernelTimeIntegral`; and the per-`s` vanishing,
  -- the truncated integrability of the kernel and the `ε → 0` limit on constants are the
  -- three clauses of `PVKernelConstantCancellation`.  What is assembled here is Step 0's
  -- bounds on `f`, Step 4's Fubini exchange on `ℝⁿ × (0,∞)` and the subtracted identity
  -- (10) it yields, and Step 5's splitting of the truncated integral with dominated
  -- convergence in `ε`.  Steps 1 and 2(a)-(b) of the `.tex` -- the null-set equivalence
  -- and the almost-everywhere-to-everywhere upgrade -- are not needed on this route:
  -- `PVSemigroupKernelDerivative` reaches (5) by a change of variables and an
  -- integration by parts in `y`, with no `L²` representative anywhere.
  obtain ⟨D, hD⟩ : ∃ D : ℝ → EuclideanSpace ℝ (Fin n) → ℝ,
      ∀ (s : ℝ) (y : EuclideanSpace ℝ (Fin n)), D s y =
        Real.sqrt 2 * Real.exp (-s) * (y j - Real.exp (-s) * x j) / (1 - Real.exp (-2 * s))
          * (Real.pi ^ (-(n : ℝ) / 2) * (1 - Real.exp (-2 * s)) ^ (-(n : ℝ) / 2)
              * Real.exp (-‖Real.exp (-s) • x - y‖ ^ 2 / (1 - Real.exp (-2 * s)))) := ⟨_, fun _ _ => rfl⟩
  -- STEP 0: the bounds on f that the estimates consume
  obtain ⟨M, hM⟩ := hfc.exists_bound_of_continuous hf.continuous
  obtain ⟨L, hL0, hLip⟩ : ∃ L : ℝ, 0 ≤ L ∧ ∀ y : EuclideanSpace ℝ (Fin n),
      |f y - f x| ≤ L * ‖y - x‖ := by
    have hfdc : Continuous (fderiv ℝ f) := hf.continuous_fderiv (by simp)
    obtain ⟨L, hL⟩ := (hfc.fderiv ℝ).exists_bound_of_continuous hfdc
    refine ⟨L, le_trans (norm_nonneg (fderiv ℝ f x)) (hL x), fun y => ?_⟩
    have h := Convex.norm_image_sub_le_of_norm_fderiv_le (f := f) (s := Set.univ)
      (fun z _ => (hf.differentiable (by simp)) z) (fun z _ => hL z) convex_univ
      (Set.mem_univ x) (Set.mem_univ y)
    rwa [Real.norm_eq_abs] at h
  obtain ⟨C, hC0, hCbd⟩ := PVSubtractedSliceBound j x
  have hΩm : ∀ ε : ℝ, MeasurableSet {y : EuclideanSpace ℝ (Fin n) | ε < ‖x - y‖} :=
    fun ε => measurableSet_lt measurable_const (by fun_prop)
  have hx1 : (0:ℝ) < 1 + ‖x‖ := by positivity
  -- the integrable time weight
  have hw2 : ∫⁻ s in Set.Ioi (0:ℝ),
      ENNReal.ofReal ((Real.sqrt s)⁻¹ * Real.exp (-s)) < ⊤ := by
    have h2 := SubordinationWeightIntegral.1.2
    rw [hasFiniteIntegral_iff_enorm] at h2
    refine lt_of_le_of_lt (le_of_eq ?_) h2
    refine lintegral_congr fun s => ?_
    exact (Real.enorm_eq_ofReal
      (by positivity : (0:ℝ) ≤ (Real.sqrt s)⁻¹ * Real.exp (-s))).symm
  -- STEP 4: Fubini on ℝⁿ × (0,∞)
  have hjm : Measurable (Function.uncurry
      (fun (y : EuclideanSpace ℝ (Fin n)) (s : ℝ) =>
        (Real.sqrt s)⁻¹ * (D s y * (f y - f x)))) := by
    simp only [hD]
    have hfm : Measurable f := hf.continuous.measurable
    fun_prop
  have hF : Integrable (Function.uncurry
      (fun (y : EuclideanSpace ℝ (Fin n)) (s : ℝ) =>
        (Real.sqrt s)⁻¹ * (D s y * (f y - f x))))
      ((volume : Measure (EuclideanSpace ℝ (Fin n))).prod
        (volume.restrict (Set.Ioi (0:ℝ)))) := by
    refine ⟨hjm.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_enorm, lintegral_prod_symm _ hjm.enorm.aemeasurable]
    have hbd : ∀ s : ℝ, s ∈ Set.Ioi (0:ℝ) →
        ∫⁻ y : EuclideanSpace ℝ (Fin n),
            ‖Function.uncurry (fun (y : EuclideanSpace ℝ (Fin n)) (s : ℝ) =>
              (Real.sqrt s)⁻¹ * (D s y * (f y - f x))) (y, s)‖ₑ
          ≤ ENNReal.ofReal ((Real.sqrt s)⁻¹ * (C * L * (1 + ‖x‖) * Real.exp (-s))) := by
      intro s hs
      have h1 : ∫⁻ y : EuclideanSpace ℝ (Fin n),
            ‖Function.uncurry (fun (y : EuclideanSpace ℝ (Fin n)) (s : ℝ) =>
              (Real.sqrt s)⁻¹ * (D s y * (f y - f x))) (y, s)‖ₑ
          = ENNReal.ofReal ((Real.sqrt s)⁻¹)
              * ∫⁻ y : EuclideanSpace ℝ (Fin n), ‖D s y * (f y - f x)‖ₑ := by
        rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        refine lintegral_congr fun y => ?_
        rw [Function.uncurry_apply_pair, enorm_mul,
          Real.enorm_eq_ofReal (by positivity : (0:ℝ) ≤ (Real.sqrt s)⁻¹)]
      have h3 : ∫⁻ y : EuclideanSpace ℝ (Fin n), ‖D s y * (f y - f x)‖ₑ
          ≤ ENNReal.ofReal (C * L * Real.exp (-s) * (1 + ‖x‖)) := by
        refine le_trans (le_of_eq ?_) (hCbd f L hL0 hLip s (Set.mem_Ioi.1 hs))
        exact lintegral_congr fun y => by rw [hD]
      rw [h1]
      calc ENNReal.ofReal ((Real.sqrt s)⁻¹)
            * ∫⁻ y : EuclideanSpace ℝ (Fin n), ‖D s y * (f y - f x)‖ₑ
          ≤ ENNReal.ofReal ((Real.sqrt s)⁻¹)
              * ENNReal.ofReal (C * L * Real.exp (-s) * (1 + ‖x‖)) := mul_le_mul' le_rfl h3
        _ = ENNReal.ofReal ((Real.sqrt s)⁻¹ * (C * L * (1 + ‖x‖) * Real.exp (-s))) := by
            rw [← ENNReal.ofReal_mul (by positivity : (0:ℝ) ≤ (Real.sqrt s)⁻¹)]
            congr 1
            ring
    calc ∫⁻ s in Set.Ioi (0:ℝ), ∫⁻ y : EuclideanSpace ℝ (Fin n),
            ‖Function.uncurry (fun (y : EuclideanSpace ℝ (Fin n)) (s : ℝ) =>
              (Real.sqrt s)⁻¹ * (D s y * (f y - f x))) (y, s)‖ₑ
        ≤ ∫⁻ s in Set.Ioi (0:ℝ),
            ENNReal.ofReal ((Real.sqrt s)⁻¹ * (C * L * (1 + ‖x‖) * Real.exp (-s))) :=
          lintegral_mono_ae ((ae_restrict_iff' measurableSet_Ioi).2
            (Filter.Eventually.of_forall hbd))
      _ = ENNReal.ofReal (C * L * (1 + ‖x‖))
            * ∫⁻ s in Set.Ioi (0:ℝ), ENNReal.ofReal ((Real.sqrt s)⁻¹ * Real.exp (-s)) := by
          rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
          refine lintegral_congr fun s => ?_
          rw [← ENNReal.ofReal_mul (by positivity : (0:ℝ) ≤ C * L * (1 + ‖x‖))]
          congr 1
          ring
      _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hw2
  -- the time integral of a single slice, against PVKernelTimeIntegral
  have hKT : ∀ y : EuclideanSpace ℝ (Fin n),
      ∫ s in Set.Ioi (0:ℝ), (Real.sqrt s)⁻¹ * (D s y * (f y - f x))
        = (f y - f x) * (Real.sqrt Real.pi * GaussRieszKernel j x y) := by
    intro y
    have hπ : Real.sqrt Real.pi ≠ 0 := by positivity
    have h3 : (∫ s in Set.Ioi (0:ℝ), (Real.sqrt s)⁻¹ * D s y)
        = Real.sqrt Real.pi * GaussRieszKernel j x y := by
      rw [(PVKernelTimeIntegral j x y).2, ← mul_assoc, mul_inv_cancel₀ hπ, one_mul]
      simp only [hD]
    rw [show (∫ s in Set.Ioi (0:ℝ), (Real.sqrt s)⁻¹ * (D s y * (f y - f x)))
        = ∫ s in Set.Ioi (0:ℝ), ((Real.sqrt s)⁻¹ * D s y) * (f y - f x) from
      integral_congr_ae (Filter.Eventually.of_forall fun s => by ring)]
    rw [integral_mul_const, h3]
    ring
  have hint10 : Integrable (fun y : EuclideanSpace ℝ (Fin n) =>
      GaussRieszKernel j x y * (f y - f x)) volume := by
    have hπ : Real.sqrt Real.pi ≠ 0 := by positivity
    have h2 : Integrable (fun y : EuclideanSpace ℝ (Fin n) =>
        (f y - f x) * (Real.sqrt Real.pi * GaussRieszKernel j x y)) volume := by
      refine (hF.integral_prod_left).congr (Filter.Eventually.of_forall fun y => ?_)
      simpa only [Function.uncurry_apply_pair] using hKT y
    refine (h2.const_mul (Real.sqrt Real.pi)⁻¹).congr
      (Filter.Eventually.of_forall fun y => ?_)
    field_simp
  -- the space integral of a single slice, against the two closed helpers
  have hright : ∀ s : ℝ, 0 < s →
      (∫ y : EuclideanSpace ℝ (Fin n), (Real.sqrt s)⁻¹ * (D s y * (f y - f x)))
        = (Real.sqrt s)⁻¹ * (Real.exp (-s) * ((Real.sqrt 2)⁻¹ *
          ∫ z, fderiv ℝ f (Real.exp (-s) • x + Real.sqrt (1 - Real.exp (-2 * s)) • z)
            (EuclideanSpace.single j (1 : ℝ)) ∂(GaussMeasure n))) := by
    intro s hs
    have hDpi : Integrable (fun y : EuclideanSpace ℝ (Fin n) => D s y) volume := by
      simpa only [hD] using ((PVKernelConstantCancellation j x).1 s hs).1
    have hDf : Integrable (fun y : EuclideanSpace ℝ (Fin n) => D s y * f y) volume := by
      simpa only [hD] using (PVSemigroupKernelDerivative f hf hfc j x s hs).1
    have hz : ∫ y : EuclideanSpace ℝ (Fin n), D s y = 0 := by
      simpa only [hD] using ((PVKernelConstantCancellation j x).1 s hs).2
    have hval : ∫ y : EuclideanSpace ℝ (Fin n), D s y * f y = Real.exp (-s) * ((Real.sqrt 2)⁻¹ *
          ∫ z, fderiv ℝ f (Real.exp (-s) • x + Real.sqrt (1 - Real.exp (-2 * s)) • z)
            (EuclideanSpace.single j (1 : ℝ)) ∂(GaussMeasure n)) := by
      simpa only [hD] using (PVSemigroupKernelDerivative f hf hfc j x s hs).2
    rw [integral_const_mul]
    congr 1
    rw [show (∫ y : EuclideanSpace ℝ (Fin n), D s y * (f y - f x))
        = ∫ y : EuclideanSpace ℝ (Fin n), (D s y * f y - f x * D s y) from
      integral_congr_ae (Filter.Eventually.of_forall fun y => by ring)]
    rw [integral_sub hDf (hDpi.const_mul (f x)), integral_const_mul, hz, mul_zero, sub_zero, hval]
  have h10 : ∫ y : EuclideanSpace ℝ (Fin n), GaussRieszKernel j x y * (f y - f x)
      = (Real.sqrt Real.pi)⁻¹ * ∫ s in Set.Ioi (0 : ℝ), (Real.sqrt s)⁻¹ * (Real.exp (-s) * ((Real.sqrt 2)⁻¹ *
          ∫ z, fderiv ℝ f (Real.exp (-s) • x + Real.sqrt (1 - Real.exp (-2 * s)) • z)
            (EuclideanSpace.single j (1 : ℝ)) ∂(GaussMeasure n))) := by
    have hπ : Real.sqrt Real.pi ≠ 0 := by positivity
    have hleft : (∫ y : EuclideanSpace ℝ (Fin n), ∫ s in Set.Ioi (0:ℝ),
          (Real.sqrt s)⁻¹ * (D s y * (f y - f x)))
        = Real.sqrt Real.pi
            * ∫ y : EuclideanSpace ℝ (Fin n), GaussRieszKernel j x y * (f y - f x) := by
      rw [show (∫ y : EuclideanSpace ℝ (Fin n), ∫ s in Set.Ioi (0:ℝ),
            (Real.sqrt s)⁻¹ * (D s y * (f y - f x)))
          = ∫ y : EuclideanSpace ℝ (Fin n),
              Real.sqrt Real.pi * (GaussRieszKernel j x y * (f y - f x)) from
        integral_congr_ae (Filter.Eventually.of_forall fun y => by
          show (∫ s in Set.Ioi (0:ℝ), (Real.sqrt s)⁻¹ * (D s y * (f y - f x)))
              = Real.sqrt Real.pi * (GaussRieszKernel j x y * (f y - f x))
          rw [hKT y]; ring)]
      rw [integral_const_mul]
    have hr : (∫ s in Set.Ioi (0:ℝ), ∫ y : EuclideanSpace ℝ (Fin n),
          (Real.sqrt s)⁻¹ * (D s y * (f y - f x)))
        = ∫ s in Set.Ioi (0:ℝ), (Real.sqrt s)⁻¹ * (Real.exp (-s) * ((Real.sqrt 2)⁻¹ *
          ∫ z, fderiv ℝ f (Real.exp (-s) • x + Real.sqrt (1 - Real.exp (-2 * s)) • z)
            (EuclideanSpace.single j (1 : ℝ)) ∂(GaussMeasure n))) :=
      integral_congr_ae ((ae_restrict_iff' measurableSet_Ioi).2
        (Filter.Eventually.of_forall fun s hs => hright s (Set.mem_Ioi.1 hs)))
    rw [← hr, ← integral_integral_swap hF, hleft]
    field_simp
  -- STEP 5: the truncated integrals
  refine ⟨fun ε hε => ?_, ?_⟩
  · have hKε := (PVKernelConstantCancellation j x).2.1 ε hε
    refine Integrable.mono' (Integrable.const_mul (Integrable.norm hKε) M)
      (AEStronglyMeasurable.mul (Integrable.aestronglyMeasurable hKε)
        hf.continuous.aestronglyMeasurable)
      (Filter.Eventually.of_forall fun y => ?_)
    rw [norm_mul]
    exact (mul_le_mul_of_nonneg_left (hM y) (norm_nonneg _)).trans (le_of_eq (mul_comm _ _))
  · have hns : (volume : Measure (EuclideanSpace ℝ (Fin n))) {x} = 0 := by
      have : Nontrivial (EuclideanSpace ℝ (Fin n)) :=
        Module.nontrivial_of_finrank_pos (by rw [finrank_euclideanSpace_fin]; exact Fin.pos j)
      exact measure_singleton x
    have h0 : ∀ᵐ y ∂(volume : Measure (EuclideanSpace ℝ (Fin n))), y ≠ x := by
      rw [MeasureTheory.ae_iff]
      simpa using hns
    have hlim : Filter.Tendsto
        (fun ε : ℝ => ∫ y in {y : EuclideanSpace ℝ (Fin n) | ε < ‖x - y‖},
          GaussRieszKernel j x y * (f y - f x))
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds (∫ y : EuclideanSpace ℝ (Fin n), GaussRieszKernel j x y * (f y - f x))) := by
      have hdct := tendsto_integral_filter_of_dominated_convergence
        (μ := (volume : Measure (EuclideanSpace ℝ (Fin n))))
        (l := nhdsWithin (0:ℝ) (Set.Ioi 0))
        (F := fun (ε : ℝ) => Set.indicator {y : EuclideanSpace ℝ (Fin n) | ε < ‖x - y‖}
          (fun y => GaussRieszKernel j x y * (f y - f x)))
        (f := fun y : EuclideanSpace ℝ (Fin n) => GaussRieszKernel j x y * (f y - f x))
        (fun y => ‖GaussRieszKernel j x y * (f y - f x)‖)
        (Filter.Eventually.of_forall fun ε =>
          hint10.aestronglyMeasurable.indicator (hΩm ε))
        (Filter.Eventually.of_forall fun ε => Filter.Eventually.of_forall fun y =>
          norm_indicator_le_norm_self _ _)
        hint10.norm ?_
      · refine hdct.congr fun ε => ?_
        exact integral_indicator (hΩm ε)
      · filter_upwards [h0] with y hy
        have hpos : 0 < ‖x - y‖ := by
          rw [norm_pos_iff, sub_ne_zero]
          exact fun h => hy h.symm
        refine Filter.Tendsto.congr' ?_ tendsto_const_nhds
        filter_upwards [Filter.Eventually.filter_mono nhdsWithin_le_nhds (gt_mem_nhds hpos)]
          with ε hεy
        exact (Set.indicator_of_mem
          (show y ∈ {y' : EuclideanSpace ℝ (Fin n) | ε < ‖x - y'‖} from hεy)
          (fun y => GaussRieszKernel j x y * (f y - f x))).symm
    have hlim2 : Filter.Tendsto
        (fun ε : ℝ => f x * ∫ y in {y : EuclideanSpace ℝ (Fin n) | ε < ‖x - y‖},
          GaussRieszKernel j x y)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
      simpa using ((PVKernelConstantCancellation j x).2.2).const_mul (f x)
    have heq : ∀ ε : ℝ, 0 < ε →
        (∫ y in {y : EuclideanSpace ℝ (Fin n) | ε < ‖x - y‖},
            GaussRieszKernel j x y * (f y - f x))
          + f x * ∫ y in {y : EuclideanSpace ℝ (Fin n) | ε < ‖x - y‖}, GaussRieszKernel j x y
        = ∫ y in {y : EuclideanSpace ℝ (Fin n) | ε < ‖x - y‖}, GaussRieszKernel j x y * f y := by
      intro ε hε
      have hKε := (PVKernelConstantCancellation j x).2.1 ε hε
      have h1 : IntegrableOn (fun y : EuclideanSpace ℝ (Fin n) =>
          GaussRieszKernel j x y * (f y - f x))
          {y : EuclideanSpace ℝ (Fin n) | ε < ‖x - y‖} volume := hint10.integrableOn
      have h2 : IntegrableOn (fun y : EuclideanSpace ℝ (Fin n) =>
          f x * GaussRieszKernel j x y)
          {y : EuclideanSpace ℝ (Fin n) | ε < ‖x - y‖} volume :=
        Integrable.const_mul hKε (f x)
      rw [← integral_const_mul, ← integral_add h1 h2]
      exact integral_congr_ae (Filter.Eventually.of_forall fun y => by ring)
    rw [← h10]
    refine Filter.Tendsto.congr' ?_ (by simpa using hlim.add hlim2)
    filter_upwards [self_mem_nhdsWithin] with ε hε
    exact heq ε hε
