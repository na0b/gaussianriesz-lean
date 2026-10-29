module

public import GaussianRiesz.GaussRieszKernel
public import GaussianRiesz.MehlerKernelXDerivative
public import GaussianRiesz.MehlerKernelSliceVanishing
public import GaussianRiesz.PVTruncatedSliceMajorant
public import GaussianRiesz.PVKernelTimeIntegral
public import GaussianRiesz.PVTruncatedTimeSliceFinite
public import GaussianRiesz.SubordinationWeightIntegral
public import GaussianRiesz.GaussIsProb

@[expose] public section
open MeasureTheory
theorem PVKernelConstantCancellation {n : ℕ} (j : Fin n) (x : EuclideanSpace ℝ (Fin n)) :
    (∀ s : ℝ, 0 < s →
        Integrable (fun y : EuclideanSpace ℝ (Fin n) =>
            Real.sqrt 2 * Real.exp (-s) * (y j - Real.exp (-s) * x j) / (1 - Real.exp (-2 * s))
              * (Real.pi ^ (-(n : ℝ) / 2) * (1 - Real.exp (-2 * s)) ^ (-(n : ℝ) / 2)
                  * Real.exp (-‖Real.exp (-s) • x - y‖ ^ 2 / (1 - Real.exp (-2 * s)))))
            volume
          ∧ ∫ y : EuclideanSpace ℝ (Fin n),
              Real.sqrt 2 * Real.exp (-s) * (y j - Real.exp (-s) * x j) / (1 - Real.exp (-2 * s))
                * (Real.pi ^ (-(n : ℝ) / 2) * (1 - Real.exp (-2 * s)) ^ (-(n : ℝ) / 2)
                    * Real.exp (-‖Real.exp (-s) • x - y‖ ^ 2 / (1 - Real.exp (-2 * s)))) = 0)
      ∧ (∀ ε : ℝ, 0 < ε →
          IntegrableOn (fun y : EuclideanSpace ℝ (Fin n) => GaussRieszKernel j x y)
            {y : EuclideanSpace ℝ (Fin n) | ε < ‖x - y‖} volume)
      ∧ Filter.Tendsto
          (fun ε : ℝ => ∫ y in {y : EuclideanSpace ℝ (Fin n) | ε < ‖x - y‖},
            GaussRieszKernel j x y)
          (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
  -- Clause (1) is `MehlerKernelSliceVanishing`: after the translation `y = e^{-s} x + w`
  -- the integrand is an odd multiple of a Gaussian in `w`, so the vanishing is oddness
  -- rather than an estimate, and the integrability is the Gaussian majorant.
  -- Clauses (2) and (3) are Steps 4-7 of the `.tex`.  Steps 2 and 4 -- the
  -- `ε`-independent majorant `|I_{ε,s}| ≤ C |x| e^{-s}` and the fixed-`s` limit
  -- `I_{ε,s} → 0` -- are `PVTruncatedSliceMajorant`, and Step 5, the `ρ = e^{-s}`
  -- time-integral representation of `K_{γ,j}` together with its integrability
  -- equivalence, is `PVKernelTimeIntegral`.  What remains is Steps 6 and 7: the
  -- two-regime bound on `∫_{Ω_ε} |D_j^x p_s|`, the Fubini exchange on `Ω_ε × (0,∞)`,
  -- and the dominated convergence in `ε`.  The two-regime bound, in the integral-upper
  -- form that Tonelli consumes, is `PVTruncatedTimeSliceFinite`; the exchange itself and
  -- the dominated convergence are below.
  refine ⟨MehlerKernelSliceVanishing j x, ?_⟩
  obtain ⟨D, hD⟩ : ∃ D : ℝ → EuclideanSpace ℝ (Fin n) → ℝ,
      ∀ (s : ℝ) (y : EuclideanSpace ℝ (Fin n)), D s y =
        Real.sqrt 2 * Real.exp (-s) * (y j - Real.exp (-s) * x j) / (1 - Real.exp (-2 * s))
          * (Real.pi ^ (-(n : ℝ) / 2) * (1 - Real.exp (-2 * s)) ^ (-(n : ℝ) / 2)
              * Real.exp (-‖Real.exp (-s) • x - y‖ ^ 2 / (1 - Real.exp (-2 * s)))) :=
    ⟨_, fun _ _ => rfl⟩
  have hjm : Measurable
      (Function.uncurry (fun (y : EuclideanSpace ℝ (Fin n)) (s : ℝ) => (Real.sqrt s)⁻¹ * D s y)) := by
    simp only [hD]
    fun_prop
  -- STEP 6: integrability on the product of the truncated region and the time half-line
  have hF : ∀ ε : ℝ, 0 < ε →
      Integrable (Function.uncurry
          (fun (y : EuclideanSpace ℝ (Fin n)) (s : ℝ) => (Real.sqrt s)⁻¹ * D s y))
        ((volume.restrict {y : EuclideanSpace ℝ (Fin n) | ε < ‖x - y‖}).prod
          (volume.restrict (Set.Ioi (0:ℝ)))) := by
    intro ε hε
    have hfin : ∫⁻ s in Set.Ioi (0 : ℝ), ENNReal.ofReal ((Real.sqrt s)⁻¹)
        * ∫⁻ y in {y : EuclideanSpace ℝ (Fin n) | ε < ‖x - y‖}, ‖D s y‖ₑ < ⊤ := by
      refine lt_of_le_of_lt (le_of_eq ?_) (PVTruncatedTimeSliceFinite j x ε hε)
      refine lintegral_congr fun s => ?_
      congr 1
      exact lintegral_congr fun y => by rw [hD]
    refine ⟨hjm.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_enorm, lintegral_prod_symm _ hjm.enorm.aemeasurable]
    refine lt_of_le_of_lt (le_of_eq ?_) hfin
    refine lintegral_congr fun s => ?_
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine lintegral_congr fun y => ?_
    rw [Function.uncurry_apply_pair, enorm_mul,
      Real.enorm_eq_ofReal (by positivity : (0:ℝ) ≤ (Real.sqrt s)⁻¹)]
  refine ⟨fun ε hε => ?_, ?_⟩
  · -- clause (2): truncated absolute integrability of the kernel
    refine (((hF ε hε).integral_prod_left).const_mul (Real.sqrt Real.pi)⁻¹).congr
      (Filter.Eventually.of_forall fun y => ?_)
    simp only [Function.uncurry_apply_pair, hD]
    exact ((PVKernelTimeIntegral j x y).2).symm
  · -- STEP 7: dominated convergence in the time variable
    obtain ⟨C, hC0, hCbd⟩ := (PVTruncatedSliceMajorant j x).1
    have hvan := (PVTruncatedSliceMajorant j x).2
    have hbi : IntegrableOn
        (fun s : ℝ => C * ‖x‖ * ((Real.sqrt s)⁻¹ * Real.exp (-s))) (Set.Ioi (0:ℝ)) volume :=
      SubordinationWeightIntegral.1.const_mul _
    have key : Filter.Tendsto
        (fun ε : ℝ => ∫ s in Set.Ioi (0:ℝ),
            (Real.sqrt s)⁻¹ * ∫ y in {y : EuclideanSpace ℝ (Fin n) | ε < ‖x - y‖}, D s y)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds (∫ _s in Set.Ioi (0:ℝ), (0:ℝ))) := by
      refine tendsto_integral_filter_of_dominated_convergence _ ?_ ?_ hbi ?_
      · filter_upwards [self_mem_nhdsWithin] with ε hε
        refine ((hF ε hε).integral_prod_right.aestronglyMeasurable).congr
          (Filter.Eventually.of_forall fun s => ?_)
        simp only [Function.uncurry_apply_pair]
        exact integral_const_mul (Real.sqrt s)⁻¹ (fun y => D s y)
      · filter_upwards [self_mem_nhdsWithin] with ε hε
        refine (ae_restrict_iff' measurableSet_Ioi).2 (Filter.Eventually.of_forall fun s hs => ?_)
        have h2 : |∫ y in {y : EuclideanSpace ℝ (Fin n) | ε < ‖x - y‖}, D s y|
            ≤ C * ‖x‖ * Real.exp (-s) := by
          simpa only [hD] using hCbd ε s hε (Set.mem_Ioi.1 hs)
        rw [Real.norm_eq_abs, abs_mul,
          abs_of_nonneg (by positivity : (0:ℝ) ≤ (Real.sqrt s)⁻¹)]
        calc (Real.sqrt s)⁻¹ * |∫ y in {y : EuclideanSpace ℝ (Fin n) | ε < ‖x - y‖}, D s y|
            ≤ (Real.sqrt s)⁻¹ * (C * ‖x‖ * Real.exp (-s)) :=
              mul_le_mul_of_nonneg_left h2 (by positivity)
          _ = C * ‖x‖ * ((Real.sqrt s)⁻¹ * Real.exp (-s)) := by ring
      · refine (ae_restrict_iff' measurableSet_Ioi).2 (Filter.Eventually.of_forall fun s hs => ?_)
        have := (hvan s (Set.mem_Ioi.1 hs)).const_mul ((Real.sqrt s)⁻¹)
        simpa only [hD, mul_zero] using this
    -- assemble: the kernel's truncated integral is the time integral of the slice integrals
    have hchain : ∀ ε : ℝ, 0 < ε →
        (Real.sqrt Real.pi)⁻¹ * ∫ s in Set.Ioi (0:ℝ),
            (Real.sqrt s)⁻¹ * ∫ y in {y : EuclideanSpace ℝ (Fin n) | ε < ‖x - y‖}, D s y
          = ∫ y in {y : EuclideanSpace ℝ (Fin n) | ε < ‖x - y‖}, GaussRieszKernel j x y := by
      intro ε hε
      have e1 : ∫ y in {y : EuclideanSpace ℝ (Fin n) | ε < ‖x - y‖}, GaussRieszKernel j x y
          = ∫ y in {y : EuclideanSpace ℝ (Fin n) | ε < ‖x - y‖},
              (Real.sqrt Real.pi)⁻¹ * ∫ s in Set.Ioi (0:ℝ), (Real.sqrt s)⁻¹ * D s y := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
        simp only [hD]
        exact (PVKernelTimeIntegral j x y).2
      rw [e1, integral_const_mul]
      congr 1
      rw [integral_integral_swap (hF ε hε)]
      refine integral_congr_ae (Filter.Eventually.of_forall fun s => ?_)
      exact (integral_const_mul _ _).symm
    refine Filter.Tendsto.congr' ?_ (by simpa using key.const_mul (Real.sqrt Real.pi)⁻¹)
    filter_upwards [self_mem_nhdsWithin] with ε hε
    exact hchain ε hε
