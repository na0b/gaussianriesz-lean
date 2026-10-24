import GaussianRiesz.SmoothCompactDenseL1Gauss
import GaussianRiesz.GaussRieszKernelFarMajorant
import GaussianRiesz.GaussLebesgueBallComparison
open MeasureTheory Metric
open scoped ENNReal
theorem GaussRieszTruncationSmoothSplit {n : ℕ} (f : Lp ℝ 1 (GaussMeasure n)) (k : ℕ) :
    ∃ (φ : EuclideanSpace ℝ (Fin n) → ℝ) (g : Lp ℝ 1 (GaussMeasure n)),
      ContDiff ℝ (⊤ : ℕ∞) φ ∧ HasCompactSupport φ ∧ MemLp φ 1 (GaussMeasure n)
        ∧ (∫ y, |(g : EuclideanSpace ℝ (Fin n) → ℝ) y| ∂(GaussMeasure n)) < 1 / ((k : ℝ) + 1)
        ∧ ((f : EuclideanSpace ℝ (Fin n) → ℝ)
            =ᵐ[GaussMeasure n] fun y => φ y + (g : EuclideanSpace ℝ (Fin n) → ℝ) y)
        ∧ ∀ (j : Fin n) (x : EuclideanSpace ℝ (Fin n)) (ε : ℝ), 0 < ε →
            IntegrableOn (fun y => GaussRieszKernel j x y
                * (f : EuclideanSpace ℝ (Fin n) → ℝ) y)
              {y : EuclideanSpace ℝ (Fin n) | ε < ‖x - y‖} volume
            ∧ IntegrableOn (fun y => GaussRieszKernel j x y * φ y)
              {y : EuclideanSpace ℝ (Fin n) | ε < ‖x - y‖} volume
            ∧ IntegrableOn (fun y => GaussRieszKernel j x y
                * (g : EuclideanSpace ℝ (Fin n) → ℝ) y)
              {y : EuclideanSpace ℝ (Fin n) | ε < ‖x - y‖} volume
            ∧ (∫ y in {y : EuclideanSpace ℝ (Fin n) | ε < ‖x - y‖},
                  GaussRieszKernel j x y * (f : EuclideanSpace ℝ (Fin n) → ℝ) y)
                = (∫ y in {y : EuclideanSpace ℝ (Fin n) | ε < ‖x - y‖},
                    GaussRieszKernel j x y * φ y)
                  + ∫ y in {y : EuclideanSpace ℝ (Fin n) | ε < ‖x - y‖},
                      GaussRieszKernel j x y * (g : EuclideanSpace ℝ (Fin n) → ℝ) y := by
  classical
  -- STEP 1: the approximant
  obtain ⟨φ, hφsm, hφcs, hφmem, hφnorm⟩ :=
    SmoothCompactDenseL1Gauss f (1 / ((k : ℝ) + 1)) (by positivity)
  have hgae : ((f - hφmem.toLp φ : Lp ℝ 1 (GaussMeasure n))
      : EuclideanSpace ℝ (Fin n) → ℝ)
      =ᵐ[GaussMeasure n] fun y => (f : EuclideanSpace ℝ (Fin n) → ℝ) y - φ y := by
    filter_upwards [Lp.coeFn_sub f (hφmem.toLp φ), hφmem.coeFn_toLp] with y h1 h2
    rw [h1, Pi.sub_apply, h2]
  refine ⟨φ, f - hφmem.toLp φ, hφsm, hφcs, hφmem, ?_, ?_, ?_⟩
  · -- the `L¹(γ)` smallness, in the `(A2)` form the consumer uses
    have hgint : Integrable ((f - hφmem.toLp φ : Lp ℝ 1 (GaussMeasure n))
        : EuclideanSpace ℝ (Fin n) → ℝ) (GaussMeasure n) :=
      memLp_one_iff_integrable.1 (Lp.memLp _)
    refine (ENNReal.ofReal_lt_ofReal_iff (by positivity)).1 ?_
    calc ENNReal.ofReal (∫ y, |((f - hφmem.toLp φ : Lp ℝ 1 (GaussMeasure n))
            : EuclideanSpace ℝ (Fin n) → ℝ) y| ∂(GaussMeasure n))
        = ∫⁻ y, ‖((f - hφmem.toLp φ : Lp ℝ 1 (GaussMeasure n))
            : EuclideanSpace ℝ (Fin n) → ℝ) y‖ₑ ∂(GaussMeasure n) := by
          rw [← ofReal_integral_norm_eq_lintegral_enorm hgint]
          simp [Real.norm_eq_abs]
      _ = eLpNorm ((f - hφmem.toLp φ : Lp ℝ 1 (GaussMeasure n))
            : EuclideanSpace ℝ (Fin n) → ℝ) 1 (GaussMeasure n) := by
          rw [eLpNorm_one_eq_lintegral_enorm]
      _ = eLpNorm (fun y => (f : EuclideanSpace ℝ (Fin n) → ℝ) y - φ y) 1
            (GaussMeasure n) := eLpNorm_congr_ae hgae
      _ < ENNReal.ofReal (1 / ((k : ℝ) + 1)) := hφnorm
  · -- `f = φ + g` as `L¹(γ)` classes, at the level of representatives
    filter_upwards [hgae] with y hy
    rw [hy]
    ring
  -- STEP 2: finiteness of every truncation, and the three-term splitting
  intro j x ε hε
  obtain ⟨C, hC0, hpt, hfar⟩ :=
    (GaussRieszKernelFarMajorant j).1 (max ‖x‖ 1) ε (lt_of_lt_of_le one_pos (le_max_right _ _)) hε
  have hxR : ‖x‖ ≤ max ‖x‖ 1 := le_max_left _ _
  have hacv : (volume : Measure (EuclideanSpace ℝ (Fin n))) ≪ GaussMeasure n := by
    have h4 := (GaussLebesgueBallComparison (n := n)).2.2.2
    exact Measure.AbsolutelyContinuous.mk fun s _ hs0 => (h4 s).1 hs0
  have hgaev : ((f - hφmem.toLp φ : Lp ℝ 1 (GaussMeasure n))
      : EuclideanSpace ℝ (Fin n) → ℝ)
      =ᵐ[volume] fun y => (f : EuclideanSpace ℝ (Fin n) → ℝ) y - φ y := by
    refine hacv.ae_eq ?_
    filter_upwards [Lp.coeFn_sub f (hφmem.toLp φ), hφmem.coeFn_toLp] with y h1 h2
    rw [h1, Pi.sub_apply, h2]
  have h1 := (hfar (f : EuclideanSpace ℝ (Fin n) → ℝ) (Lp.memLp f) x hxR).1
  have h2 := (hfar φ hφmem x hxR).1
  have h3 := (hfar ((f - hφmem.toLp φ : Lp ℝ 1 (GaussMeasure n))
    : EuclideanSpace ℝ (Fin n) → ℝ) (Lp.memLp _) x hxR).1
  refine ⟨h1, h2, h3, ?_⟩
  rw [← integral_add h2 h3]
  refine setIntegral_congr_ae (measurableSet_lt measurable_const (by fun_prop)) ?_
  filter_upwards [hgaev] with y hy _
  rw [hy]
  ring
