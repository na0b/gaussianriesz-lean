module

public import GaussianRiesz.GaussMaximalTruncationLocal
public import GaussianRiesz.CoordinateEndpointBound
public import GaussianRiesz.SmoothCompactDenseL1Gauss
public import GaussianRiesz.PVCoreSmooth
public import GaussianRiesz.GaussRieszKernelFarMajorant
public import GaussianRiesz.L1Extension
public import GaussianRiesz.GaussRieszTruncationSmoothSplit
public import GaussianRiesz.SmoothCoreTruncationBridge
public import GaussianRiesz.GaussRieszPrincipalValueExists
public import GaussianRiesz.GaussRieszPrincipalValueIsOperator

@[expose] public section
open MeasureTheory
open scoped ENNReal
set_option linter.unusedVariables false
theorem PVIdentification {n : ℕ}
    (T : Lp ℝ 1 (GaussMeasure n) →ₗ[ℝ]
      (EuclideanSpace ℝ (Fin n) →ₘ[GaussMeasure n] EuclideanSpace ℝ (Fin n)))
    (hext : ∀ v : Lp ℝ 2 (GaussMeasure n),
      T (ToL1 v) = (RieszTransform v : EuclideanSpace ℝ (Fin n)
        →ₘ[GaussMeasure n] EuclideanSpace ℝ (Fin n)))
    (hT : ∀ (f : Lp ℝ 1 (GaussMeasure n)) (t : ℝ), 0 < t →
      ENNReal.ofReal t * GaussMeasure n {x | t < ‖T f x‖} ≤ ENNReal.ofReal (2 * ‖f‖))
    (f : Lp ℝ 1 (GaussMeasure n)) :
    (∀ᵐ x ∂(GaussMeasure n), ∀ j : Fin n,
        Filter.Tendsto
          (fun ε : ℝ => ∫ y in {y : EuclideanSpace ℝ (Fin n) | ε < ‖x - y‖},
            GaussRieszKernel j x y * (f : EuclideanSpace ℝ (Fin n) → ℝ) y)
          (nhdsWithin 0 (Set.Ioi 0)) (nhds (T f x j)))
      ∧ (∀ F : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n),
          (∀ᵐ x ∂(GaussMeasure n), ∀ j : Fin n,
              Filter.Tendsto
                (fun ε : ℝ => ∫ y in {y : EuclideanSpace ℝ (Fin n) | ε < ‖x - y‖},
                  GaussRieszKernel j x y * (f : EuclideanSpace ℝ (Fin n) → ℝ) y)
                (nhdsWithin 0 (Set.Ioi 0)) (nhds (F x j))) →
          ∀ t : ℝ, 0 < t →
            ENNReal.ofReal t * GaussMeasure n {x | t < ‖F x‖}
              ≤ ENNReal.ofReal (2 * ‖f‖)) := by
  classical
  -- STEP 9: the coordinate assembly, giving clause (1)
  have hclause1 : ∀ᵐ x ∂(GaussMeasure n), ∀ j : Fin n,
      Filter.Tendsto
        (fun ε : ℝ => ∫ y in {y : EuclideanSpace ℝ (Fin n) | ε < ‖x - y‖},
          GaussRieszKernel j x y * (f : EuclideanSpace ℝ (Fin n) → ℝ) y)
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds ((T f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) x j)) := by
    refine ae_all_iff.mpr fun j => ?_
    filter_upwards [GaussRieszPrincipalValueExists T hext hT f j,
      GaussRieszPrincipalValueIsOperator T hext hT f j] with x hx1 hx2
    obtain ⟨L, hL⟩ := hx1
    rw [← hx2 L hL]
    exact hL
  refine ⟨hclause1, ?_⟩
  -- STEP 10: clause (2)
  intro F hF t ht
  have hFeq : ∀ᵐ x ∂(GaussMeasure n),
      F x = (T f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) x := by
    filter_upwards [hclause1, hF] with x h1 h2
    ext j
    exact tendsto_nhds_unique (h2 j) (h1 j)
  have hset : {x : EuclideanSpace ℝ (Fin n) | t < ‖F x‖}
      =ᵐ[GaussMeasure n] {x : EuclideanSpace ℝ (Fin n) | t <
        ‖(T f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) x‖} := by
    filter_upwards [hFeq] with x hx
    exact congrArg (fun v : EuclideanSpace ℝ (Fin n) => t < ‖v‖) hx
  rw [measure_congr hset]
  exact hT f t ht
