import GaussianRiesz.PVCoreSmooth
import GaussianRiesz.RieszSemigroupPointwise
open MeasureTheory
open scoped ENNReal
theorem SmoothCoreTruncationBridge {n : ℕ}
    (T : Lp ℝ 1 (GaussMeasure n) →ₗ[ℝ]
      (EuclideanSpace ℝ (Fin n) →ₘ[GaussMeasure n] EuclideanSpace ℝ (Fin n)))
    (hext : ∀ v : Lp ℝ 2 (GaussMeasure n),
      T (ToL1 v) = (RieszTransform v : EuclideanSpace ℝ (Fin n)
        →ₘ[GaussMeasure n] EuclideanSpace ℝ (Fin n)))
    (φ : EuclideanSpace ℝ (Fin n) → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφc : HasCompactSupport φ) (hφmem : MemLp φ 1 (GaussMeasure n)) (j : Fin n) :
    ∀ᵐ x ∂(GaussMeasure n),
      Filter.Tendsto
        (fun ε : ℝ => ∫ y in {y : EuclideanSpace ℝ (Fin n) | ε < ‖x - y‖},
          GaussRieszKernel j x y * φ y)
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds ((T (hφmem.toLp φ) : EuclideanSpace ℝ (Fin n)
          → EuclideanSpace ℝ (Fin n)) x j)) := by
  classical
  -- (a) a smooth compactly supported function is bounded, hence in `L²(γ)`
  obtain ⟨C, hC⟩ := HasCompactSupport.exists_bound_of_continuous hφc hφ.continuous
  have hmem2 : MemLp φ 2 (GaussMeasure n) :=
    MemLp.of_bound hφ.continuous.aestronglyMeasurable C (Filter.Eventually.of_forall hC)
  -- (b) the spectral identification of the smooth core
  obtain ⟨-, -, hae⟩ := RieszSemigroupPointwise φ hφ hφc hmem2 j
  -- (c) `(T1)` pins `T` on the class of `φ`
  have hTeq : T (hφmem.toLp φ)
      = (RieszTransform (hmem2.toLp φ) : EuclideanSpace ℝ (Fin n)
          →ₘ[GaussMeasure n] EuclideanSpace ℝ (Fin n)) := by
    rw [← show ToL1 (hmem2.toLp φ) = hφmem.toLp φ from by
      rw [ToL1]; exact MemLp.toLp_congr _ _ (MemLp.coeFn_toLp hmem2)]
    exact hext _
  filter_upwards [hae] with x hx
  rw [hTeq, ← hx]
  exact (PVCoreSmooth φ hφ hφc j x).2
