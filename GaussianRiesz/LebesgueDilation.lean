module

public import GaussianRiesz.Preamble
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

@[expose] public section
open MeasureTheory
open scoped ENNReal Pointwise
theorem LebesgueDilation {n : ℕ} :
    (∀ (c : ℝ) (A : Set (EuclideanSpace ℝ (Fin n))),
        volume (c • A) = ENNReal.ofReal (|c| ^ n) * volume A)
      ∧ (∀ c : ℝ, c ≠ 0 → ∀ N : Set (EuclideanSpace ℝ (Fin n)),
          volume N = 0 → volume ((fun z : EuclideanSpace ℝ (Fin n) => c • z) ⁻¹' N) = 0) := by
  constructor
  · intro c A
    rw [Measure.addHaar_smul (volume : Measure (EuclideanSpace ℝ (Fin n))) c A,
      finrank_euclideanSpace_fin, abs_pow]
  · intro c hc N hN
    rw [Measure.addHaar_preimage_smul (volume : Measure (EuclideanSpace ℝ (Fin n))) hc, hN,
      mul_zero]
