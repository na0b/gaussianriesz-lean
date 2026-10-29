module

public import GaussianRiesz.NonnegTestCharacterization
public import GaussianRiesz.ObstacleCone
public import GaussianRiesz.L2InnerGaussIntegral

@[expose] public section
open MeasureTheory
theorem ConeWeaklyClosed {n : ℕ} (vk : ℕ → Lp ℝ 2 (GaussMeasure n))
    (v : Lp ℝ 2 (GaussMeasure n))
    (hk : ∀ k, 0 ≤ᵐ[GaussMeasure n] ((vk k : EuclideanSpace ℝ (Fin n) → ℝ)))
    (hconv : ∀ φ : Lp ℝ 2 (GaussMeasure n),
      Filter.Tendsto (fun k => inner ℝ (vk k) φ) Filter.atTop (nhds (inner ℝ v φ))) :
    0 ≤ᵐ[GaussMeasure n] (v : EuclideanSpace ℝ (Fin n) → ℝ) := by
  rw [NonnegTestCharacterization v]
  intro φ hφ
  rw [← L2InnerGaussIntegral v φ]
  refine ge_of_tendsto (hconv φ) ?_
  filter_upwards with k
  rw [L2InnerGaussIntegral (vk k) φ]
  exact (NonnegTestCharacterization (vk k)).mp (hk k) φ hφ
