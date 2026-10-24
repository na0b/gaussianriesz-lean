import GaussianRiesz.HermiteL2
import GaussianRiesz.HermiteFunMemLp
import GaussianRiesz.Hermite1Zero
open MeasureTheory
theorem HermiteL2ZeroAEOne {n : ℕ} :
    ((HermiteL2 (0 : Fin n → ℕ) : Lp ℝ 2 (GaussMeasure n)) :
      EuclideanSpace ℝ (Fin n) → ℝ) =ᵐ[GaussMeasure n] fun _ => 1 := by
  -- `He₀ = 1`, so the zeroth Hermite function is identically `1`
  have hfun1 : ∀ x : EuclideanSpace ℝ (Fin n), HermiteFun (0 : Fin n → ℕ) x = 1 := by
    intro x
    unfold HermiteFun
    simp [Hermite1Zero]
  exact (HermiteFunMemLp (0 : Fin n → ℕ)).coeFn_toLp.trans
    (Filter.Eventually.of_forall hfun1)
