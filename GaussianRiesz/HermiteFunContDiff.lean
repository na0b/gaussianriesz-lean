module

public import GaussianRiesz.HermiteFun
public import Mathlib.Analysis.Calculus.ContDiff.Polynomial

@[expose] public section
theorem HermiteFunContDiff {n : ℕ} (α : Fin n → ℕ) :
    ContDiff ℝ (⊤ : ℕ∞) (HermiteFun α) := by
  unfold HermiteFun
  refine contDiff_prod fun j _ => ?_
  have h1 : ContDiff ℝ (⊤ : ℕ∞) (Hermite1 (α j)) := by
    unfold Hermite1
    exact ((Polynomial.contDiff_aeval _ _).comp
      (contDiff_const.mul contDiff_id)).div_const _
  exact h1.comp ((EuclideanSpace.proj (𝕜 := ℝ) j).contDiff (n := (⊤ : ℕ∞)))
