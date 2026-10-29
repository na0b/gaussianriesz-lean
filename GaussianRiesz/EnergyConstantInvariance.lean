module

public import GaussianRiesz.EnergyBil
public import GaussianRiesz.HermiteL2
public import GaussianRiesz.Hermite1Zero

@[expose] public section
open MeasureTheory
theorem EnergyConstantInvariance {n : ℕ} (v : Lp ℝ 2 (GaussMeasure n)) (c : ℝ) :
    EnergyBil v (HermiteL2 (0 : Fin n → ℕ)) = 0
      ∧ Energy (v + c • HermiteL2 (0 : Fin n → ℕ)) = Energy v := by
  classical
  -- `HermiteL2` is literally the basis family of `HermiteBasis`
  have hcoe : ((HermiteBasis n) : (Fin n → ℕ) → Lp ℝ 2 (GaussMeasure n))
      = HermiteL2 (n := n) := HilbertBasis.coe_mk _ _
  -- so the index-`0` element has vanishing coefficients away from `0`
  have hzero : ∀ α : Fin n → ℕ, α ≠ 0 →
      (HermiteBasis n).repr (HermiteL2 (0 : Fin n → ℕ)) α = 0 := by
    intro α hα
    have h0 : HermiteL2 (0 : Fin n → ℕ) = (HermiteBasis n) (0 : Fin n → ℕ) := by
      rw [hcoe]
    rw [h0, HilbertBasis.repr_self, lp.single_apply_ne _ _ _ hα]
  refine ⟨?_, ?_⟩
  · -- every term of the defining series carries the factor `(h₀)_α` with `α ≠ 0`
    rw [EnergyBil]
    rw [tsum_congr (fun α : {α : Fin n → ℕ // α ≠ 0} => ?_), tsum_zero]
    rw [hzero (α : Fin n → ℕ) α.2, mul_zero]
  · -- the coefficients at indices `α ≠ 0` are unchanged
    have key : ∀ α : Fin n → ℕ, α ≠ 0 →
        (HermiteBasis n).repr (v + c • HermiteL2 (0 : Fin n → ℕ)) α
          = (HermiteBasis n).repr v α := by
      intro α hα
      rw [map_add, map_smul, lp.coeFn_add, Pi.add_apply, lp.coeFn_smul, Pi.smul_apply,
        hzero α hα, smul_zero, add_zero]
    rw [Energy, Energy]
    exact tsum_congr fun α => by rw [key (α : Fin n → ℕ) α.2]
