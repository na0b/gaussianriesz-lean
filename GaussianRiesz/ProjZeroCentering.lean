import GaussianRiesz.FracPow
import GaussianRiesz.HermiteL2
import GaussianRiesz.Hermite1Zero
import GaussianRiesz.HermiteZeroModeConstant
import GaussianRiesz.FracPowLinear
open MeasureTheory
theorem ProjZeroCentering {n : ℕ} (v : Lp ℝ 2 (GaussMeasure n)) :
    FracPow (0 : ℝ) v
      = v - (∫ x, (v : EuclideanSpace ℝ (Fin n) → ℝ) x ∂(GaussMeasure n))
            • HermiteL2 (0 : Fin n → ℕ) := by
  classical
  have hcoe : ((HermiteBasis n) : (Fin n → ℕ) → Lp ℝ 2 (GaussMeasure n))
      = HermiteL2 (n := n) := HilbertBasis.coe_mk _ _
  have hb0 : HermiteL2 (0 : Fin n → ℕ) = (HermiteBasis n) (0 : Fin n → ℕ) := by rw [hcoe]
  -- the coefficients of `h₀`
  have hrepr0 : ∀ α : Fin n → ℕ,
      (HermiteBasis n).repr (HermiteL2 (0 : Fin n → ℕ)) α
        = if α = (0 : Fin n → ℕ) then (1 : ℝ) else 0 := by
    intro α
    rw [hb0, HilbertBasis.repr_self]
    simp [lp.single_apply, Pi.single_apply]
  -- the zeroth coefficient of `v` is its mean
  have hmean : (HermiteBasis n).repr v (0 : Fin n → ℕ)
      = ∫ x, (v : EuclideanSpace ℝ (Fin n) → ℝ) x ∂(GaussMeasure n) := by
    rw [HilbertBasis.repr_apply_apply, ← hb0, (HermiteZeroModeConstant (n := n)).2.2.1 v]
  -- `v ∈ Dom(L⁰)`
  have h0 : Memℓp (FracPowCoeff (0 : ℝ) (fun α => (HermiteBasis n).repr v α)) 2 :=
    (FracPowLinear (0 : ℝ)).1 le_rfl v
  have hvalue : FracPow (0 : ℝ) v = (HermiteBasis n).repr.symm ⟨_, h0⟩ := by
    simp only [FracPow]
    rw [dif_pos h0]
  -- compare the two coefficient families
  rw [hvalue]
  refine (HermiteBasis n).repr.injective ?_
  rw [LinearIsometryEquiv.apply_symm_apply, map_sub, map_smul]
  refine lp.ext (funext fun α => ?_)
  simp only [lp.coeFn_sub, lp.coeFn_smul, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  simp only [FracPowCoeff]
  by_cases hα : α = (0 : Fin n → ℕ)
  · rw [if_pos hα, hrepr0, if_pos hα, hα, hmean]
    ring
  · rw [if_neg hα, hrepr0, if_neg hα, Real.rpow_zero, one_mul]
    ring
