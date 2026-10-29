module

public import GaussianRiesz.EnergyBil
public import GaussianRiesz.FracPow

@[expose] public section
open MeasureTheory
theorem EnergyBilIsOperator {n : ℕ} (v w : Lp ℝ 2 (GaussMeasure n))
    (hv : v ∈ FracPowDomain ((1 : ℝ) / 2)) :
    EnergyBil v w = inner ℝ (FracPow ((1 : ℝ) / 2) v) w := by
  classical
  -- Step 1: the coefficients of `L^{1/2} v`
  have hv' : Memℓp (FracPowCoeff ((1 : ℝ) / 2)
      (fun α => (HermiteBasis n).repr v α)) 2 := hv
  have hval : FracPow ((1 : ℝ) / 2) v = (HermiteBasis n).repr.symm ⟨_, hv'⟩ := by
    simp only [FracPow]
    rw [dif_pos hv']
  have hcoef : ∀ α : Fin n → ℕ,
      (HermiteBasis n).repr (FracPow ((1 : ℝ) / 2) v) α
        = FracPowCoeff ((1 : ℝ) / 2) (fun β => (HermiteBasis n).repr v β) α := by
    intro α
    rw [hval, LinearIsometryEquiv.apply_symm_apply]
  -- Step 2: Parseval for the inner product
  have hinner : inner ℝ (FracPow ((1 : ℝ) / 2) v) w
      = ∑' α : Fin n → ℕ,
          FracPowCoeff ((1 : ℝ) / 2) (fun β => (HermiteBasis n).repr v β) α
            * (HermiteBasis n).repr w α := by
    rw [← (HermiteBasis n).repr.inner_map_map (FracPow ((1 : ℝ) / 2) v) w, lp.inner_eq_tsum]
    refine tsum_congr fun α => ?_
    rw [hcoef α]
    simp [RCLike.inner_apply, mul_comm]
  -- Step 3: the index `α = 0` drops out, leaving the defining series of `E(v,w)`
  rw [hinner, EnergyBil]
  have hsupp : Function.support (fun α : Fin n → ℕ =>
      FracPowCoeff ((1 : ℝ) / 2) (fun β => (HermiteBasis n).repr v β) α
        * (HermiteBasis n).repr w α)
      ⊆ {α : Fin n → ℕ | α ≠ 0} := by
    intro α hα
    by_contra hcon
    have hz : α = 0 := not_not.mp hcon
    simp only [Function.mem_support] at hα
    exact hα (by simp [hz, FracPowCoeff])
  rw [← tsum_subtype_eq_of_support_subset hsupp]
  refine tsum_congr fun x => ?_
  have hx : (x : Fin n → ℕ) ≠ 0 := x.2
  simp only [FracPowCoeff, if_neg hx]
