module

public import GaussianRiesz.ProjZeroCentering
public import GaussianRiesz.Energy
public import GaussianRiesz.OneLeMultiIndexSum
public import GaussianRiesz.FracPowLinear

@[expose] public section
open MeasureTheory
theorem FractionalGap {n : ℕ} (v : Lp ℝ 2 (GaussMeasure n)) :
    ENNReal.ofReal (‖FracPow (0 : ℝ) v‖ ^ 2) ≤ Energy v := by
  have h0 : Memℓp (FracPowCoeff (0 : ℝ) (fun α => (HermiteBasis n).repr v α)) 2 :=
    (FracPowLinear (0 : ℝ)).1 le_rfl v
  set A : lp (fun _ : Fin n → ℕ => ℝ) 2 :=
    ⟨FracPowCoeff (0 : ℝ) (fun α => (HermiteBasis n).repr v α), h0⟩ with hA
  have hAapp : ∀ α : Fin n → ℕ,
      A α = FracPowCoeff (0 : ℝ) (fun β => (HermiteBasis n).repr v β) α := fun _ => rfl
  have hnormA : ‖FracPow (0 : ℝ) v‖ = ‖A‖ := by
    have hvalue : FracPow (0 : ℝ) v = (HermiteBasis n).repr.symm A := by
      simp only [FracPow]
      rw [dif_pos h0]
    rw [hvalue]
    exact LinearIsometryEquiv.norm_map _ _
  -- Parseval for the coefficient family of `Π₀ v`
  have hs := lp.hasSum_norm (p := (2 : ENNReal)) (by norm_num) A
  have hs' : HasSum (fun α : Fin n → ℕ => ‖A α‖ ^ (2 : ℕ)) (‖A‖ ^ (2 : ℕ)) := by
    rw [show ((2 : ENNReal)).toReal = ((2 : ℕ) : ℝ) from by norm_num] at hs
    simpa only [Real.rpow_natCast] using hs
  rw [hnormA, ← hs'.tsum_eq,
    ENNReal.ofReal_tsum_of_nonneg (fun α => by positivity) hs'.summable]
  -- only the nonconstant modes contribute
  have hsupp : Function.support (fun α : Fin n → ℕ => ENNReal.ofReal (‖A α‖ ^ (2 : ℕ)))
      ⊆ {α : Fin n → ℕ | α ≠ 0} := by
    intro α hα
    simp only [Function.mem_support] at hα
    by_contra hcon
    have hzero : α = 0 := not_not.mp hcon
    refine hα ?_
    rw [hAapp α]
    simp [hzero, FracPowCoeff]
  rw [← tsum_subtype_eq_of_support_subset hsupp, Energy]
  -- termwise comparison, using `|α|^{1/2} ≥ 1`
  refine ENNReal.tsum_le_tsum fun x => ?_
  have hx : (x : Fin n → ℕ) ≠ 0 := x.2
  have hAx : A (x : Fin n → ℕ) = (HermiteBasis n).repr v (x : Fin n → ℕ) := by
    rw [hAapp]
    simp only [FracPowCoeff, if_neg hx, Real.rpow_zero, one_mul]
  have hge : (1 : ℝ) ≤ (MultiIndexSum (x : Fin n → ℕ) : ℝ) ^ ((1 : ℝ) / 2) := by
    have h := Real.rpow_le_rpow_of_exponent_le (OneLeMultiIndexSum (x : Fin n → ℕ) hx)
      (by norm_num : (0 : ℝ) ≤ (1 : ℝ) / 2)
    rwa [Real.rpow_zero] at h
  refine ENNReal.ofReal_le_ofReal ?_
  rw [hAx, Real.norm_eq_abs, sq_abs]
  exact le_mul_of_one_le_left (sq_nonneg _) hge
