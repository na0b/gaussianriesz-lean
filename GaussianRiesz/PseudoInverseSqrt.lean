module

public import GaussianRiesz.FracPow
public import GaussianRiesz.OneLeMultiIndexSum

@[expose] public section
open MeasureTheory
theorem PseudoInverseSqrt {n : ℕ} (f : Lp ℝ 2 (GaussMeasure n)) :
    FracPow (-(1 : ℝ) / 2) f ∈ FracPowDomain ((1 : ℝ) / 2)
      ∧ FracPow ((1 : ℝ) / 2) (FracPow (-(1 : ℝ) / 2) f) = FracPow (0 : ℝ) f := by
  -- for `s ≤ 0` the multiplied family is dominated by the coefficient family
  have hdom : ∀ s : ℝ, s ≤ 0 → ∀ v : Lp ℝ 2 (GaussMeasure n),
      Memℓp (FracPowCoeff s (fun α => (HermiteBasis n).repr v α)) 2 := by
    intro s hs v
    have hv : Memℓp (fun α => (HermiteBasis n).repr v α) 2 := lp.memℓp _
    have hsum : Summable fun α : Fin n → ℕ =>
        ‖(HermiteBasis n).repr v α‖ ^ ((2 : ENNReal).toReal) :=
      (memℓp_gen_iff (p := (2 : ENNReal)) (by norm_num)).mp hv
    refine memℓp_gen (Summable.of_nonneg_of_le (fun α => by positivity) (fun α => ?_) hsum)
    have hbd : ‖FracPowCoeff s (fun β => (HermiteBasis n).repr v β) α‖
        ≤ ‖(HermiteBasis n).repr v α‖ := by
      unfold FracPowCoeff
      by_cases hα : α = 0
      · simp [hα]
      · rw [if_neg hα, norm_mul, Real.norm_eq_abs]
        have h1 : (1 : ℝ) ≤ (MultiIndexSum α : ℝ) := OneLeMultiIndexSum α hα
        have h3 : (0 : ℝ) ≤ (MultiIndexSum α : ℝ) ^ s := Real.rpow_nonneg (by linarith) s
        rw [abs_of_nonneg h3]
        exact mul_le_of_le_one_left (norm_nonneg _)
          (Real.rpow_le_one_of_one_le_of_nonpos h1 hs)
    exact Real.rpow_le_rpow (norm_nonneg _) hbd ENNReal.toReal_nonneg
  -- the value and the coefficients of `L^s v` on the domain
  have hval : ∀ (s : ℝ) (v : Lp ℝ 2 (GaussMeasure n))
      (h : Memℓp (FracPowCoeff s (fun α => (HermiteBasis n).repr v α)) 2),
      FracPow s v = (HermiteBasis n).repr.symm ⟨_, h⟩ := by
    intro s v h
    simp only [FracPow]
    rw [dif_pos h]
  have hcoef : ∀ (s : ℝ) (v : Lp ℝ 2 (GaussMeasure n))
      (h : Memℓp (FracPowCoeff s (fun α => (HermiteBasis n).repr v α)) 2)
      (α : Fin n → ℕ),
      (HermiteBasis n).repr (FracPow s v) α
        = FracPowCoeff s (fun β => (HermiteBasis n).repr v β) α := by
    intro s v h α
    rw [hval s v h, LinearIsometryEquiv.apply_symm_apply]
  -- Step 1: `f ∈ Dom(L^{-1/2})`, so the pseudoinverse is given by its series
  have hf : Memℓp (FracPowCoeff (-(1 : ℝ) / 2)
      (fun α => (HermiteBasis n).repr f α)) 2 := hdom _ (by norm_num) f
  have hf0 : Memℓp (FracPowCoeff (0 : ℝ) (fun α => (HermiteBasis n).repr f α)) 2 :=
    hdom _ le_rfl f
  -- Step 2: the multiplier `|α|^{1/2}` cancels the multiplier `|α|^{-1/2}`
  have hcancel : FracPowCoeff ((1 : ℝ) / 2)
        (fun α => (HermiteBasis n).repr (FracPow (-(1 : ℝ) / 2) f) α)
      = FracPowCoeff (0 : ℝ) (fun α => (HermiteBasis n).repr f α) := by
    funext α
    simp only [FracPowCoeff]
    by_cases hα : α = 0
    · simp [hα]
    · rw [if_neg hα, if_neg hα, hcoef _ _ hf α]
      simp only [FracPowCoeff, if_neg hα]
      have hpos : (0 : ℝ) < (MultiIndexSum α : ℝ) := lt_of_lt_of_le zero_lt_one (OneLeMultiIndexSum α hα)
      rw [← mul_assoc, ← Real.rpow_add hpos]
      norm_num
  refine ⟨?_, ?_⟩
  · show Memℓp (FracPowCoeff ((1 : ℝ) / 2)
      (fun α => (HermiteBasis n).repr (FracPow (-(1 : ℝ) / 2) f) α)) 2
    rw [hcancel]
    exact hf0
  · have h1 : Memℓp (FracPowCoeff ((1 : ℝ) / 2)
        (fun α => (HermiteBasis n).repr (FracPow (-(1 : ℝ) / 2) f) α)) 2 := by
      rw [hcancel]; exact hf0
    rw [hval _ _ h1, hval _ _ hf0]
    exact congrArg _ (lp.ext hcancel)
