import GaussianRiesz.FracPow
import GaussianRiesz.OneLeMultiIndexSum
open MeasureTheory
theorem FracPowLinear {n : ℕ} (s : ℝ) :
    (s ≤ 0 → ∀ v : Lp ℝ 2 (GaussMeasure n), v ∈ FracPowDomain s)
      ∧ (∀ v w : Lp ℝ 2 (GaussMeasure n), v ∈ FracPowDomain s → w ∈ FracPowDomain s →
          v + w ∈ FracPowDomain s ∧ FracPow s (v + w) = FracPow s v + FracPow s w)
      ∧ (∀ (c : ℝ) (v : Lp ℝ 2 (GaussMeasure n)), v ∈ FracPowDomain s →
          c • v ∈ FracPowDomain s ∧ FracPow s (c • v) = c • FracPow s v) := by
  classical
  -- the value of `L^s` on its domain, read off from the definition
  have hval : ∀ (v : Lp ℝ 2 (GaussMeasure n))
      (h : Memℓp (FracPowCoeff s (fun α => (HermiteBasis n).repr v α)) 2),
      FracPow s v = (HermiteBasis n).repr.symm ⟨_, h⟩ := by
    intro v h
    simp only [FracPow]
    rw [dif_pos h]
  -- `|α| ≥ 1` for every nonzero multi-index
  refine ⟨?_, ?_, ?_⟩
  · -- (1) for `s ≤ 0` the domain is all of `L²(γₙ)`
    intro hs v
    show Memℓp (FracPowCoeff s (fun α => (HermiteBasis n).repr v α)) 2
    have hv : Memℓp (fun α => (HermiteBasis n).repr v α) 2 := lp.memℓp _
    have hsum : Summable fun α : Fin n → ℕ =>
        ‖(HermiteBasis n).repr v α‖ ^ ((2 : ENNReal).toReal) :=
      (memℓp_gen_iff (p := (2 : ENNReal)) (by norm_num)).mp hv
    refine memℓp_gen (Summable.of_nonneg_of_le (fun α => by positivity) (fun α => ?_) hsum)
    have hdom : ‖FracPowCoeff s (fun β => (HermiteBasis n).repr v β) α‖
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
    exact Real.rpow_le_rpow (norm_nonneg _) hdom ENNReal.toReal_nonneg
  · -- (2) additivity
    intro v w hv hw
    have hv' : Memℓp (FracPowCoeff s (fun α => (HermiteBasis n).repr v α)) 2 := hv
    have hw' : Memℓp (FracPowCoeff s (fun α => (HermiteBasis n).repr w α)) 2 := hw
    have hco : FracPowCoeff s (fun β => (HermiteBasis n).repr (v + w) β)
        = FracPowCoeff s (fun β => (HermiteBasis n).repr v β)
          + FracPowCoeff s (fun β => (HermiteBasis n).repr w β) := by
      funext α
      unfold FracPowCoeff
      by_cases hα : α = 0
      · simp [hα]
      · simp only [if_neg hα, Pi.add_apply]
        rw [map_add, lp.coeFn_add, Pi.add_apply]
        ring
    have hmem : Memℓp (FracPowCoeff s (fun β => (HermiteBasis n).repr (v + w) β)) 2 := by
      rw [hco]; exact hv'.add hw'
    refine ⟨hmem, ?_⟩
    rw [hval _ hmem, hval _ hv', hval _ hw', ← map_add]
    exact congrArg _ (lp.ext hco)
  · -- (3) homogeneity
    intro c v hv
    have hv' : Memℓp (FracPowCoeff s (fun α => (HermiteBasis n).repr v α)) 2 := hv
    have hco : FracPowCoeff s (fun β => (HermiteBasis n).repr (c • v) β)
        = c • FracPowCoeff s (fun β => (HermiteBasis n).repr v β) := by
      funext α
      unfold FracPowCoeff
      by_cases hα : α = 0
      · simp [hα]
      · simp only [if_neg hα, Pi.smul_apply, smul_eq_mul]
        rw [map_smul, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul]
        ring
    have hmem : Memℓp (FracPowCoeff s (fun β => (HermiteBasis n).repr (c • v) β)) 2 := by
      rw [hco]; exact hv'.const_smul c
    refine ⟨hmem, ?_⟩
    rw [hval _ hmem, hval _ hv', ← map_smul]
    exact congrArg _ (lp.ext hco)
