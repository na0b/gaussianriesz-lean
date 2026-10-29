module

public import GaussianRiesz.RieszTransform
public import GaussianRiesz.SqrtDomainSobolev
public import GaussianRiesz.ProjZeroCentering
public import GaussianRiesz.GaussDLinear
public import GaussianRiesz.OneLeMultiIndexSum

@[expose] public section
open MeasureTheory
theorem RieszSqrtIdentity {n : ℕ} (u : Lp ℝ 2 (GaussMeasure n))
    (hu : u ∈ FracPowDomain ((1 : ℝ) / 2)) :
    RieszTransform (FracPow ((1 : ℝ) / 2) u) = GaussD u := by
  have hval : ∀ (s : ℝ) (z : Lp ℝ 2 (GaussMeasure n))
      (h : Memℓp (FracPowCoeff s (fun α => (HermiteBasis n).repr z α)) 2),
      FracPow s z = (HermiteBasis n).repr.symm ⟨_, h⟩ := by
    intro s z h
    simp only [FracPow]
    rw [dif_pos h]
  have hcoef : ∀ (s : ℝ) (z : Lp ℝ 2 (GaussMeasure n))
      (h : Memℓp (FracPowCoeff s (fun α => (HermiteBasis n).repr z α)) 2)
      (α : Fin n → ℕ),
      (HermiteBasis n).repr (FracPow s z) α
        = FracPowCoeff s (fun β => (HermiteBasis n).repr z β) α := by
    intro s z h α
    rw [hval s z h, LinearIsometryEquiv.apply_symm_apply]
  have hu' : Memℓp (FracPowCoeff ((1 : ℝ) / 2)
      (fun α => (HermiteBasis n).repr u α)) 2 := hu
  have hbd0 : ∀ α : Fin n → ℕ,
      ‖FracPowCoeff (0 : ℝ) (fun β => (HermiteBasis n).repr u β) α‖
        ≤ ‖(HermiteBasis n).repr u α‖ := by
    intro α
    simp only [FracPowCoeff]
    by_cases hα : α = 0
    · simp [hα]
    · rw [if_neg hα, Real.rpow_zero, one_mul]
  have h0 : Memℓp (FracPowCoeff (0 : ℝ) (fun α => (HermiteBasis n).repr u α)) 2 := by
    have hvf : Memℓp (fun α => (HermiteBasis n).repr u α) 2 := lp.memℓp _
    have hsum : Summable fun α : Fin n → ℕ =>
        ‖(HermiteBasis n).repr u α‖ ^ ((2 : ENNReal).toReal) :=
      (memℓp_gen_iff (p := (2 : ENNReal)) (by norm_num)).mp hvf
    refine memℓp_gen (Summable.of_nonneg_of_le (fun α => by positivity) (fun α => ?_) hsum)
    exact Real.rpow_le_rpow (norm_nonneg _) (hbd0 α) ENNReal.toReal_nonneg
  -- Step 2: `|α|^{-1/2}` cancels `|α|^{1/2}`
  have hcancel : FracPowCoeff (-(1 : ℝ) / 2)
        (fun α => (HermiteBasis n).repr (FracPow ((1 : ℝ) / 2) u) α)
      = FracPowCoeff (0 : ℝ) (fun α => (HermiteBasis n).repr u α) := by
    funext α
    simp only [FracPowCoeff]
    by_cases hα : α = 0
    · simp [hα]
    · rw [if_neg hα, if_neg hα, hcoef _ _ hu' α]
      simp only [FracPowCoeff, if_neg hα]
      have hpos : (0 : ℝ) < (MultiIndexSum α : ℝ) := lt_of_lt_of_le zero_lt_one (OneLeMultiIndexSum α hα)
      rw [← mul_assoc, ← Real.rpow_add hpos]
      norm_num
  have hmem : Memℓp (FracPowCoeff (-(1 : ℝ) / 2)
      (fun α => (HermiteBasis n).repr (FracPow ((1 : ℝ) / 2) u) α)) 2 := by
    rw [hcancel]; exact h0
  have hstep2 : FracPow (-(1 : ℝ) / 2) (FracPow ((1 : ℝ) / 2) u) = FracPow (0 : ℝ) u := by
    rw [hval _ _ hmem, hval _ _ h0]
    exact congrArg _ (lp.ext hcancel)
  -- Step 3: apply `D`, using that constants are null directions
  show GaussD (FracPow (-(1 : ℝ) / 2) (FracPow ((1 : ℝ) / 2) u)) = GaussD u
  rw [hstep2, ProjZeroCentering u]
  have hu0 : u ∈ SobolevW12 n := (SqrtDomainSobolev u hu).1
  have h3 := (GaussDLinear (n := n)).2.2
    (-(∫ x, (u : EuclideanSpace ℝ (Fin n) → ℝ) x ∂(GaussMeasure n)))
  have hsub : u - (∫ x, (u : EuclideanSpace ℝ (Fin n) → ℝ) x ∂(GaussMeasure n))
        • HermiteL2 (0 : Fin n → ℕ)
      = u + (-(∫ x, (u : EuclideanSpace ℝ (Fin n) → ℝ) x ∂(GaussMeasure n)))
        • HermiteL2 (0 : Fin n → ℕ) := by
    rw [neg_smul, ← sub_eq_add_neg]
  rw [hsub, ((GaussDLinear (n := n)).1 u _ hu0 h3.1).2, h3.2, add_zero]
