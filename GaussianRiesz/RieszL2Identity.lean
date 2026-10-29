module

public import GaussianRiesz.RieszTransform
public import GaussianRiesz.SqrtDomainSobolev
public import GaussianRiesz.PseudoInverseSqrt

@[expose] public section
open MeasureTheory
theorem RieszL2Identity {n : ℕ} (f : Lp ℝ 2 (GaussMeasure n)) :
    ‖RieszTransform f‖ = ‖FracPow (0 : ℝ) f‖ ∧ ‖RieszTransform f‖ ≤ ‖f‖ := by
  -- the first identity: `R_γ f = Dv` with `v = L^{-1/2}Π₀ f`, and `L^{1/2}v = Π₀ f`
  have hv := PseudoInverseSqrt f
  have hS := SqrtDomainSobolev (FracPow (-(1 : ℝ) / 2) f) hv.1
  have h1 : ‖RieszTransform f‖ = ‖FracPow (0 : ℝ) f‖ := by
    show ‖GaussD (FracPow (-(1 : ℝ) / 2) f)‖ = ‖FracPow (0 : ℝ) f‖
    rw [← hS.2, hv.2]
  refine ⟨h1, ?_⟩
  rw [h1]
  -- the second: `‖Π₀ f‖ ≤ ‖f‖` by Parseval and termwise domination
  have hbd : ∀ α : Fin n → ℕ,
      ‖FracPowCoeff (0 : ℝ) (fun β => (HermiteBasis n).repr f β) α‖
        ≤ ‖(HermiteBasis n).repr f α‖ := by
    intro α
    simp only [FracPowCoeff]
    by_cases hα : α = 0
    · simp [hα]
    · rw [if_neg hα, Real.rpow_zero, one_mul]
  have h0 : Memℓp (FracPowCoeff (0 : ℝ) (fun α => (HermiteBasis n).repr f α)) 2 := by
    have hvf : Memℓp (fun α => (HermiteBasis n).repr f α) 2 := lp.memℓp _
    have hsum : Summable fun α : Fin n → ℕ =>
        ‖(HermiteBasis n).repr f α‖ ^ ((2 : ENNReal).toReal) :=
      (memℓp_gen_iff (p := (2 : ENNReal)) (by norm_num)).mp hvf
    refine memℓp_gen (Summable.of_nonneg_of_le (fun α => by positivity) (fun α => ?_) hsum)
    exact Real.rpow_le_rpow (norm_nonneg _) (hbd α) ENNReal.toReal_nonneg
  set A : lp (fun _ : Fin n → ℕ => ℝ) 2 :=
    ⟨FracPowCoeff (0 : ℝ) (fun α => (HermiteBasis n).repr f α), h0⟩ with hA
  have hnormA : ‖FracPow (0 : ℝ) f‖ = ‖A‖ := by
    have hvalue : FracPow (0 : ℝ) f = (HermiteBasis n).repr.symm A := by
      simp only [FracPow]
      rw [dif_pos h0]
    rw [hvalue]
    exact LinearIsometryEquiv.norm_map _ _
  have hnormf : ‖f‖ = ‖(HermiteBasis n).repr f‖ :=
    ((HermiteBasis n).repr.norm_map f).symm
  have hs1 := lp.hasSum_norm (p := (2 : ENNReal)) (by norm_num) A
  have hs2 := lp.hasSum_norm (p := (2 : ENNReal)) (by norm_num) ((HermiteBasis n).repr f)
  have hle : ‖A‖ ^ ((2 : ENNReal).toReal)
      ≤ ‖(HermiteBasis n).repr f‖ ^ ((2 : ENNReal).toReal) :=
    hasSum_le (fun α => Real.rpow_le_rpow (norm_nonneg _) (hbd α) ENNReal.toReal_nonneg)
      hs1 hs2
  have c1 : ‖A‖ ^ ((2 : ENNReal).toReal) = ‖A‖ ^ (2 : ℕ) := by
    rw [show ((2 : ENNReal)).toReal = ((2 : ℕ) : ℝ) from by norm_num, Real.rpow_natCast]
  have c2 : ‖(HermiteBasis n).repr f‖ ^ ((2 : ENNReal).toReal)
      = ‖(HermiteBasis n).repr f‖ ^ (2 : ℕ) := by
    rw [show ((2 : ENNReal)).toReal = ((2 : ℕ) : ℝ) from by norm_num, Real.rpow_natCast]
  rw [c1, c2] at hle
  rw [hnormA, hnormf]
  nlinarith [norm_nonneg A, norm_nonneg ((HermiteBasis n).repr f), hle]
