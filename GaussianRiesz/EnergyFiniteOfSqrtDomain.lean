module

public import GaussianRiesz.Energy
public import GaussianRiesz.MultiIndexSum
public import GaussianRiesz.OneLeMultiIndexSum

@[expose] public section
open MeasureTheory
theorem EnergyFiniteOfSqrtDomain {n : ℕ} (v : Lp ℝ 2 (GaussMeasure n))
    (hv : v ∈ FracPowDomain ((1 : ℝ) / 2)) :
    Energy v ≠ ⊤ := by
  classical
  -- Step 1: what the hypothesis says, as summability of a real family
  have hv' : Memℓp (FracPowCoeff ((1 : ℝ) / 2)
      (fun α => (HermiteBasis n).repr v α)) 2 := hv
  have hA : Summable (fun α : Fin n → ℕ =>
      ‖FracPowCoeff ((1 : ℝ) / 2) (fun β => (HermiteBasis n).repr v β) α‖ ^ (2 : ℝ)) := by
    have h := (memℓp_gen_iff (p := 2) (f := FracPowCoeff ((1 : ℝ) / 2)
      (fun α => (HermiteBasis n).repr v α)) (by norm_num)).1 hv'
    simpa using h
  have hB : Summable (fun α : {α : Fin n → ℕ // α ≠ 0} =>
      ‖FracPowCoeff ((1 : ℝ) / 2) (fun β => (HermiteBasis n).repr v β)
        (α : Fin n → ℕ)‖ ^ (2 : ℝ)) := hA.subtype _
  -- the rpow/npow bridges: `x ^ (2 : ℝ) = x ^ 2`, and `(t ^ (1/2)) ^ 2 = t` for `t ≥ 0`
  have h2 : ∀ x : ℝ, x ^ (2 : ℝ) = x ^ 2 := by
    intro x
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) from by norm_num, Real.rpow_natCast]
  have hhalf : ∀ t : ℝ, 0 ≤ t → (t ^ ((1 : ℝ) / 2)) ^ 2 = t := by
    intro t ht
    rw [← Real.rpow_natCast (t ^ ((1 : ℝ) / 2)) 2, ← Real.rpow_mul ht]
    norm_num
  have hC : ∀ α : {α : Fin n → ℕ // α ≠ 0},
      ‖FracPowCoeff ((1 : ℝ) / 2) (fun β => (HermiteBasis n).repr v β)
          (α : Fin n → ℕ)‖ ^ (2 : ℝ)
        = (MultiIndexSum (α : Fin n → ℕ) : ℝ)
            * ((HermiteBasis n).repr v (α : Fin n → ℕ)) ^ 2 := by
    intro α
    have h1 : FracPowCoeff ((1 : ℝ) / 2) (fun β => (HermiteBasis n).repr v β)
        (α : Fin n → ℕ)
        = (MultiIndexSum (α : Fin n → ℕ) : ℝ) ^ ((1 : ℝ) / 2)
            * (HermiteBasis n).repr v (α : Fin n → ℕ) := by
      rw [FracPowCoeff]
      exact if_neg α.2
    rw [h1, h2, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _), mul_pow,
      hhalf _ (Nat.cast_nonneg _), sq_abs]
  -- Steps 2 and 3: `1 ≤ |α|` gives `|α| ^ (1/2) ≤ |α|`, so the energy summands are dominated
  have hmaj : Summable (fun α : {α : Fin n → ℕ // α ≠ 0} =>
      (MultiIndexSum (α : Fin n → ℕ) : ℝ) ^ ((1 : ℝ) / 2)
        * ((HermiteBasis n).repr v (α : Fin n → ℕ)) ^ 2) := by
    refine Summable.of_nonneg_of_le (fun α => ?_) (fun α => ?_) (hB.congr hC)
    · have : (0:ℝ) ≤ (MultiIndexSum (α : Fin n → ℕ) : ℝ) ^ ((1 : ℝ) / 2) :=
        Real.rpow_nonneg (Nat.cast_nonneg _) _
      exact mul_nonneg this (sq_nonneg _)
    · refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
      calc (MultiIndexSum (α : Fin n → ℕ) : ℝ) ^ ((1 : ℝ) / 2)
          ≤ (MultiIndexSum (α : Fin n → ℕ) : ℝ) ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (OneLeMultiIndexSum _ α.2) (by norm_num)
        _ = (MultiIndexSum (α : Fin n → ℕ) : ℝ) := Real.rpow_one _
  -- Step 4: a convergent sum of nonnegative reals has finite `ENNReal.ofReal` tsum
  have hE : Energy v = ∑' α : {α : Fin n → ℕ // α ≠ 0},
      ENNReal.ofReal ((MultiIndexSum (α : Fin n → ℕ) : ℝ) ^ ((1 : ℝ) / 2)
        * ((HermiteBasis n).repr v (α : Fin n → ℕ)) ^ 2) := rfl
  rw [hE, ← ENNReal.ofReal_tsum_of_nonneg (fun α => ?_) hmaj]
  · exact ENNReal.ofReal_ne_top
  · have : (0:ℝ) ≤ (MultiIndexSum (α : Fin n → ℕ) : ℝ) ^ ((1 : ℝ) / 2) :=
      Real.rpow_nonneg (Nat.cast_nonneg _) _
    exact mul_nonneg this (sq_nonneg _)
