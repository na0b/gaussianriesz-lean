import GaussianRiesz.HermiteDerivative
import GaussianRiesz.HermiteGeneratingComplex
theorem HermiteGenerating (y z : ℝ) :
    HasSum (fun k : ℕ =>
        Polynomial.aeval y (Polynomial.hermite k) * z ^ k / (Nat.factorial k : ℝ))
      (Real.exp (y * z - z ^ 2 / 2)) := by
  -- the real and complex evaluations agree
  have haeval : ∀ (x : ℝ) (k : ℕ),
      Polynomial.aeval ((x : ℂ)) (Polynomial.hermite k)
        = ((Polynomial.aeval x (Polynomial.hermite k) : ℝ) : ℂ) := by
    intro x k
    simp [Polynomial.aeval_def, Polynomial.eval₂_eq_sum_range]
  -- specialise to real arguments and descend from `ℂ` to `ℝ`
  have hC := HermiteGeneratingComplex (y : ℂ) (z : ℂ)
  have hterm : ∀ k : ℕ,
      Polynomial.aeval ((y : ℂ)) (Polynomial.hermite k) * (z : ℂ) ^ k / (Nat.factorial k : ℂ)
        = ((Polynomial.aeval y (Polynomial.hermite k) * z ^ k
            / (Nat.factorial k : ℝ) : ℝ) : ℂ) := by
    intro k
    rw [haeval y k]
    push_cast
    ring
  have hvalue : Complex.exp ((y : ℂ) * (z : ℂ) - (z : ℂ) ^ 2 / 2)
      = ((Real.exp (y * z - z ^ 2 / 2) : ℝ) : ℂ) := by
    rw [Complex.ofReal_exp]
    congr 1
    push_cast
    ring
  rw [hvalue] at hC
  have hC' : HasSum (fun k : ℕ => ((Polynomial.aeval y (Polynomial.hermite k) * z ^ k
      / (Nat.factorial k : ℝ) : ℝ) : ℂ)) ((Real.exp (y * z - z ^ 2 / 2) : ℝ) : ℂ) := by
    refine HasSum.congr_fun hC ?_
    intro k
    exact (hterm k).symm
  have hre := ((Complex.hasSum_iff _ _).1 hC').1
  simp only [Complex.ofReal_re] at hre
  exact hre
