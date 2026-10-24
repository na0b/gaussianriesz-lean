import GaussianRiesz.HermiteDerivative
import GaussianRiesz.HermiteGeneratingComplex
theorem HermiteAbsMajorant (w z : ℝ) :
    Summable (fun k : ℕ =>
        |Polynomial.aeval w (Polynomial.hermite k)| * |z| ^ k / (Nat.factorial k : ℝ))
      ∧ ∑' k : ℕ, |Polynomial.aeval w (Polynomial.hermite k)| * |z| ^ k
            / (Nat.factorial k : ℝ)
          ≤ Real.exp (|w| * |z| + z ^ 2 / 2) := by
  -- the three-term recurrence, over `ℂ` and over `ℝ`
  have hrecC : ∀ (ζ : ℂ) (k : ℕ),
      Polynomial.aeval ζ (Polynomial.hermite (k + 2))
        = ζ * Polynomial.aeval ζ (Polynomial.hermite (k + 1))
          - ((k : ℂ) + 1) * Polynomial.aeval ζ (Polynomial.hermite k) := by
    intro ζ k
    rw [Polynomial.hermite_succ (k + 1), HermiteDerivative k, map_sub, map_mul,
      Polynomial.aeval_X, map_nsmul, nsmul_eq_mul]
    push_cast
    ring
  have hrecR : ∀ (x : ℝ) (k : ℕ),
      Polynomial.aeval x (Polynomial.hermite (k + 2))
        = x * Polynomial.aeval x (Polynomial.hermite (k + 1))
          - ((k : ℝ) + 1) * Polynomial.aeval x (Polynomial.hermite k) := by
    intro x k
    rw [Polynomial.hermite_succ (k + 1), HermiteDerivative k, map_sub, map_mul,
      Polynomial.aeval_X, map_nsmul, nsmul_eq_mul]
    push_cast
    ring
  -- the all-plus companion family, realised at the imaginary argument `i|w|`
  obtain ⟨A, hAdef⟩ : ∃ A : ℕ → ℂ, A = fun k =>
      (-Complex.I) ^ k * Polynomial.aeval (Complex.I * ((|w| : ℝ) : ℂ))
        (Polynomial.hermite k) := ⟨_, rfl⟩
  have hI2 : (-Complex.I) ^ 2 = -1 := by
    rw [neg_pow, Complex.I_sq]
    norm_num
  have hA0 : A 0 = 1 := by
    rw [hAdef]
    simp [Polynomial.hermite_zero]
  have hA1 : A 1 = ((|w| : ℝ) : ℂ) := by
    rw [hAdef]
    simp only [pow_one, Polynomial.hermite_one, Polynomial.aeval_X]
    rw [neg_mul, ← mul_assoc, Complex.I_mul_I]
    ring
  have hArec : ∀ k : ℕ, A (k + 2)
      = ((|w| : ℝ) : ℂ) * A (k + 1) + ((k : ℂ) + 1) * A k := by
    intro k
    simp only [hAdef]
    rw [hrecC (Complex.I * ((|w| : ℝ) : ℂ)) k,
      show (-Complex.I) ^ (k + 2) = -((-Complex.I) ^ k) from by rw [pow_add, hI2]; ring,
      show (-Complex.I) ^ (k + 1) = (-Complex.I) ^ k * (-Complex.I) from pow_succ _ _]
    ring
  -- the companion values are real, nonnegative, and dominate `|He_k(w)|`
  have hP : ∀ k : ℕ,
      ((A k).im = 0 ∧ 0 ≤ (A k).re
          ∧ |Polynomial.aeval w (Polynomial.hermite k)| ≤ (A k).re)
        ∧ ((A (k + 1)).im = 0 ∧ 0 ≤ (A (k + 1)).re
          ∧ |Polynomial.aeval w (Polynomial.hermite (k + 1))| ≤ (A (k + 1)).re) := by
    intro k
    induction k with
    | zero =>
      refine ⟨⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩⟩
      · show (A 0).im = 0
        rw [hA0]; simp
      · show 0 ≤ (A 0).re
        rw [hA0]; simp
      · show |Polynomial.aeval w (Polynomial.hermite 0)| ≤ (A 0).re
        rw [hA0]
        simp [Polynomial.hermite_zero]
      · show (A 1).im = 0
        rw [hA1]; simp
      · show 0 ≤ (A 1).re
        rw [hA1]; simp
      · show |Polynomial.aeval w (Polynomial.hermite 1)| ≤ (A 1).re
        rw [hA1]
        simp
    | succ m ih =>
      obtain ⟨⟨him0, hre0, hb0⟩, ⟨him1, hre1, hb1⟩⟩ := ih
      refine ⟨⟨him1, hre1, hb1⟩, ?_⟩
      have him : (A (m + 2)).im = 0 := by
        rw [hArec m]
        simp [him0, him1]
      have hre : (A (m + 2)).re
          = |w| * (A (m + 1)).re + ((m : ℝ) + 1) * (A m).re := by
        rw [hArec m]
        simp [him0, him1]
      refine ⟨him, ?_, ?_⟩
      · rw [hre]
        have : (0:ℝ) ≤ |w| := abs_nonneg w
        positivity
      · rw [hre, hrecR w m]
        have hstep : |w * Polynomial.aeval w (Polynomial.hermite (m + 1))
              - ((m : ℝ) + 1) * Polynomial.aeval w (Polynomial.hermite m)|
            ≤ |w| * |Polynomial.aeval w (Polynomial.hermite (m + 1))|
              + ((m : ℝ) + 1) * |Polynomial.aeval w (Polynomial.hermite m)| := by
          refine le_trans (abs_sub _ _) ?_
          rw [abs_mul, abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ (m : ℝ) + 1)]
        refine le_trans hstep ?_
        exact add_le_add (mul_le_mul_of_nonneg_left hb1 (abs_nonneg w))
          (mul_le_mul_of_nonneg_left hb0 (by positivity))
  -- the generating function of the companion family
  have hsumA : HasSum (fun k : ℕ => (A k).re * |z| ^ k / (Nat.factorial k : ℝ))
      (Real.exp (|w| * |z| + z ^ 2 / 2)) := by
    have hC := HermiteGeneratingComplex (Complex.I * ((|w| : ℝ) : ℂ)) (-Complex.I * ((|z| : ℝ) : ℂ))
    have hterm : ∀ k : ℕ,
        Polynomial.aeval (Complex.I * ((|w| : ℝ) : ℂ)) (Polynomial.hermite k)
            * (-Complex.I * ((|z| : ℝ) : ℂ)) ^ k / (Nat.factorial k : ℂ)
          = (((A k).re * |z| ^ k / (Nat.factorial k : ℝ) : ℝ) : ℂ) := by
      intro k
      have hAk : A k = (((A k).re : ℝ) : ℂ) := by
        refine Complex.ext rfl ?_
        rw [Complex.ofReal_im, (hP k).1.1]
      have hexp : (-Complex.I * ((|z| : ℝ) : ℂ)) ^ k
          = (-Complex.I) ^ k * ((|z| : ℝ) : ℂ) ^ k := mul_pow _ _ _
      rw [hexp]
      have hAval : (-Complex.I) ^ k
          * Polynomial.aeval (Complex.I * ((|w| : ℝ) : ℂ)) (Polynomial.hermite k) = A k := by
        rw [hAdef]
      calc Polynomial.aeval (Complex.I * ((|w| : ℝ) : ℂ)) (Polynomial.hermite k)
              * ((-Complex.I) ^ k * ((|z| : ℝ) : ℂ) ^ k) / (Nat.factorial k : ℂ)
          = ((-Complex.I) ^ k
              * Polynomial.aeval (Complex.I * ((|w| : ℝ) : ℂ)) (Polynomial.hermite k))
                * ((|z| : ℝ) : ℂ) ^ k / (Nat.factorial k : ℂ) := by ring
        _ = A k * ((|z| : ℝ) : ℂ) ^ k / (Nat.factorial k : ℂ) := by rw [hAval]
        _ = (((A k).re * |z| ^ k / (Nat.factorial k : ℝ) : ℝ) : ℂ) := by
            push_cast
            rw [← hAk]
    have hvalue : Complex.exp (Complex.I * ((|w| : ℝ) : ℂ) * (-Complex.I * ((|z| : ℝ) : ℂ))
        - (-Complex.I * ((|z| : ℝ) : ℂ)) ^ 2 / 2)
        = ((Real.exp (|w| * |z| + z ^ 2 / 2) : ℝ) : ℂ) := by
      rw [Complex.ofReal_exp]
      congr 1
      have hII : Complex.I * Complex.I = -1 := Complex.I_mul_I
      have hzz : ((|z| : ℝ) : ℂ) ^ 2 = ((z : ℝ) : ℂ) ^ 2 := by
        rw [← Complex.ofReal_pow, ← Complex.ofReal_pow, sq_abs]
      push_cast
      rw [← hzz]
      linear_combination (-(((|w| : ℝ) : ℂ) * ((|z| : ℝ) : ℂ))
        - ((|z| : ℝ) : ℂ) ^ 2 / 2) * hII
    rw [hvalue] at hC
    have hC' : HasSum (fun k : ℕ => (((A k).re * |z| ^ k
        / (Nat.factorial k : ℝ) : ℝ) : ℂ)) ((Real.exp (|w| * |z| + z ^ 2 / 2) : ℝ) : ℂ) := by
      refine HasSum.congr_fun hC ?_
      intro k
      exact (hterm k).symm
    have hre := ((Complex.hasSum_iff _ _).1 hC').1
    simp only [Complex.ofReal_re] at hre
    exact hre
  -- comparison
  have hdom : ∀ k : ℕ, |Polynomial.aeval w (Polynomial.hermite k)| * |z| ^ k
        / (Nat.factorial k : ℝ)
      ≤ (A k).re * |z| ^ k / (Nat.factorial k : ℝ) := by
    intro k
    have hfac : (0:ℝ) < (Nat.factorial k : ℝ) := by
      exact_mod_cast Nat.factorial_pos k
    rw [div_le_div_iff_of_pos_right hfac]
    exact mul_le_mul_of_nonneg_right (hP k).1.2.2 (by positivity)
  have hnn : ∀ k : ℕ, 0 ≤ |Polynomial.aeval w (Polynomial.hermite k)| * |z| ^ k
      / (Nat.factorial k : ℝ) := by
    intro k
    positivity
  have hsummable : Summable (fun k : ℕ =>
      |Polynomial.aeval w (Polynomial.hermite k)| * |z| ^ k / (Nat.factorial k : ℝ)) :=
    Summable.of_nonneg_of_le hnn hdom hsumA.summable
  refine ⟨hsummable, ?_⟩
  calc ∑' k : ℕ, |Polynomial.aeval w (Polynomial.hermite k)| * |z| ^ k
          / (Nat.factorial k : ℝ)
      ≤ ∑' k : ℕ, (A k).re * |z| ^ k / (Nat.factorial k : ℝ) :=
        Summable.tsum_le_tsum hdom hsummable hsumA.summable
    _ = Real.exp (|w| * |z| + z ^ 2 / 2) := hsumA.tsum_eq
