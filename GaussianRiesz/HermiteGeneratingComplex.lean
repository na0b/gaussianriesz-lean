import GaussianRiesz.Preamble
theorem HermiteGeneratingComplex (ζ ξ : ℂ) :
    HasSum (fun k : ℕ =>
        Polynomial.aeval ζ (Polynomial.hermite k) * ξ ^ k / (Nat.factorial k : ℂ))
      (Complex.exp (ζ * ξ - ξ ^ 2 / 2)) := by
  -- the Gaussian and its derivative
  have hGd : ∀ w : ℂ, HasDerivAt (fun v : ℂ => Complex.exp (-(v ^ 2 / 2)))
      (-w * Complex.exp (-(w ^ 2 / 2))) w := by
    intro w
    have hfe : (fun v : ℂ => -(v ^ 2 / 2)) = fun v : ℂ => (-(1 : ℂ) / 2) * v ^ 2 := by
      funext v
      ring
    have h : HasDerivAt (fun v : ℂ => -(v ^ 2 / 2)) (-w) w := by
      rw [hfe]
      exact ((hasDerivAt_pow 2 w).const_mul (-(1 : ℂ) / 2)).congr_deriv (by push_cast; ring)
    exact h.cexp.congr_deriv (by ring)
  have hGdiff : Differentiable ℂ (fun v : ℂ => Complex.exp (-(v ^ 2 / 2))) :=
    fun w => (hGd w).differentiableAt
  -- Rodrigues' identity over `ℂ`, by induction on the order
  have hiter : ∀ (k : ℕ) (w : ℂ),
      iteratedDeriv k (fun v : ℂ => Complex.exp (-(v ^ 2 / 2))) w
        = (-1) ^ k * Polynomial.aeval w (Polynomial.hermite k)
            * Complex.exp (-(w ^ 2 / 2)) := by
    intro k
    induction k with
    | zero =>
      intro w
      simp [Polynomial.hermite_zero]
    | succ m ih =>
      intro w
      have hfun : iteratedDeriv m (fun v : ℂ => Complex.exp (-(v ^ 2 / 2)))
          = fun v => (-1) ^ m * Polynomial.aeval v (Polynomial.hermite m)
              * Complex.exp (-(v ^ 2 / 2)) := funext ih
      rw [iteratedDeriv_succ, hfun]
      have hp : HasDerivAt (fun v : ℂ => Polynomial.aeval v (Polynomial.hermite m))
          (Polynomial.aeval w (Polynomial.derivative (Polynomial.hermite m))) w := by
        have h : DifferentiableAt ℂ (fun v : ℂ => Polynomial.aeval v (Polynomial.hermite m)) w :=
          (Polynomial.differentiable_aeval (Polynomial.hermite m)).differentiableAt
        simpa [Polynomial.deriv_aeval] using h.hasDerivAt
      have h1 : HasDerivAt (fun v : ℂ => (-1 : ℂ) ^ m * Polynomial.aeval v (Polynomial.hermite m))
          ((-1 : ℂ) ^ m * Polynomial.aeval w (Polynomial.derivative (Polynomial.hermite m))) w :=
        hp.const_mul _
      have hprod : HasDerivAt (fun v : ℂ => (-1 : ℂ) ^ m
            * Polynomial.aeval v (Polynomial.hermite m) * Complex.exp (-(v ^ 2 / 2)))
          ((-1 : ℂ) ^ (m + 1) * Polynomial.aeval w (Polynomial.hermite (m + 1))
            * Complex.exp (-(w ^ 2 / 2))) w := by
        refine (h1.mul (hGd w)).congr_deriv ?_
        rw [Polynomial.hermite_succ]
        simp only [map_sub, map_mul, Polynomial.aeval_X]
        ring
      exact hprod.deriv
  -- Taylor's theorem for the entire Gaussian, centred at `ζ` and evaluated at `ζ - ξ`
  have hT := Complex.hasSum_taylorSeries_of_entire hGdiff ζ (ζ - ξ)
  have hterm : ∀ k : ℕ,
      ((Nat.factorial k : ℂ))⁻¹ • ((ζ - ξ) - ζ) ^ k
          • iteratedDeriv k (fun v : ℂ => Complex.exp (-(v ^ 2 / 2))) ζ
        = (Polynomial.aeval ζ (Polynomial.hermite k) * ξ ^ k / (Nat.factorial k : ℂ))
            * Complex.exp (-(ζ ^ 2 / 2)) := by
    intro k
    rw [hiter k ζ, show (ζ - ξ) - ζ = -ξ from by ring, smul_eq_mul, smul_eq_mul, neg_pow]
    have hone : ((-1 : ℂ)) ^ k * ((-1 : ℂ)) ^ k = 1 := by
      rw [← mul_pow]
      norm_num
    rw [div_eq_mul_inv]
    calc (↑(Nat.factorial k) : ℂ)⁻¹ * ((-1) ^ k * ξ ^ k
          * ((-1) ^ k * Polynomial.aeval ζ (Polynomial.hermite k)
            * Complex.exp (-(ζ ^ 2 / 2))))
        = ((-1 : ℂ) ^ k * (-1 : ℂ) ^ k) * (Polynomial.aeval ζ (Polynomial.hermite k)
            * ξ ^ k * (↑(Nat.factorial k) : ℂ)⁻¹ * Complex.exp (-(ζ ^ 2 / 2))) := by ring
      _ = Polynomial.aeval ζ (Polynomial.hermite k) * ξ ^ k
            * (↑(Nat.factorial k) : ℂ)⁻¹ * Complex.exp (-(ζ ^ 2 / 2)) := by
          rw [hone, one_mul]
  have hval : Complex.exp (-((ζ - ξ) ^ 2 / 2))
      = Complex.exp (ζ * ξ - ξ ^ 2 / 2) * Complex.exp (-(ζ ^ 2 / 2)) := by
    rw [← Complex.exp_add]
    congr 1
    ring
  rw [hval] at hT
  have hTr : HasSum (fun k : ℕ =>
      (Polynomial.aeval ζ (Polynomial.hermite k) * ξ ^ k / (Nat.factorial k : ℂ))
        * Complex.exp (-(ζ ^ 2 / 2)))
      (Complex.exp (ζ * ξ - ξ ^ 2 / 2) * Complex.exp (-(ζ ^ 2 / 2))) := by
    refine HasSum.congr_fun hT ?_
    intro k
    exact (hterm k).symm
  have hdiv := hTr.div_const (Complex.exp (-(ζ ^ 2 / 2)))
  simpa [mul_div_cancel_right₀, Complex.exp_ne_zero] using hdiv
