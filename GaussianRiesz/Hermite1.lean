import GaussianRiesz.Preamble
noncomputable def Hermite1 (k : ℕ) (x : ℝ) : ℝ :=
  Polynomial.aeval (Real.sqrt 2 * x) (Polynomial.hermite k) / Real.sqrt (Nat.factorial k)
