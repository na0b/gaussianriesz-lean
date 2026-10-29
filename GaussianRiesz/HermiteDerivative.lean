module

public import GaussianRiesz.Preamble

@[expose] public section
theorem HermiteDerivative (k : ℕ) :
    Polynomial.derivative (Polynomial.hermite (k + 1)) = (k + 1 : ℕ) • Polynomial.hermite k := by
  induction k with
  | zero =>
    rw [Polynomial.hermite_succ, Polynomial.hermite_zero]
    simp
  | succ m ih =>
    rw [Polynomial.hermite_succ (m + 1), map_sub, Polynomial.derivative_mul,
      Polynomial.derivative_X, one_mul, ih, map_nsmul, Polynomial.hermite_succ m]
    simp only [nsmul_eq_mul, Nat.cast_add, Nat.cast_one]
    ring
