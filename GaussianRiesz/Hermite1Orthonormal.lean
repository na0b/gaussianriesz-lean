module

public import GaussianRiesz.Hermite1
public import GaussianRiesz.HermiteGenerating
public import GaussianRiesz.HermiteAbsMajorant
public import GaussianRiesz.HermiteDerivative

@[expose] public section
open MeasureTheory
theorem Hermite1Orthonormal (k l : ℕ) :
    ∫ x : ℝ, Real.pi ^ (-(1 : ℝ) / 2) * Real.exp (-x ^ 2) * (Hermite1 k x * Hermite1 l x)
      = if k = l then 1 else 0 := by
  classical
  have hs2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hs2pos : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  -- (0) a polynomial in `√2 x` against the Gaussian weight is integrable
  have hint0 : ∀ m : ℕ, Integrable (fun s : ℝ => s ^ m * Real.exp (-s ^ 2)) := by
    intro m
    have h := integrable_rpow_mul_exp_neg_mul_sq (b := (1 : ℝ)) one_pos (s := (m : ℝ))
      (lt_of_lt_of_le (by norm_num) (Nat.cast_nonneg m))
    simpa [Real.rpow_natCast] using h
  have hintP : ∀ q : Polynomial ℤ,
      Integrable (fun x : ℝ => Polynomial.aeval (Real.sqrt 2 * x) q * Real.exp (-x ^ 2)) := by
    intro q
    refine Polynomial.induction_on' q (fun p r hp hr => ?_) (fun m a => ?_)
    · refine (hp.add hr).congr (Filter.Eventually.of_forall fun s => ?_)
      simp only [Pi.add_apply, map_add]
      ring
    · have hre : (fun x : ℝ => Polynomial.aeval (Real.sqrt 2 * x)
            (Polynomial.monomial m a) * Real.exp (-x ^ 2))
          = fun x : ℝ => ((a : ℝ) * Real.sqrt 2 ^ m) * (x ^ m * Real.exp (-x ^ 2)) := by
        funext x
        simp [Polynomial.aeval_monomial, mul_pow]
        ring
      rw [hre]
      exact (hint0 m).const_mul _
  -- (1) the derivative bridge: `aeval` of an INTEGER polynomial at a real point
  have hd : ∀ (p : Polynomial ℤ) (y : ℝ),
      HasDerivAt (fun z : ℝ => Polynomial.aeval z p)
        (Polynomial.aeval y (Polynomial.derivative p)) y := by
    intro p y
    have h1 : ∀ (r : Polynomial ℤ) (z : ℝ), Polynomial.aeval z r
        = Polynomial.eval z (r.map (algebraMap ℤ ℝ)) := by
      intro r z; rw [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map]
    simp only [h1]
    rw [← Polynomial.derivative_map]
    exact Polynomial.hasDerivAt _ y
  have hsucc : ∀ (b : ℕ) (y : ℝ), Polynomial.aeval y (Polynomial.hermite (b + 1))
      = y * Polynomial.aeval y (Polynomial.hermite b)
        - Polynomial.aeval y (Polynomial.derivative (Polynomial.hermite b)) := by
    intro b y; simp [Polynomial.hermite_succ]
  -- (2) the single integration by parts, with the √2 factors cancelling exactly
  have hfe : ∀ (r : Polynomial ℤ) (c : ℕ),
      Integrable (fun x : ℝ => Polynomial.aeval (Real.sqrt 2 * x) r
        * Polynomial.aeval (Real.sqrt 2 * x) (Polynomial.hermite c) * Real.exp (-x ^ 2)) := by
    intro r c
    refine (hintP (r * Polynomial.hermite c)).congr (Filter.Eventually.of_forall fun x => ?_)
    simp only [map_mul]
  have hIBP : ∀ (q : Polynomial ℤ) (b : ℕ),
      (∫ x : ℝ, Polynomial.aeval (Real.sqrt 2 * x) q
          * Polynomial.aeval (Real.sqrt 2 * x) (Polynomial.hermite (b + 1))
          * Real.exp (-x ^ 2))
        = ∫ x : ℝ, Polynomial.aeval (Real.sqrt 2 * x) (Polynomial.derivative q)
          * Polynomial.aeval (Real.sqrt 2 * x) (Polynomial.hermite b) * Real.exp (-x ^ 2) := by
    intro q b
    have hderiv : ∀ x : ℝ, HasDerivAt
        (fun y : ℝ => Polynomial.aeval (Real.sqrt 2 * y) q
            * Polynomial.aeval (Real.sqrt 2 * y) (Polynomial.hermite b) * Real.exp (-y ^ 2))
        (Real.sqrt 2 * (Polynomial.aeval (Real.sqrt 2 * x) (Polynomial.derivative q)
            * Polynomial.aeval (Real.sqrt 2 * x) (Polynomial.hermite b) * Real.exp (-x ^ 2))
          - Real.sqrt 2 * (Polynomial.aeval (Real.sqrt 2 * x) q
            * Polynomial.aeval (Real.sqrt 2 * x) (Polynomial.hermite (b + 1))
            * Real.exp (-x ^ 2))) x := by
      intro x
      have hlin : HasDerivAt (fun y : ℝ => Real.sqrt 2 * y) (Real.sqrt 2) x := by
        simpa using (hasDerivAt_id x).const_mul (Real.sqrt 2)
      have hq : HasDerivAt (fun y : ℝ => Polynomial.aeval (Real.sqrt 2 * y) q)
          (Polynomial.aeval (Real.sqrt 2 * x) (Polynomial.derivative q) * Real.sqrt 2) x :=
        (hd q (Real.sqrt 2 * x)).comp x hlin
      have hb : HasDerivAt
          (fun y : ℝ => Polynomial.aeval (Real.sqrt 2 * y) (Polynomial.hermite b))
          (Polynomial.aeval (Real.sqrt 2 * x)
            (Polynomial.derivative (Polynomial.hermite b)) * Real.sqrt 2) x :=
        (hd (Polynomial.hermite b) (Real.sqrt 2 * x)).comp x hlin
      have hsq : HasDerivAt (fun y : ℝ => -y ^ 2) (-(2 * x)) x := by
        have h := (hasDerivAt_pow 2 x).neg
        norm_num at h
        exact h
      have he : HasDerivAt (fun y : ℝ => Real.exp (-y ^ 2))
          (Real.exp (-x ^ 2) * -(2 * x)) x := hsq.exp
      refine ((hq.mul hb).mul he).congr_deriv ?_
      simp only [Pi.mul_apply]
      have h2x : (2 : ℝ) * x = Real.sqrt 2 * (Real.sqrt 2 * x) := by
        rw [← mul_assoc, hs2]
      rw [hsucc b (Real.sqrt 2 * x), h2x]
      ring
    have hf' : Integrable (fun x : ℝ =>
        Real.sqrt 2 * (Polynomial.aeval (Real.sqrt 2 * x) (Polynomial.derivative q)
            * Polynomial.aeval (Real.sqrt 2 * x) (Polynomial.hermite b) * Real.exp (-x ^ 2))
          - Real.sqrt 2 * (Polynomial.aeval (Real.sqrt 2 * x) q
            * Polynomial.aeval (Real.sqrt 2 * x) (Polynomial.hermite (b + 1))
            * Real.exp (-x ^ 2))) :=
      ((hfe (Polynomial.derivative q) b).const_mul _).sub ((hfe q (b + 1)).const_mul _)
    have hzero := integral_eq_zero_of_hasDerivAt_of_integrable hderiv hf' (hfe q b)
    rw [integral_sub ((hfe (Polynomial.derivative q) b).const_mul _)
        ((hfe q (b + 1)).const_mul _), integral_const_mul, integral_const_mul,
      sub_eq_zero] at hzero
    exact (mul_left_cancel₀ (ne_of_gt hs2pos) hzero).symm
  -- (3) the two recurrences and the symmetry
  have hz : ∀ b : ℕ, (∫ x : ℝ, Polynomial.aeval (Real.sqrt 2 * x) (Polynomial.hermite 0)
      * Polynomial.aeval (Real.sqrt 2 * x) (Polynomial.hermite (b + 1))
      * Real.exp (-x ^ 2)) = 0 := by
    intro b
    rw [hIBP (Polynomial.hermite 0) b]
    have hzz : ∀ x : ℝ, Polynomial.aeval (Real.sqrt 2 * x)
          (Polynomial.derivative (Polynomial.hermite 0))
        * Polynomial.aeval (Real.sqrt 2 * x) (Polynomial.hermite b) * Real.exp (-x ^ 2)
        = 0 := by
      intro x
      rw [Polynomial.hermite_zero]
      simp
    rw [integral_congr_ae (Filter.Eventually.of_forall hzz), integral_zero]
  have hstep : ∀ m b : ℕ, (∫ x : ℝ,
        Polynomial.aeval (Real.sqrt 2 * x) (Polynomial.hermite (m + 1))
        * Polynomial.aeval (Real.sqrt 2 * x) (Polynomial.hermite (b + 1))
        * Real.exp (-x ^ 2))
      = (m + 1 : ℝ) * ∫ x : ℝ, Polynomial.aeval (Real.sqrt 2 * x) (Polynomial.hermite m)
        * Polynomial.aeval (Real.sqrt 2 * x) (Polynomial.hermite b) * Real.exp (-x ^ 2) := by
    intro m b
    rw [hIBP (Polynomial.hermite (m + 1)) b, HermiteDerivative m, ← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [nsmul_eq_mul, map_mul, map_natCast]
    push_cast
    ring
  have hsymm : ∀ a b : ℕ, (∫ x : ℝ, Polynomial.aeval (Real.sqrt 2 * x) (Polynomial.hermite a)
        * Polynomial.aeval (Real.sqrt 2 * x) (Polynomial.hermite b) * Real.exp (-x ^ 2))
      = ∫ x : ℝ, Polynomial.aeval (Real.sqrt 2 * x) (Polynomial.hermite b)
        * Polynomial.aeval (Real.sqrt 2 * x) (Polynomial.hermite a) * Real.exp (-x ^ 2) :=
    fun a b => integral_congr_ae (Filter.Eventually.of_forall fun x => by ring)
  -- (4) the closed form of the unnormalized integral
  have key : ∀ a b : ℕ, (∫ x : ℝ, Polynomial.aeval (Real.sqrt 2 * x) (Polynomial.hermite a)
        * Polynomial.aeval (Real.sqrt 2 * x) (Polynomial.hermite b) * Real.exp (-x ^ 2))
      = if a = b then Real.sqrt Real.pi * (Nat.factorial a : ℝ) else 0 := by
    intro a
    induction a with
    | zero =>
        intro b
        cases b with
        | zero =>
            have hg : (∫ x : ℝ, Polynomial.aeval (Real.sqrt 2 * x) (Polynomial.hermite 0)
                * Polynomial.aeval (Real.sqrt 2 * x) (Polynomial.hermite 0)
                * Real.exp (-x ^ 2)) = ∫ x : ℝ, Real.exp (-1 * x ^ 2) := by
              refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
              simp [Polynomial.hermite_zero]
            rw [hg, integral_gaussian]
            simp
        | succ c => rw [hz c]; simp
    | succ m ih =>
        intro b
        cases b with
        | zero =>
            rw [hsymm (m + 1) 0, hz m]
            simp
        | succ c =>
            rw [hstep m c, ih c]
            by_cases h : m = c
            · subst h
              simp only [Nat.factorial_succ]
              push_cast
              ring
            · rw [if_neg h, if_neg (by simpa using h)]
              ring
  -- (5) normalize
  have hre : ∀ x : ℝ, Real.pi ^ (-(1 : ℝ) / 2) * Real.exp (-x ^ 2)
        * (Hermite1 k x * Hermite1 l x)
      = (Real.pi ^ (-(1 : ℝ) / 2)
          / (Real.sqrt (Nat.factorial k) * Real.sqrt (Nat.factorial l)))
        * (Polynomial.aeval (Real.sqrt 2 * x) (Polynomial.hermite k)
          * Polynomial.aeval (Real.sqrt 2 * x) (Polynomial.hermite l)
          * Real.exp (-x ^ 2)) := by
    intro x
    simp only [Hermite1]
    ring
  rw [integral_congr_ae (Filter.Eventually.of_forall hre), integral_const_mul, key k l]
  have hpi : Real.pi ^ (-(1 : ℝ) / 2) = (Real.sqrt Real.pi)⁻¹ := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_neg Real.pi_pos.le]
    norm_num
  by_cases h : k = l
  · subst h
    rw [if_pos rfl, if_pos rfl, Real.mul_self_sqrt (by positivity), hpi]
    have hfk : (0 : ℝ) < (Nat.factorial k : ℝ) := by positivity
    have hsp : (0 : ℝ) < Real.sqrt Real.pi := Real.sqrt_pos.mpr Real.pi_pos
    field_simp
  · rw [if_neg h, if_neg h, mul_zero]
