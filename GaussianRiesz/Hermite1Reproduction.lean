import GaussianRiesz.Hermite1
import GaussianRiesz.HermiteGenerating
import GaussianRiesz.HermiteAbsMajorant
import GaussianRiesz.HermiteDerivative
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import GaussianRiesz.ExpNegSqIntegrationByParts
open MeasureTheory
theorem Hermite1Reproduction (k : ℕ) (r t : ℝ) (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    ∫ σ : ℝ, Real.pi ^ (-(1 : ℝ) / 2) * Real.exp (-σ ^ 2)
        * Hermite1 k (r * t + Real.sqrt (1 - r ^ 2) * σ)
      = r ^ k * Hermite1 k t := by
  -- a monomial against the Gaussian weight is integrable
  have mono0 : ∀ m : ℕ, Integrable (fun σ : ℝ => Real.exp (-σ ^ 2) * σ ^ m) volume := by
    intro m
    have hs : (-1 : ℝ) < (m : ℝ) := by
      have h0 : (0:ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
      linarith
    have h := integrable_rpow_mul_exp_neg_mul_sq (b := 1) one_pos hs
    refine h.congr (Filter.Eventually.of_forall fun x => ?_)
    show x ^ ((m : ℕ) : ℝ) * Real.exp (-1 * x ^ 2) = Real.exp (-x ^ 2) * x ^ m
    rw [Real.rpow_natCast]
    ring_nf
  -- powers of an affine function against the Gaussian weight
  have monoAff : ∀ (a b : ℝ) (n m : ℕ),
      Integrable (fun σ : ℝ => Real.exp (-σ ^ 2) * (σ ^ m * (a + b * σ) ^ n)) volume := by
    intro a b n
    induction n with
    | zero =>
      intro m
      refine (mono0 m).congr (Filter.Eventually.of_forall fun x => ?_)
      simp
    | succ p ih =>
      intro m
      have h1 := (ih m).const_mul a
      have h2 := (ih (m + 1)).const_mul b
      refine (h1.add h2).congr (Filter.Eventually.of_forall fun x => ?_)
      show a * (Real.exp (-x ^ 2) * (x ^ m * (a + b * x) ^ p))
          + b * (Real.exp (-x ^ 2) * (x ^ (m + 1) * (a + b * x) ^ p))
        = Real.exp (-x ^ 2) * (x ^ m * (a + b * x) ^ (p + 1))
      rw [pow_succ, pow_succ]
      ring
  -- a polynomial in an affine variable against the Gaussian weight
  have monoPoly : ∀ (a b : ℝ) (p : Polynomial ℤ) (m : ℕ),
      Integrable (fun σ : ℝ => Real.exp (-σ ^ 2)
        * (σ ^ m * Polynomial.aeval (a + b * σ) p)) volume := by
    intro a b p
    induction p using Polynomial.induction_on' with
    | add q s hq hs =>
      intro m
      refine ((hq m).add (hs m)).congr (Filter.Eventually.of_forall fun x => ?_)
      show Real.exp (-x ^ 2) * (x ^ m * Polynomial.aeval (a + b * x) q)
          + Real.exp (-x ^ 2) * (x ^ m * Polynomial.aeval (a + b * x) s)
        = Real.exp (-x ^ 2) * (x ^ m * Polynomial.aeval (a + b * x) (q + s))
      rw [map_add]
      ring
    | monomial n c =>
      intro m
      have h := (monoAff a b n m).const_mul ((c : ℝ))
      refine h.congr (Filter.Eventually.of_forall fun x => ?_)
      show (c : ℝ) * (Real.exp (-x ^ 2) * (x ^ m * (a + b * x) ^ n))
        = Real.exp (-x ^ 2) * (x ^ m * Polynomial.aeval (a + b * x) (Polynomial.monomial n c))
      rw [Polynomial.aeval_monomial, eq_intCast]
      ring
  -- the chain rule for a polynomial in an affine variable
  have affDeriv : ∀ (a b : ℝ) (p : Polynomial ℤ) (σ : ℝ),
      HasDerivAt (fun s : ℝ => Polynomial.aeval (a + b * s) p)
        (b * Polynomial.aeval (a + b * σ) (Polynomial.derivative p)) σ := by
    intro a b p σ
    have h1 : HasDerivAt (fun s : ℝ => a + b * s) b σ := by
      simpa using ((hasDerivAt_id σ).const_mul b).const_add a
    have h2 : HasDerivAt (fun y : ℝ => Polynomial.aeval y p)
        (Polynomial.aeval (a + b * σ) (Polynomial.derivative p)) (a + b * σ) := by
      have hd : DifferentiableAt ℝ (fun y : ℝ => Polynomial.aeval y p) (a + b * σ) :=
        (Polynomial.differentiable_aeval p).differentiableAt
      simpa [Polynomial.deriv_aeval] using hd.hasDerivAt
    refine (h2.comp σ h1).congr_deriv ?_
    ring
  have hr2 : r ^ 2 ≤ 1 := by nlinarith
  obtain ⟨c, hcdef⟩ : ∃ c : ℝ, c = Real.pi ^ (-(1 : ℝ) / 2) := ⟨_, rfl⟩
  obtain ⟨α, hαdef⟩ : ∃ α : ℝ, α = Real.sqrt 2 * (r * t) := ⟨_, rfl⟩
  obtain ⟨β, hβdef⟩ : ∃ β : ℝ, β = Real.sqrt 2 * Real.sqrt (1 - r ^ 2) := ⟨_, rfl⟩
  have hβsq : β ^ 2 = 2 * (1 - r ^ 2) := by
    rw [hβdef, mul_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2),
      Real.sq_sqrt (by linarith : (0:ℝ) ≤ 1 - r ^ 2)]
  -- pulling the normalising constant out of an integral
  have hpull : ∀ f : ℝ → ℝ, (∫ σ : ℝ, c * Real.exp (-σ ^ 2) * f σ)
      = c * ∫ σ : ℝ, Real.exp (-σ ^ 2) * f σ := by
    intro f
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun σ => ?_)
    show c * Real.exp (-σ ^ 2) * f σ = c * (Real.exp (-σ ^ 2) * f σ)
    ring
  -- `γ₁` is a probability measure
  have hcpi : c * Real.sqrt Real.pi = 1 := by
    rw [hcdef, Real.sqrt_eq_rpow, ← Real.rpow_add Real.pi_pos]
    norm_num
  have hgauss : (∫ σ : ℝ, Real.exp (-σ ^ 2) * (1 : ℝ)) = Real.sqrt Real.pi := by
    have h := integral_gaussian 1
    rw [show (∫ σ : ℝ, Real.exp (-σ ^ 2) * (1 : ℝ))
        = ∫ σ : ℝ, Real.exp (-1 * σ ^ 2) from
      integral_congr_ae (Filter.Eventually.of_forall fun σ => by ring_nf), h]
    norm_num
  -- integrability of the integrands that occur
  have hI : ∀ (p : Polynomial ℤ) (m : ℕ),
      Integrable (fun σ : ℝ => Real.exp (-σ ^ 2)
        * (σ ^ m * Polynomial.aeval (α + β * σ) p)) volume := fun p m => monoPoly α β p m
  have hI0 : ∀ p : Polynomial ℤ,
      Integrable (fun σ : ℝ => Real.exp (-σ ^ 2)
        * Polynomial.aeval (α + β * σ) p) volume := by
    intro p
    refine (hI p 0).congr (Filter.Eventually.of_forall fun σ => ?_)
    show Real.exp (-σ ^ 2) * (σ ^ 0 * Polynomial.aeval (α + β * σ) p)
        = Real.exp (-σ ^ 2) * Polynomial.aeval (α + β * σ) p
    rw [pow_zero, one_mul]
  have hI1 : ∀ p : Polynomial ℤ,
      Integrable (fun σ : ℝ => Real.exp (-σ ^ 2)
        * (σ * Polynomial.aeval (α + β * σ) p)) volume := by
    intro p
    refine (hI p 1).congr (Filter.Eventually.of_forall fun σ => ?_)
    show Real.exp (-σ ^ 2) * (σ ^ 1 * Polynomial.aeval (α + β * σ) p)
        = Real.exp (-σ ^ 2) * (σ * Polynomial.aeval (α + β * σ) p)
    rw [pow_one]
  -- the first moment vanishes
  have hmom : (∫ σ : ℝ, Real.exp (-σ ^ 2) * (σ * (1 : ℝ))) = 0 := by
    have h := ExpNegSqIntegrationByParts (fun _ : ℝ => (1 : ℝ)) (fun _ : ℝ => (0 : ℝ))
      (fun σ => hasDerivAt_const σ (1 : ℝ))
      (by simp)
      (by
        refine (mono0 1).congr (Filter.Eventually.of_forall fun σ => ?_)
        show Real.exp (-σ ^ 2) * σ ^ 1 = Real.exp (-σ ^ 2) * (σ * (1 : ℝ))
        rw [pow_one]
        ring)
      (by
        refine (mono0 0).congr (Filter.Eventually.of_forall fun σ => ?_)
        show Real.exp (-σ ^ 2) * σ ^ 0 = Real.exp (-σ ^ 2) * (1 : ℝ)
        rw [pow_zero])
    rw [h]
    simp
  -- the pointwise Hermite recurrence
  have hpt : ∀ (y : ℝ) (j : ℕ), Polynomial.aeval y (Polynomial.hermite (j + 2))
      = y * Polynomial.aeval y (Polynomial.hermite (j + 1))
        - ((j : ℝ) + 1) * Polynomial.aeval y (Polynomial.hermite j) := by
    intro y j
    rw [Polynomial.hermite_succ (j + 1), HermiteDerivative j, map_sub, map_mul,
      Polynomial.aeval_X, map_nsmul, nsmul_eq_mul]
    push_cast
    ring
  -- the integral functional and its recurrence
  obtain ⟨A, hAdef⟩ : ∃ A : ℕ → ℝ, A = fun j =>
      ∫ σ : ℝ, c * Real.exp (-σ ^ 2)
        * Polynomial.aeval (α + β * σ) (Polynomial.hermite j) := ⟨_, rfl⟩
  have hA0 : A 0 = 1 := by
    rw [hAdef]
    show (∫ σ : ℝ, c * Real.exp (-σ ^ 2)
      * Polynomial.aeval (α + β * σ) (Polynomial.hermite 0)) = 1
    rw [show (fun σ : ℝ => c * Real.exp (-σ ^ 2)
          * Polynomial.aeval (α + β * σ) (Polynomial.hermite 0))
        = fun σ : ℝ => c * Real.exp (-σ ^ 2) * (1 : ℝ) from by
      funext σ
      simp [Polynomial.hermite_zero]]
    rw [hpull (fun _ => (1:ℝ)), hgauss, hcpi]
  have hA1 : A 1 = α := by
    rw [hAdef]
    show (∫ σ : ℝ, c * Real.exp (-σ ^ 2)
      * Polynomial.aeval (α + β * σ) (Polynomial.hermite 1)) = α
    have hsplit : (∫ σ : ℝ, c * Real.exp (-σ ^ 2)
          * Polynomial.aeval (α + β * σ) (Polynomial.hermite 1))
        = ∫ σ : ℝ, (α * (c * Real.exp (-σ ^ 2) * (1 : ℝ))
            + β * (c * Real.exp (-σ ^ 2) * (σ * (1 : ℝ)))) := by
      refine integral_congr_ae (Filter.Eventually.of_forall fun σ => ?_)
      show c * Real.exp (-σ ^ 2)
            * Polynomial.aeval (α + β * σ) (Polynomial.hermite 1)
          = α * (c * Real.exp (-σ ^ 2) * (1 : ℝ))
            + β * (c * Real.exp (-σ ^ 2) * (σ * (1 : ℝ)))
      simp only [Polynomial.hermite_one, Polynomial.aeval_X]
      ring
    have j1 : Integrable (fun σ : ℝ => α * (c * Real.exp (-σ ^ 2) * (1 : ℝ))) volume := by
      refine ((mono0 0).const_mul (α * c)).congr (Filter.Eventually.of_forall fun σ => ?_)
      show α * c * (Real.exp (-σ ^ 2) * σ ^ 0) = α * (c * Real.exp (-σ ^ 2) * (1 : ℝ))
      rw [pow_zero]
      ring
    have j2 : Integrable
        (fun σ : ℝ => β * (c * Real.exp (-σ ^ 2) * (σ * (1 : ℝ)))) volume := by
      refine ((mono0 1).const_mul (β * c)).congr (Filter.Eventually.of_forall fun σ => ?_)
      show β * c * (Real.exp (-σ ^ 2) * σ ^ 1) = β * (c * Real.exp (-σ ^ 2) * (σ * (1 : ℝ)))
      rw [pow_one]
      ring
    rw [hsplit, integral_add j1 j2, integral_const_mul, integral_const_mul,
      hpull (fun _ => (1:ℝ)), hpull (fun σ => σ * (1:ℝ)), hgauss, hmom, hcpi]
    ring
  -- the recurrence satisfied by the integrals
  have hAstep : ∀ j : ℕ, A (j + 2) = α * A (j + 1) - r ^ 2 * ((j : ℝ) + 1) * A j := by
    intro j
    have hgd : ∀ σ : ℝ,
        HasDerivAt (fun s : ℝ => Polynomial.aeval (α + β * s) (Polynomial.hermite (j + 1)))
          (β * (((j : ℝ) + 1)
            * Polynomial.aeval (α + β * σ) (Polynomial.hermite j))) σ := by
      intro σ
      refine (affDeriv α β (Polynomial.hermite (j + 1)) σ).congr_deriv ?_
      rw [HermiteDerivative j, map_nsmul, nsmul_eq_mul]
      push_cast
      ring
    have i1 : Integrable (fun σ : ℝ => Real.exp (-σ ^ 2)
        * (β * (((j : ℝ) + 1)
          * Polynomial.aeval (α + β * σ) (Polynomial.hermite j)))) volume := by
      refine ((hI0 (Polynomial.hermite j)).const_mul (β * ((j : ℝ) + 1))).congr
        (Filter.Eventually.of_forall fun σ => ?_)
      show β * ((j : ℝ) + 1) * (Real.exp (-σ ^ 2)
            * Polynomial.aeval (α + β * σ) (Polynomial.hermite j))
          = Real.exp (-σ ^ 2) * (β * (((j : ℝ) + 1)
            * Polynomial.aeval (α + β * σ) (Polynomial.hermite j)))
      ring
    have hM := ExpNegSqIntegrationByParts
      (fun s : ℝ => Polynomial.aeval (α + β * s) (Polynomial.hermite (j + 1)))
      (fun s : ℝ => β * (((j : ℝ) + 1)
        * Polynomial.aeval (α + β * s) (Polynomial.hermite j)))
      hgd i1 (hI1 (Polynomial.hermite (j + 1))) (hI0 (Polynomial.hermite (j + 1)))
    have hM2 : (∫ σ : ℝ, Real.exp (-σ ^ 2) * (β * (((j : ℝ) + 1)
          * Polynomial.aeval (α + β * σ) (Polynomial.hermite j))))
        = (β * ((j : ℝ) + 1))
          * ∫ σ : ℝ, Real.exp (-σ ^ 2)
            * Polynomial.aeval (α + β * σ) (Polynomial.hermite j) := by
      rw [← integral_const_mul]
      refine integral_congr_ae (Filter.Eventually.of_forall fun σ => ?_)
      show Real.exp (-σ ^ 2) * (β * (((j : ℝ) + 1)
            * Polynomial.aeval (α + β * σ) (Polynomial.hermite j)))
          = β * ((j : ℝ) + 1) * (Real.exp (-σ ^ 2)
            * Polynomial.aeval (α + β * σ) (Polynomial.hermite j))
      ring
    rw [hM2] at hM
    -- split the integral defining `A (j+2)`
    have k1 : Integrable (fun σ : ℝ => α * (c * Real.exp (-σ ^ 2)
        * Polynomial.aeval (α + β * σ) (Polynomial.hermite (j + 1)))) volume := by
      refine ((hI0 (Polynomial.hermite (j + 1))).const_mul (α * c)).congr
        (Filter.Eventually.of_forall fun σ => ?_)
      show α * c * (Real.exp (-σ ^ 2)
            * Polynomial.aeval (α + β * σ) (Polynomial.hermite (j + 1)))
          = α * (c * Real.exp (-σ ^ 2)
            * Polynomial.aeval (α + β * σ) (Polynomial.hermite (j + 1)))
      ring
    have k2 : Integrable (fun σ : ℝ => β * (c * Real.exp (-σ ^ 2)
        * (σ * Polynomial.aeval (α + β * σ) (Polynomial.hermite (j + 1))))) volume := by
      refine ((hI1 (Polynomial.hermite (j + 1))).const_mul (β * c)).congr
        (Filter.Eventually.of_forall fun σ => ?_)
      show β * c * (Real.exp (-σ ^ 2)
            * (σ * Polynomial.aeval (α + β * σ) (Polynomial.hermite (j + 1))))
          = β * (c * Real.exp (-σ ^ 2)
            * (σ * Polynomial.aeval (α + β * σ) (Polynomial.hermite (j + 1))))
      ring
    have k3 : Integrable (fun σ : ℝ => ((j : ℝ) + 1) * (c * Real.exp (-σ ^ 2)
        * Polynomial.aeval (α + β * σ) (Polynomial.hermite j))) volume := by
      refine ((hI0 (Polynomial.hermite j)).const_mul (((j : ℝ) + 1) * c)).congr
        (Filter.Eventually.of_forall fun σ => ?_)
      show ((j : ℝ) + 1) * c * (Real.exp (-σ ^ 2)
            * Polynomial.aeval (α + β * σ) (Polynomial.hermite j))
          = ((j : ℝ) + 1) * (c * Real.exp (-σ ^ 2)
            * Polynomial.aeval (α + β * σ) (Polynomial.hermite j))
      ring
    have hsplit : A (j + 2)
        = ∫ σ : ℝ, (α * (c * Real.exp (-σ ^ 2)
              * Polynomial.aeval (α + β * σ) (Polynomial.hermite (j + 1)))
            + β * (c * Real.exp (-σ ^ 2)
              * (σ * Polynomial.aeval (α + β * σ) (Polynomial.hermite (j + 1))))
            - ((j : ℝ) + 1) * (c * Real.exp (-σ ^ 2)
              * Polynomial.aeval (α + β * σ) (Polynomial.hermite j))) := by
      rw [hAdef]
      refine integral_congr_ae (Filter.Eventually.of_forall fun σ => ?_)
      show c * Real.exp (-σ ^ 2)
            * Polynomial.aeval (α + β * σ) (Polynomial.hermite (j + 2))
          = α * (c * Real.exp (-σ ^ 2)
              * Polynomial.aeval (α + β * σ) (Polynomial.hermite (j + 1)))
            + β * (c * Real.exp (-σ ^ 2)
              * (σ * Polynomial.aeval (α + β * σ) (Polynomial.hermite (j + 1))))
            - ((j : ℝ) + 1) * (c * Real.exp (-σ ^ 2)
              * Polynomial.aeval (α + β * σ) (Polynomial.hermite j))
      rw [hpt (α + β * σ) j]
      ring
    have hAj : A j = c * ∫ σ : ℝ, Real.exp (-σ ^ 2)
        * Polynomial.aeval (α + β * σ) (Polynomial.hermite j) := by
      rw [hAdef]
      exact hpull _
    have hAj1 : A (j + 1) = c * ∫ σ : ℝ, Real.exp (-σ ^ 2)
        * Polynomial.aeval (α + β * σ) (Polynomial.hermite (j + 1)) := by
      rw [hAdef]
      exact hpull _
    have k12 : Integrable (fun σ : ℝ => α * (c * Real.exp (-σ ^ 2)
          * Polynomial.aeval (α + β * σ) (Polynomial.hermite (j + 1)))
        + β * (c * Real.exp (-σ ^ 2)
          * (σ * Polynomial.aeval (α + β * σ) (Polynomial.hermite (j + 1))))) volume :=
      (k1.add k2).congr (Filter.Eventually.of_forall fun σ => rfl)
    rw [hsplit, integral_sub k12 k3, integral_add k1 k2,
      integral_const_mul, integral_const_mul, integral_const_mul,
      hpull (fun σ => Polynomial.aeval (α + β * σ) (Polynomial.hermite (j + 1))),
      hpull (fun σ => σ * Polynomial.aeval (α + β * σ) (Polynomial.hermite (j + 1))),
      hpull (fun σ => Polynomial.aeval (α + β * σ) (Polynomial.hermite j)), hM,
      hAj, hAj1]
    linear_combination (((j : ℝ) + 1) * c
      * (∫ σ : ℝ, Real.exp (-σ ^ 2)
          * Polynomial.aeval (α + β * σ) (Polynomial.hermite j)) / 2) * hβsq
  -- two-step induction
  have hkey : ∀ j : ℕ,
      A j = r ^ j * Polynomial.aeval (Real.sqrt 2 * t) (Polynomial.hermite j)
        ∧ A (j + 1) = r ^ (j + 1)
          * Polynomial.aeval (Real.sqrt 2 * t) (Polynomial.hermite (j + 1)) := by
    intro j
    induction j with
    | zero =>
      refine ⟨?_, ?_⟩
      · show A 0 = r ^ 0 * Polynomial.aeval (Real.sqrt 2 * t) (Polynomial.hermite 0)
        rw [hA0]
        simp [Polynomial.hermite_zero]
      · show A 1 = r ^ 1 * Polynomial.aeval (Real.sqrt 2 * t) (Polynomial.hermite 1)
        rw [hA1, hαdef]
        simp only [Polynomial.hermite_one, Polynomial.aeval_X, pow_one]
        ring
    | succ m ih =>
      refine ⟨ih.2, ?_⟩
      show A (m + 2) = r ^ (m + 2)
        * Polynomial.aeval (Real.sqrt 2 * t) (Polynomial.hermite (m + 2))
      rw [hAstep m, ih.1, ih.2, hpt (Real.sqrt 2 * t) m, hαdef]
      ring
  -- convert the goal
  have hgoal : (∫ σ : ℝ, c * Real.exp (-σ ^ 2)
        * Hermite1 k (r * t + Real.sqrt (1 - r ^ 2) * σ))
      = A k / Real.sqrt (Nat.factorial k) := by
    rw [hAdef, ← integral_div]
    refine integral_congr_ae (Filter.Eventually.of_forall fun σ => ?_)
    show c * Real.exp (-σ ^ 2) * Hermite1 k (r * t + Real.sqrt (1 - r ^ 2) * σ)
        = c * Real.exp (-σ ^ 2) * Polynomial.aeval (α + β * σ) (Polynomial.hermite k)
          / Real.sqrt (Nat.factorial k)
    simp only [Hermite1]
    rw [hαdef, hβdef, show Real.sqrt 2 * (r * t + Real.sqrt (1 - r ^ 2) * σ)
        = Real.sqrt 2 * (r * t) + Real.sqrt 2 * Real.sqrt (1 - r ^ 2) * σ from by ring]
    ring
  rw [← hcdef, hgoal, (hkey k).1]
  simp only [Hermite1]
  ring
