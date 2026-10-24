import GaussianRiesz.GaussRieszKernel
import GaussianRiesz.MehlerKernelXDerivative
open MeasureTheory
theorem PVKernelTimeIntegral {n : ℕ} (j : Fin n) (x y : EuclideanSpace ℝ (Fin n)) :
    (IntegrableOn (fun s : ℝ => (Real.sqrt s)⁻¹ *
          (Real.sqrt 2 * Real.exp (-s) * (y j - Real.exp (-s) * x j) / (1 - Real.exp (-2 * s))
            * (Real.pi ^ (-(n : ℝ) / 2) * (1 - Real.exp (-2 * s)) ^ (-(n : ℝ) / 2)
                * Real.exp (-‖Real.exp (-s) • x - y‖ ^ 2 / (1 - Real.exp (-2 * s))))))
        (Set.Ioi (0 : ℝ))
      ↔ IntegrableOn (fun r : ℝ =>
          (y j - r * x j) / ((1 - r ^ 2) ^ ((n : ℝ) / 2 + 1) * Real.sqrt (-Real.log r))
            * Real.exp (-‖r • x - y‖ ^ 2 / (1 - r ^ 2))) (Set.Ioo (0 : ℝ) 1))
      ∧ GaussRieszKernel j x y
          = (Real.sqrt Real.pi)⁻¹ * ∫ s in Set.Ioi (0 : ℝ), (Real.sqrt s)⁻¹ *
              (Real.sqrt 2 * Real.exp (-s) * (y j - Real.exp (-s) * x j)
                  / (1 - Real.exp (-2 * s))
                * (Real.pi ^ (-(n : ℝ) / 2) * (1 - Real.exp (-2 * s)) ^ (-(n : ℝ) / 2)
                    * Real.exp (-‖Real.exp (-s) • x - y‖ ^ 2 / (1 - Real.exp (-2 * s))))) := by
  classical
  set g : ℝ → ℝ := fun r =>
    (y j - r * x j) / ((1 - r ^ 2) ^ ((n : ℝ) / 2 + 1) * Real.sqrt (-Real.log r))
      * Real.exp (-‖r • x - y‖ ^ 2 / (1 - r ^ 2)) with hg
  set H : ℝ → ℝ := fun s => (Real.sqrt s)⁻¹ *
    (Real.sqrt 2 * Real.exp (-s) * (y j - Real.exp (-s) * x j) / (1 - Real.exp (-2 * s))
      * (Real.pi ^ (-(n : ℝ) / 2) * (1 - Real.exp (-2 * s)) ^ (-(n : ℝ) / 2)
          * Real.exp (-‖Real.exp (-s) • x - y‖ ^ 2 / (1 - Real.exp (-2 * s))))) with hH
  set A : ℝ := Real.sqrt 2 * Real.pi ^ (-((n : ℝ) + 1) / 2) with hA
  have hApos : 0 < A := by
    rw [hA]
    exact mul_pos (by positivity) (Real.rpow_pos_of_pos Real.pi_pos _)
  -- the substitution `ρ = e^{-s}` as a change of variables on `(0,∞)`
  have himg : Set.image (fun s : ℝ => Real.exp (-s)) (Set.Ioi 0) = Set.Ioo 0 1 := by
    ext ρ
    simp only [Set.mem_image, Set.mem_Ioi, Set.mem_Ioo]
    constructor
    · rintro ⟨s, hs, rfl⟩
      refine ⟨Real.exp_pos _, ?_⟩
      rw [Real.exp_lt_one_iff]; linarith
    · rintro ⟨h0, h1⟩
      refine ⟨-Real.log ρ, ?_, ?_⟩
      · have := Real.log_neg h0 h1; linarith
      · rw [neg_neg, Real.exp_log h0]
  have hderiv : ∀ s ∈ Set.Ioi (0 : ℝ),
      HasDerivWithinAt (fun s : ℝ => Real.exp (-s)) (-Real.exp (-s)) (Set.Ioi (0 : ℝ)) s := by
    intro s _
    have h : HasDerivAt (fun s : ℝ => Real.exp (-s)) (Real.exp (-s) * -1) s :=
      (Real.hasDerivAt_exp (-s)).comp s (hasDerivAt_neg s)
    have h2 : HasDerivAt (fun s : ℝ => Real.exp (-s)) (-Real.exp (-s)) s := by simpa using h
    exact h2.hasDerivWithinAt
  have hinj : Set.InjOn (fun s : ℝ => Real.exp (-s)) (Set.Ioi 0) := by
    intro a _ b _ h
    simp only at h
    have := Real.exp_injective h
    linarith
  -- the constant identity `√π · A = √2 · π^{-n/2}`
  have hC : Real.sqrt Real.pi * A = Real.sqrt 2 * Real.pi ^ (-(n : ℝ) / 2) := by
    have hpi : Real.sqrt Real.pi * Real.pi ^ (-((n : ℝ) + 1) / 2)
        = Real.pi ^ (-(n : ℝ) / 2) := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_add Real.pi_pos,
        show (1 : ℝ) / 2 + -((n : ℝ) + 1) / 2 = -(n : ℝ) / 2 from by ring]
    rw [hA]
    calc Real.sqrt Real.pi * (Real.sqrt 2 * Real.pi ^ (-((n : ℝ) + 1) / 2))
        = Real.sqrt 2 * (Real.sqrt Real.pi * Real.pi ^ (-((n : ℝ) + 1) / 2)) := by ring
      _ = Real.sqrt 2 * Real.pi ^ (-(n : ℝ) / 2) := by rw [hpi]
  -- the pointwise identity under the substitution
  have hpt : ∀ s : ℝ, 0 < s →
      |(-Real.exp (-s))| • g (Real.exp (-s)) = (Real.sqrt Real.pi * A)⁻¹ * H s := by
    intro s hs
    have hr0 : (0 : ℝ) < Real.exp (-s) := Real.exp_pos _
    set σ : ℝ := 1 - Real.exp (-2 * s) with hσ
    have hσ0 : 0 < σ := by
      rw [hσ]
      have h : Real.exp (-2 * s) < 1 := by rw [Real.exp_lt_one_iff]; linarith
      linarith
    have hsq : 1 - Real.exp (-s) ^ 2 = σ := by
      rw [hσ, pow_two, ← Real.exp_add, show (-s) + (-s) = -2 * s from by ring]
    have hlog : -Real.log (Real.exp (-s)) = s := by rw [Real.log_exp]; ring
    have habs : |(-Real.exp (-s))| = Real.exp (-s) := by rw [abs_neg, abs_of_pos hr0]
    have hσpow : σ ^ (-(n : ℝ) / 2) = (σ ^ ((n : ℝ) / 2))⁻¹ := by
      rw [neg_div, Real.rpow_neg hσ0.le]
    have hσadd : σ ^ ((n : ℝ) / 2 + 1) = σ ^ ((n : ℝ) / 2) * σ := by
      rw [Real.rpow_add hσ0, Real.rpow_one]
    rw [habs, smul_eq_mul, hC]
    simp only [hg, hH]
    rw [hsq, hlog, hσpow, hσadd]
    set E : ℝ := Real.exp (-‖Real.exp (-s) • x - y‖ ^ 2 / σ) with hEdef
    set Y : ℝ := y j - Real.exp (-s) * x j with hYdef
    set P : ℝ := σ ^ ((n : ℝ) / 2) with hPdef
    have hnorm : (1 : ℝ) - Real.exp (-(s * 2)) = σ := by
      rw [hσ, show -(s * 2) = -2 * s from by ring]
    field_simp
    rw [hnorm]
    field_simp
  -- the change of variables, in both the integral and the integrability form
  refine ⟨?_, ?_⟩
  · rw [← himg,
      integrableOn_image_iff_integrableOn_abs_deriv_smul measurableSet_Ioi hderiv hinj g]
    constructor
    · intro h
      refine IntegrableOn.congr_fun (h.const_mul ((Real.sqrt Real.pi * A)⁻¹)) ?_
        measurableSet_Ioi
      intro s hs
      exact (hpt s hs).symm
    · intro h
      refine IntegrableOn.congr_fun (h.const_mul (Real.sqrt Real.pi * A)) ?_
        measurableSet_Ioi
      intro s hs
      simp only
      rw [hpt s hs, ← mul_assoc, mul_inv_cancel₀ (by positivity), one_mul]
  · have hK : GaussRieszKernel j x y = A * ∫ r in Set.Ioo (0 : ℝ) 1, g r := by
      rw [hA, hg, GaussRieszKernel]
    have hcv : ∫ r in Set.Ioo (0 : ℝ) 1, g r
        = (Real.sqrt Real.pi * A)⁻¹ * ∫ s in Set.Ioi (0 : ℝ), H s := by
      rw [← himg, integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi hderiv hinj g,
        ← integral_const_mul]
      exact setIntegral_congr_fun measurableSet_Ioi fun s hs => hpt s hs
    rw [hK, hcv]
    field_simp
