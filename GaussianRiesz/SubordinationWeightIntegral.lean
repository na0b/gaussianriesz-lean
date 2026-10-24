import GaussianRiesz.Preamble
open MeasureTheory
theorem SubordinationWeightIntegral :
    IntegrableOn (fun s : ℝ => (Real.sqrt s)⁻¹ * Real.exp (-s)) (Set.Ioi (0 : ℝ))
      ∧ ∫ s in Set.Ioi (0 : ℝ), (Real.sqrt s)⁻¹ * Real.exp (-s) = Real.sqrt Real.pi := by
  have hexp : ((1:ℝ)/2 - 1) = -((1:ℝ)/2) := by norm_num
  have hpt : ∀ s ∈ Set.Ioi (0 : ℝ),
      (fun s : ℝ => Real.exp (-s) * s ^ ((1:ℝ)/2 - 1)) s
        = (fun s : ℝ => (Real.sqrt s)⁻¹ * Real.exp (-s)) s := by
    intro s hs
    have hs' : (0:ℝ) ≤ s := le_of_lt hs
    simp only
    rw [Real.sqrt_eq_rpow, ← Real.rpow_neg hs', ← hexp, mul_comm]
  have hconv : IntegrableOn
      (fun x : ℝ => Real.exp (-x) * x ^ ((1:ℝ)/2 - 1)) (Set.Ioi 0) :=
    Real.GammaIntegral_convergent (by norm_num)
  have hint : IntegrableOn (fun s : ℝ => (Real.sqrt s)⁻¹ * Real.exp (-s)) (Set.Ioi (0:ℝ)) :=
    hconv.congr_fun hpt measurableSet_Ioi
  refine ⟨hint, ?_⟩
  have hval : ∫ s in Set.Ioi (0:ℝ), (Real.sqrt s)⁻¹ * Real.exp (-s)
      = ∫ s in Set.Ioi (0:ℝ), Real.exp (-s) * s ^ ((1:ℝ)/2 - 1) :=
    (setIntegral_congr_fun measurableSet_Ioi hpt).symm
  rw [hval, ← Real.Gamma_eq_integral (by norm_num : (0:ℝ) < 1/2), Real.Gamma_one_half_eq]
