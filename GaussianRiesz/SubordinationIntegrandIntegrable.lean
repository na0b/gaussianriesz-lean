module

public import GaussianRiesz.Preamble

@[expose] public section
open MeasureTheory Set
theorem SubordinationIntegrandIntegrable (lam : ℝ) (hlam : 0 ≤ lam) :
    IntegrableOn (fun s : ℝ => (1 - Real.exp (-s * lam)) / s ^ ((3:ℝ)/2))
      (Ioi (0:ℝ)) := by
  have hex : ∀ x : ℝ, 1 - Real.exp (-x) ≤ x := by
    intro x
    have := Real.add_one_le_exp (-x)
    linarith
  have hex0 : ∀ x : ℝ, 0 ≤ x → 0 ≤ 1 - Real.exp (-x) := by
    intro x hx
    have : Real.exp (-x) ≤ 1 := by
      rw [Real.exp_le_one_iff]; linarith
    linarith
  have hmA : Measurable (fun s : ℝ => (1 - Real.exp (-s * lam)) / s ^ ((3:ℝ)/2)) := by fun_prop
  have hpow : ∀ p : ℝ, -1 < p → IntegrableOn (fun s : ℝ => s ^ p) (Ioc (0:ℝ) 1) := by
    intro p hp
    rw [← intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one]
    exact intervalIntegral.intervalIntegrable_rpow' hp
  have hcover : Ioc (0:ℝ) 1 ∪ Ioi (1:ℝ) = Ioi (0:ℝ) := Ioc_union_Ioi_eq_Ioi zero_le_one
  rw [← hcover, integrableOn_union]
  constructor
  · refine Integrable.mono' ((hpow (-(1/2) : ℝ) (by norm_num)).const_mul lam)
      hmA.aestronglyMeasurable.restrict ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    have hs0 : (0:ℝ) < s := hs.1
    have hnn : 0 ≤ 1 - Real.exp (-s * lam) := by
      have := hex0 (s * lam) (by positivity)
      rw [show -s * lam = -(s * lam) by ring]
      exact this
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have hkey : s / s ^ ((3:ℝ)/2) = s ^ (-(1/2) : ℝ) := by
      rw [eq_comm, eq_div_iff (by positivity), ← Real.rpow_add hs0]
      norm_num
    calc (1 - Real.exp (-s * lam)) / s ^ ((3:ℝ)/2)
        ≤ (s * lam) / s ^ ((3:ℝ)/2) := by
          refine div_le_div_of_nonneg_right ?_ (by positivity)
          rw [show -s * lam = -(s * lam) by ring]
          exact hex (s * lam)
      _ = lam * s ^ (-(1/2) : ℝ) := by rw [mul_comm s lam, mul_div_assoc, hkey]
  · refine Integrable.mono' (integrableOn_Ioi_rpow_of_lt
      (a := (-(3/2) : ℝ)) (by norm_num) one_pos) hmA.aestronglyMeasurable.restrict ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    have hs0 : (1:ℝ) < s := hs
    have hnn : 0 ≤ 1 - Real.exp (-s * lam) := by
      have := hex0 (s * lam) (by positivity)
      rw [show -s * lam = -(s * lam) by ring]
      exact this
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), Real.rpow_neg (by linarith),
      div_eq_mul_inv]
    refine mul_le_of_le_one_left (by positivity) ?_
    linarith [Real.exp_pos (-s * lam)]
