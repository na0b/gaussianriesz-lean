import GaussianRiesz.Preamble
import GaussianRiesz.SubordinationIntegrandIntegrable
open MeasureTheory Set Filter Topology
theorem ScalarFractional (lam : ℝ) (hlam : 0 ≤ lam) :
    (1 / (2 * Real.sqrt Real.pi))
        * ∫ s in Set.Ioi (0 : ℝ), (1 - Real.exp (-s * lam)) / s ^ ((3 : ℝ) / 2)
      = Real.sqrt lam := by
  rcases eq_or_lt_of_le hlam with h | hpos
  · -- `lam = 0`: the integrand vanishes identically
    rw [← h]
    simp
  · -- `lam > 0`: the subordination computation
    have hcore : ∫ s in Ioi (0:ℝ), (1 - Real.exp (-s * lam)) / s ^ ((3:ℝ)/2)
        = 2 * Real.sqrt Real.pi * Real.sqrt lam := by
      -- the elementary inequality `1 - e^{-x} ≤ x`
      have hex : ∀ x : ℝ, 1 - Real.exp (-x) ≤ x := by
        intro x
        have := Real.add_one_le_exp (-x)
        linarith
      have hex0 : ∀ x : ℝ, 0 ≤ x → 0 ≤ 1 - Real.exp (-x) := by
        intro x hx
        have : Real.exp (-x) ≤ 1 := by
          rw [Real.exp_le_one_iff]; linarith
        linarith
      -- measurability
      have hmB : Measurable (fun s : ℝ => s ^ ((1:ℝ)/2 - 1) * Real.exp (-(lam * s))) := by fun_prop
      -- powers are integrable near zero
      have hpow : ∀ p : ℝ, -1 < p → IntegrableOn (fun s : ℝ => s ^ p) (Ioc (0:ℝ) 1) := by
        intro p hp
        rw [← intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one]
        exact intervalIntegral.intervalIntegrable_rpow' hp
      have hcover : Ioc (0:ℝ) 1 ∪ Ioi (1:ℝ) = Ioi (0:ℝ) := Ioc_union_Ioi_eq_Ioi zero_le_one
      -- (1) the two integrands are integrable on `(0,∞)`
      have hBint : IntegrableOn (fun s : ℝ => s ^ ((1:ℝ)/2 - 1) * Real.exp (-(lam * s)))
          (Ioi (0:ℝ)) := by
        rw [← hcover, integrableOn_union]
        constructor
        · refine Integrable.mono' (hpow (-(1/2) : ℝ) (by norm_num))
            hmB.aestronglyMeasurable.restrict ?_
          filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
          have hs0 : (0:ℝ) < s := hs.1
          rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
          rw [show (1:ℝ)/2 - 1 = -(1/2) by norm_num]
          refine mul_le_of_le_one_right (by positivity) ?_
          rw [Real.exp_le_one_iff]
          nlinarith
        · refine Integrable.mono' (exp_neg_integrableOn_Ioi 1 hpos)
            hmB.aestronglyMeasurable.restrict ?_
          filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
          have hs0 : (1:ℝ) < s := hs
          rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), neg_mul]
          refine mul_le_of_le_one_left (by positivity) ?_
          rw [show (1:ℝ)/2 - 1 = -(1/2) by norm_num, Real.rpow_neg (by linarith)]
          rw [inv_le_one_iff₀]
          right
          exact Real.one_le_rpow (by linarith) (by norm_num)
      have hAint := SubordinationIntegrandIntegrable lam hlam
      -- (2) the Gamma evaluation of the second integral
      have hB : ∫ s in Ioi (0:ℝ), s ^ ((1:ℝ)/2 - 1) * Real.exp (-(lam * s))
          = Real.sqrt Real.pi / Real.sqrt lam := by
        rw [Real.integral_rpow_mul_exp_neg_mul_Ioi (by norm_num) hpos, Real.Gamma_one_half_eq,
          ← Real.sqrt_eq_rpow, one_div, Real.sqrt_inv]
        field_simp
      -- (3) the antiderivative and its two boundary limits
      set g : ℝ → ℝ := fun s => -2 * (s ^ (-(1/2) : ℝ) * (1 - Real.exp (-s * lam))) with hg
      have hg0 : g 0 = 0 := by simp [hg]
      have hnorm : ∀ s : ℝ, 0 < s →
          ‖g s‖ = 2 * (s ^ (-(1/2) : ℝ) * (1 - Real.exp (-s * lam))) := by
        intro s hs0
        have hnn : 0 ≤ 1 - Real.exp (-s * lam) := by
          have := hex0 (s * lam) (by positivity)
          rw [show -s * lam = -(s * lam) by ring]
          exact this
        have hprod : (0:ℝ) ≤ s ^ (-(1/2) : ℝ) * (1 - Real.exp (-s * lam)) :=
          mul_nonneg (Real.rpow_nonneg hs0.le _) hnn
        have h2 : (0:ℝ) ≤ 2 * (s ^ (-(1/2) : ℝ) * (1 - Real.exp (-s * lam))) := by linarith
        simp only [hg]
        rw [show (-2 : ℝ) * (s ^ (-(1/2) : ℝ) * (1 - Real.exp (-s * lam)))
            = -(2 * (s ^ (-(1/2) : ℝ) * (1 - Real.exp (-s * lam)))) from by ring, norm_neg,
          Real.norm_eq_abs, abs_of_nonneg h2]
      have hderiv : ∀ s ∈ Ioi (0:ℝ), HasDerivAt g
          ((1 - Real.exp (-s * lam)) / s ^ ((3:ℝ)/2)
            - 2 * lam * (s ^ ((1:ℝ)/2 - 1) * Real.exp (-(lam * s)))) s := by
        intro s hs
        have hs0 : (0:ℝ) < s := hs
        have h1 : HasDerivAt (fun x : ℝ => x ^ (-(1/2) : ℝ))
            ((-(1/2) : ℝ) * s ^ ((-(1/2) : ℝ) - 1)) s :=
          Real.hasDerivAt_rpow_const (Or.inl hs0.ne')
        have h2 : HasDerivAt (fun x : ℝ => 1 - Real.exp (-x * lam))
            (lam * Real.exp (-s * lam)) s := by
          have hin : HasDerivAt (fun x : ℝ => -x * lam) (-lam) s := by
            refine ((hasDerivAt_id s).neg.mul_const lam).congr_deriv ?_
            ring
          have he : HasDerivAt (fun x : ℝ => Real.exp (-x * lam))
              (Real.exp (-s * lam) * -lam) s := hin.exp
          refine (he.const_sub 1).congr_deriv ?_
          ring
        have h3 := (h1.mul h2).const_mul (-2 : ℝ)
        refine h3.congr_deriv ?_
        rw [show (-(1/2) : ℝ) - 1 = -(3/2) by norm_num,
          show (1:ℝ)/2 - 1 = -(1/2) by norm_num,
          show -(lam * s) = -s * lam from by ring]
        simp only [Real.rpow_neg hs0.le]
        ring
      have hzero : ContinuousWithinAt g (Ici (0:ℝ)) 0 := by
        rw [ContinuousWithinAt, hg0]
        refine squeeze_zero_norm' (a := fun s : ℝ => 2 * lam * s ^ ((1:ℝ)/2)) ?_ ?_
        · filter_upwards [self_mem_nhdsWithin] with s hs
          rcases eq_or_lt_of_le (show (0:ℝ) ≤ s from hs) with h | h
          · rw [← h, hg0, Real.zero_rpow (by norm_num : ((1:ℝ)/2) ≠ 0)]
            simp
          · rw [hnorm s h]
            have hle : 1 - Real.exp (-s * lam) ≤ s * lam := by
              rw [show -s * lam = -(s * lam) by ring]
              exact hex (s * lam)
            have hkey2 : s ^ (-(1/2) : ℝ) * s = s ^ ((1:ℝ)/2) := by
              have hadd : s ^ (-(1/2) : ℝ) * s ^ (1:ℝ) = s ^ ((-(1/2) : ℝ) + 1) :=
                (Real.rpow_add h _ _).symm
              rw [Real.rpow_one] at hadd
              rw [hadd]
              norm_num
            calc 2 * (s ^ (-(1/2) : ℝ) * (1 - Real.exp (-s * lam)))
                ≤ 2 * (s ^ (-(1/2) : ℝ) * (s * lam)) := by
                  have := Real.rpow_nonneg h.le (-(1/2) : ℝ)
                  nlinarith
              _ = 2 * lam * s ^ ((1:ℝ)/2) := by rw [← hkey2]; ring
        · have ht : Tendsto (fun s : ℝ => s ^ ((1:ℝ)/2)) (𝓝[Ici (0:ℝ)] 0) (𝓝 0) := by
            have h := (Real.continuousAt_rpow_const 0 ((1:ℝ)/2)
              (Or.inr (by norm_num))).continuousWithinAt (s := Ici (0:ℝ))
            rw [ContinuousWithinAt] at h
            simpa [Real.zero_rpow] using h
          simpa using ht.const_mul (2 * lam)
      have hinf : Tendsto g atTop (𝓝 0) := by
        refine squeeze_zero_norm' (a := fun s : ℝ => 2 * s ^ (-(1/2) : ℝ)) ?_ ?_
        · filter_upwards [eventually_gt_atTop (0:ℝ)] with s hs
          rw [hnorm s hs]
          have h2 := Real.rpow_nonneg hs.le (-(1/2) : ℝ)
          nlinarith [Real.exp_pos (-s * lam)]
        · simpa using (tendsto_rpow_neg_atTop (by norm_num : (0:ℝ) < 1/2)).const_mul (2:ℝ)
      -- (4) the fundamental theorem of calculus on `(0,∞)`
      have hgint : IntegrableOn (fun s : ℝ => (1 - Real.exp (-s * lam)) / s ^ ((3:ℝ)/2)
          - 2 * lam * (s ^ ((1:ℝ)/2 - 1) * Real.exp (-(lam * s)))) (Ioi (0:ℝ)) :=
        hAint.sub (hBint.const_mul (2 * lam))
      have hFTC := integral_Ioi_of_hasDerivAt_of_tendsto hzero hderiv hgint hinf
      rw [hg0, sub_zero] at hFTC
      have hsub : ∫ s in Ioi (0:ℝ), ((1 - Real.exp (-s * lam)) / s ^ ((3:ℝ)/2)
            - 2 * lam * (s ^ ((1:ℝ)/2 - 1) * Real.exp (-(lam * s))))
          = (∫ s in Ioi (0:ℝ), (1 - Real.exp (-s * lam)) / s ^ ((3:ℝ)/2))
            - 2 * lam * ∫ s in Ioi (0:ℝ), s ^ ((1:ℝ)/2 - 1) * Real.exp (-(lam * s)) := by
        rw [← integral_const_mul]
        exact integral_sub hAint (hBint.const_mul (2 * lam))
      rw [hsub, hB] at hFTC
      have hrw : 2 * lam * (Real.sqrt Real.pi / Real.sqrt lam)
          = 2 * Real.sqrt Real.pi * Real.sqrt lam := by
        rw [show 2 * lam * (Real.sqrt Real.pi / Real.sqrt lam)
            = 2 * Real.sqrt Real.pi * (lam / Real.sqrt lam) from by ring, Real.div_sqrt]
      rw [hrw] at hFTC
      linarith
    rw [hcore]
    field_simp
