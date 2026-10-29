module

public import GaussianRiesz.Preamble

@[expose] public section
open MeasureTheory
theorem TauPowerIntegralBounds :
    (∀ a : ℝ, 1 < a → ∃ K : ℝ, 0 < K ∧ ∀ b : ℝ, 0 < b →
        IntegrableOn (fun τ : ℝ => τ ^ (-a) * Real.exp (-b / τ)) (Set.Ioi (0:ℝ)) volume
          ∧ ∫ τ in Set.Ioi (0:ℝ), τ ^ (-a) * Real.exp (-b / τ) ≤ K * b ^ (1 - a))
      ∧ (∀ q c : ℝ, 1 < q → 0 < c → c ≤ 1 →
          IntegrableOn (fun τ : ℝ => τ ^ (-q)) (Set.Ioo c 1) volume
            ∧ ∫ τ in Set.Ioo c 1, τ ^ (-q) ≤ c ^ (1 - q) / (q - 1)) := by
  -- the elementary decay bound `exp (-t) <= m^m t^{-m}`
  have hpow : ∀ (m : ℕ), 1 ≤ m → ∀ t : ℝ, 0 < t →
      Real.exp (-t) ≤ (m : ℝ) ^ m * (t⁻¹) ^ m := by
    intro m hm t ht
    have h1 : t / (m : ℝ) ≤ Real.exp (t / (m : ℝ)) := by
      linarith [Real.add_one_le_exp (t / (m : ℝ))]
    have h2 : (t / (m : ℝ)) ^ m ≤ Real.exp (t / (m : ℝ)) ^ m :=
      pow_le_pow_left₀ (by positivity) h1 m
    have h3 : Real.exp (t / (m : ℝ)) ^ m = Real.exp t := by
      rw [← Real.exp_nat_mul]; congr 1; field_simp
    rw [h3, div_pow, div_le_iff₀ (by positivity)] at h2
    rw [inv_pow, ← div_eq_mul_inv, Real.exp_neg, inv_eq_one_div,
      div_le_div_iff₀ (Real.exp_pos t) (by positivity : (0:ℝ) < t ^ m)]
    linarith
  have hsplit : Set.Ioi (0:ℝ) = Set.Ioo (0:ℝ) 1 ∪ Set.Ici (1:ℝ) := by
    ext v
    simp only [Set.mem_Ioi, Set.mem_union, Set.mem_Ioo, Set.mem_Ici]
    constructor
    · intro hv
      rcases lt_or_ge v 1 with h | h
      · exact Or.inl ⟨hv, h⟩
      · exact Or.inr h
    · rintro (⟨h, -⟩ | h) <;> linarith
  constructor
  · -- fact (4)
    intro a ha
    obtain ⟨m, hm1, hma⟩ : ∃ m : ℕ, 1 ≤ m ∧ a ≤ (m : ℝ) := by
      refine ⟨⌈a⌉₊, ?_, Nat.le_ceil a⟩
      have h1 : (1:ℝ) ≤ (⌈a⌉₊ : ℝ) := le_trans (by linarith) (Nat.le_ceil a)
      exact_mod_cast h1
    have hcont : ∀ b : ℝ, 0 < b → ∀ s : Set ℝ, s ⊆ Set.Ioi (0:ℝ) →
        ContinuousOn (fun τ : ℝ => τ ^ (-a) * Real.exp (-b / τ)) s := by
      intro b hb s hs
      refine ContinuousOn.mul ?_ ?_
      · exact ContinuousOn.rpow_const continuousOn_id
          (fun v hv => Or.inl (ne_of_gt (hs hv)))
      · exact Real.continuous_exp.comp_continuousOn
          (continuousOn_const.div continuousOn_id (fun v hv => ne_of_gt (hs hv)))
    have hIB : ∀ b : ℝ, 0 < b →
        IntegrableOn (fun τ : ℝ => τ ^ (-a) * Real.exp (-b / τ)) (Set.Ioi (0:ℝ)) volume := by
      intro b hb
      have hnear : IntegrableOn (fun τ : ℝ => τ ^ (-a) * Real.exp (-b / τ))
          (Set.Ioo (0:ℝ) 1) volume := by
        have hdom : IntegrableOn (fun τ : ℝ => (m : ℝ) ^ m / b ^ m * τ ^ ((m : ℝ) - a))
            (Set.Ioo (0:ℝ) 1) volume :=
          Integrable.const_mul
            ((intervalIntegral.integrableOn_Ioo_rpow_iff zero_lt_one).2 (by linarith)) _
        refine Integrable.mono' hdom
          ((hcont b hb (Set.Ioo (0:ℝ) 1) (fun v hv => hv.1)).aestronglyMeasurable
            measurableSet_Ioo) ?_
        filter_upwards [ae_restrict_mem measurableSet_Ioo] with τ hτ
        have hτ0 : (0:ℝ) < τ := hτ.1
        have hdec : Real.exp (-b / τ) ≤ (m : ℝ) ^ m / b ^ m * τ ^ m := by
          have h := hpow m hm1 (b / τ) (by positivity)
          rw [show -b / τ = -(b / τ) by ring]
          refine h.trans_eq ?_
          rw [inv_div, div_pow]
          ring
        rw [Real.norm_eq_abs, abs_of_pos (by positivity)]
        calc τ ^ (-a) * Real.exp (-b / τ)
            ≤ τ ^ (-a) * ((m : ℝ) ^ m / b ^ m * τ ^ m) :=
              mul_le_mul_of_nonneg_left hdec (Real.rpow_pos_of_pos hτ0 _).le
          _ = (m : ℝ) ^ m / b ^ m * τ ^ ((m : ℝ) - a) := by
              rw [Real.rpow_sub hτ0, Real.rpow_natCast, Real.rpow_neg hτ0.le]
              field_simp
      have hfar : IntegrableOn (fun τ : ℝ => τ ^ (-a) * Real.exp (-b / τ))
          (Set.Ici (1:ℝ)) volume := by
        rw [integrableOn_Ici_iff_integrableOn_Ioi]
        have hdom : IntegrableOn (fun τ : ℝ => τ ^ (-a)) (Set.Ioi (1:ℝ)) volume :=
          integrableOn_Ioi_rpow_of_lt (by linarith) zero_lt_one
        refine Integrable.mono' hdom
          (((hcont b hb (Set.Ioi (1:ℝ)) fun v hv =>
            Set.mem_Ioi.2 (lt_trans zero_lt_one (Set.mem_Ioi.1 hv)))).aestronglyMeasurable
              measurableSet_Ioi) ?_
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with τ hτ
        have hτ0 : (0:ℝ) < τ := lt_trans zero_lt_one hτ
        have hvp : (0:ℝ) < τ ^ (-a) := Real.rpow_pos_of_pos hτ0 _
        have hle1 : Real.exp (-b / τ) ≤ 1 := by
          refine Real.exp_le_one_iff.2 ?_
          rw [div_nonpos_iff]
          exact Or.inr ⟨by linarith, hτ0.le⟩
        rw [Real.norm_eq_abs, abs_of_pos (by positivity)]
        calc τ ^ (-a) * Real.exp (-b / τ) ≤ τ ^ (-a) * 1 :=
              mul_le_mul_of_nonneg_left hle1 hvp.le
          _ = τ ^ (-a) := by ring
      rw [hsplit]; exact hnear.union hfar
    have hK := hIB 1 one_pos
    have hKpos : 0 < ∫ v in Set.Ioi (0:ℝ), v ^ (-a) * Real.exp (-1 / v) := by
      refine (setIntegral_pos_iff_support_of_nonneg_ae ?_ hK).2 ?_
      · filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
        have hv0 : (0:ℝ) < v := hv
        positivity
      · have hsub : Set.Ioo (0:ℝ) 1 ⊆
            Function.support (fun v : ℝ => v ^ (-a) * Real.exp (-1 / v)) ∩ Set.Ioi (0:ℝ) := by
          intro v hv
          have hv0 : (0:ℝ) < v := hv.1
          exact ⟨ne_of_gt (by positivity), hv.1⟩
        have hmm := measure_mono (μ := (volume : Measure ℝ)) hsub
        rw [Real.volume_Ioo] at hmm
        refine lt_of_lt_of_le ?_ hmm
        norm_num
    refine ⟨∫ v in Set.Ioi (0:ℝ), v ^ (-a) * Real.exp (-1 / v), hKpos, fun b hb => ⟨hIB b hb, ?_⟩⟩
    have hcongb : ∀ v ∈ Set.Ioi (0:ℝ),
        (b * v) ^ (-a) * Real.exp (-b / (b * v))
          = b ^ (-a) * (v ^ (-a) * Real.exp (-1 / v)) := by
      intro v hv
      have hv0 : (0:ℝ) < v := hv
      rw [Real.mul_rpow hb.le hv0.le, show -b / (b * v) = -1 / v by field_simp]
      ring
    have h := integral_comp_mul_left_Ioi
      (fun τ : ℝ => τ ^ (-a) * Real.exp (-b / τ)) 0 hb
    rw [mul_zero, setIntegral_congr_fun measurableSet_Ioi hcongb, integral_const_mul,
      smul_eq_mul] at h
    have hval : ∫ τ in Set.Ioi (0:ℝ), τ ^ (-a) * Real.exp (-b / τ)
        = b ^ (1 - a) * ∫ v in Set.Ioi (0:ℝ), v ^ (-a) * Real.exp (-1 / v) := by
      have hstep : ∫ τ in Set.Ioi (0:ℝ), τ ^ (-a) * Real.exp (-b / τ)
          = b * (b ^ (-a) * ∫ v in Set.Ioi (0:ℝ), v ^ (-a) * Real.exp (-1 / v)) := by
        rw [h]; field_simp
      rw [hstep, ← mul_assoc]
      congr 1
      rw [show (1:ℝ) - a = 1 + -a by ring, Real.rpow_add hb, Real.rpow_one]
    rw [hval, mul_comm]
  · -- fact (5)
    intro q c hq hc0 hc1
    have hcont : ContinuousOn (fun τ : ℝ => τ ^ (-q)) (Set.Icc c 1) :=
      ContinuousOn.rpow_const continuousOn_id
        (fun v hv => Or.inl (ne_of_gt (lt_of_lt_of_le hc0 hv.1)))
    refine ⟨(hcont.integrableOn_Icc).mono_set Set.Ioo_subset_Icc_self, ?_⟩
    have hzero : (0:ℝ) ∉ Set.uIcc c 1 := by
      rw [Set.uIcc_of_le hc1]
      simp only [Set.mem_Icc, not_and, not_le]
      intro h; linarith
    have heq : ∫ τ in Set.Ioo c 1, τ ^ (-q) = ∫ τ in c..1, τ ^ (-q) := by
      rw [intervalIntegral.integral_of_le hc1, ← integral_Ioc_eq_integral_Ioo]
    have hq1 : (0:ℝ) < q - 1 := by linarith
    rw [heq, integral_rpow (Or.inr ⟨by linarith, hzero⟩), Real.one_rpow,
      show -q + 1 = 1 - q by ring,
      show (1:ℝ) - q = -(q - 1) by ring, div_neg]
    rw [show -((1 - c ^ (-(q - 1))) / (q - 1)) = (c ^ (-(q - 1)) - 1) / (q - 1) by ring,
      div_le_div_iff_of_pos_right hq1]
    linarith
