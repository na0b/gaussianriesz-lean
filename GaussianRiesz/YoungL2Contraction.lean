import GaussianRiesz.Preamble
open MeasureTheory
open scoped ENNReal
theorem YoungL2Contraction {n : ℕ} (κ : EuclideanSpace ℝ (Fin n) → ℝ)
    (hκm : Measurable κ) (hκ0 : ∀ t, 0 ≤ κ t)
    (hκint : Integrable κ volume) (hκ1 : ∫ t, κ t = 1)
    (h : EuclideanSpace ℝ (Fin n) → ℝ) (hh : AEStronglyMeasurable h volume) :
    eLpNorm (fun x => convolution κ h (ContinuousLinearMap.lsmul ℝ ℝ) volume x) 2 volume
      ≤ eLpNorm h 2 volume := by
  have hL1 : ∫⁻ t, ENNReal.ofReal (κ t) ∂(volume : Measure (EuclideanSpace ℝ (Fin n))) = 1 := by
    rw [← ofReal_integral_eq_lintegral_ofReal hκint (Filter.Eventually.of_forall hκ0), hκ1,
      ENNReal.ofReal_one]
  have hhx : ∀ x : EuclideanSpace ℝ (Fin n),
      AEMeasurable (fun t => ‖h (x - t)‖ₑ) (volume : Measure (EuclideanSpace ℝ (Fin n))) :=
    fun x => (hh.comp_measurePreserving (Measure.measurePreserving_sub_left volume x)).enorm
  have h2 : ∀ y : ℝ≥0∞, y ^ (2:ℝ) = y * y := by
    intro y
    rw [show (2:ℝ) = ((2:ℕ):ℝ) by norm_num, ENNReal.rpow_natCast, pow_two]
  -- the pointwise Jensen / Cauchy-Schwarz bound
  have hpt : ∀ x : EuclideanSpace ℝ (Fin n),
      ‖convolution κ h (ContinuousLinearMap.lsmul ℝ ℝ) volume x‖ₑ ^ (2:ℝ)
        ≤ ∫⁻ t, ENNReal.ofReal (κ t) * ‖h (x - t)‖ₑ ^ (2:ℝ) ∂volume := by
    intro x
    have hum : AEMeasurable (fun t => ENNReal.ofReal (Real.sqrt (κ t)))
        (volume : Measure (EuclideanSpace ℝ (Fin n))) :=
      (ENNReal.measurable_ofReal.comp (Real.continuous_sqrt.measurable.comp hκm)).aemeasurable
    have hwm : AEMeasurable
        (fun t => ENNReal.ofReal (Real.sqrt (κ t)) * ‖h (x - t)‖ₑ)
        (volume : Measure (EuclideanSpace ℝ (Fin n))) := hum.mul (hhx x)
    have husq : ∀ t, ENNReal.ofReal (Real.sqrt (κ t)) ^ (2:ℝ) = ENNReal.ofReal (κ t) := by
      intro t
      rw [h2, ← ENNReal.ofReal_mul (Real.sqrt_nonneg _), Real.mul_self_sqrt (hκ0 t)]
    -- step a: the enorm of the convolution integral
    have ha : ‖convolution κ h (ContinuousLinearMap.lsmul ℝ ℝ) volume x‖ₑ
        ≤ ∫⁻ t, ENNReal.ofReal (κ t) * ‖h (x - t)‖ₑ ∂volume := by
      rw [convolution_def]
      refine (enorm_integral_le_lintegral_enorm _).trans (le_of_eq (lintegral_congr fun t => ?_))
      rw [ContinuousLinearMap.lsmul_apply, enorm_smul, Real.enorm_eq_ofReal (hκ0 t)]
    -- step b: Cauchy-Schwarz against the probability density
    have hb : ∫⁻ t, ENNReal.ofReal (κ t) * ‖h (x - t)‖ₑ ∂volume
        ≤ (∫⁻ t, ENNReal.ofReal (κ t) * ‖h (x - t)‖ₑ ^ (2:ℝ) ∂volume) ^ ((1:ℝ)/2) := by
      have hCS := ENNReal.lintegral_mul_le_Lp_mul_Lq
        (volume : Measure (EuclideanSpace ℝ (Fin n))) Real.HolderConjugate.two_two hum hwm
      have e1 : ∫⁻ t, ((fun t => ENNReal.ofReal (Real.sqrt (κ t))) *
            (fun t => ENNReal.ofReal (Real.sqrt (κ t)) * ‖h (x - t)‖ₑ)) t ∂volume
          = ∫⁻ t, ENNReal.ofReal (κ t) * ‖h (x - t)‖ₑ ∂volume := by
        refine lintegral_congr fun t => ?_
        simp only [Pi.mul_apply]
        rw [← mul_assoc, ← h2, husq t]
      have e2 : ∫⁻ t, ENNReal.ofReal (Real.sqrt (κ t)) ^ (2:ℝ) ∂volume = 1 := by
        rw [← hL1]
        exact lintegral_congr fun t => husq t
      have e3 : ∫⁻ t, (ENNReal.ofReal (Real.sqrt (κ t)) * ‖h (x - t)‖ₑ) ^ (2:ℝ) ∂volume
          = ∫⁻ t, ENNReal.ofReal (κ t) * ‖h (x - t)‖ₑ ^ (2:ℝ) ∂volume := by
        refine lintegral_congr fun t => ?_
        rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0:ℝ) ≤ 2), husq t]
      rw [e1, e2, e3] at hCS
      simpa using hCS
    calc ‖convolution κ h (ContinuousLinearMap.lsmul ℝ ℝ) volume x‖ₑ ^ (2:ℝ)
        ≤ ((∫⁻ t, ENNReal.ofReal (κ t) * ‖h (x - t)‖ₑ ^ (2:ℝ) ∂volume) ^ ((1:ℝ)/2)) ^ (2:ℝ) := by
          exact ENNReal.rpow_le_rpow (ha.trans hb) (by norm_num)
      _ = ∫⁻ t, ENNReal.ofReal (κ t) * ‖h (x - t)‖ₑ ^ (2:ℝ) ∂volume := by
          rw [← ENNReal.rpow_mul]
          norm_num
  -- the degenerate case where `h` is not square integrable
  by_cases hfin : ∫⁻ y, ‖h y‖ₑ ^ (2:ℝ) ∂(volume : Measure (EuclideanSpace ℝ (Fin n))) = ⊤
  · have htop : eLpNorm h 2 (volume : Measure (EuclideanSpace ℝ (Fin n))) = ⊤ := by
      rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)]
      simp only [ENNReal.toReal_ofNat, hfin]
      rw [ENNReal.top_rpow_of_pos (by norm_num)]
    rw [htop]
    exact le_top
  -- joint measurability for Tonelli
  have hjoint : AEMeasurable
      (Function.uncurry fun x t => ENNReal.ofReal (κ t) * ‖h (x - t)‖ₑ ^ (2:ℝ))
      ((volume : Measure (EuclideanSpace ℝ (Fin n))).prod volume) := by
    have hG : AEMeasurable
        (fun z : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
          ENNReal.ofReal (κ z.2) * ‖h z.1‖ₑ ^ (2:ℝ))
        ((volume : Measure (EuclideanSpace ℝ (Fin n))).prod volume) := by
      refine AEMeasurable.mul ?_ ?_
      · exact (ENNReal.measurable_ofReal.comp hκm).aemeasurable.comp_snd
      · exact (Measurable.pow_const (fun ⦃t⦄ a => a) (2:ℝ)).comp_aemeasurable hh.enorm.comp_fst
    exact hG.comp_quasiMeasurePreserving
      (measurePreserving_sub_prod volume volume).quasiMeasurePreserving
  have hmain : ∫⁻ x, ‖convolution κ h (ContinuousLinearMap.lsmul ℝ ℝ) volume x‖ₑ ^ (2:ℝ)
        ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))
      ≤ ∫⁻ y, ‖h y‖ₑ ^ (2:ℝ) ∂(volume : Measure (EuclideanSpace ℝ (Fin n))) := by
    calc ∫⁻ x, ‖convolution κ h (ContinuousLinearMap.lsmul ℝ ℝ) volume x‖ₑ ^ (2:ℝ) ∂volume
        ≤ ∫⁻ x, ∫⁻ t, ENNReal.ofReal (κ t) * ‖h (x - t)‖ₑ ^ (2:ℝ) ∂volume ∂volume :=
          lintegral_mono hpt
      _ = ∫⁻ t, ∫⁻ x, ENNReal.ofReal (κ t) * ‖h (x - t)‖ₑ ^ (2:ℝ) ∂volume ∂volume :=
          lintegral_lintegral_swap hjoint
      _ = ∫⁻ t, ENNReal.ofReal (κ t) *
            (∫⁻ y, ‖h y‖ₑ ^ (2:ℝ) ∂volume) ∂volume := by
          refine lintegral_congr fun t => ?_
          rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
            lintegral_sub_right_eq_self (fun y => ‖h y‖ₑ ^ (2:ℝ)) t]
      _ = (∫⁻ t, ENNReal.ofReal (κ t) ∂volume) * ∫⁻ y, ‖h y‖ₑ ^ (2:ℝ) ∂volume :=
          lintegral_mul_const' _ _ hfin
      _ = ∫⁻ y, ‖h y‖ₑ ^ (2:ℝ) ∂volume := by rw [hL1, one_mul]
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num),
    eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)]
  simp only [ENNReal.toReal_ofNat]
  exact ENNReal.rpow_le_rpow hmain (by norm_num)
