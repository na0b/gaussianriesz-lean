import GaussianRiesz.GaussRieszKernelNearBounds
open MeasureTheory Metric
open scoped ENNReal
theorem GaussRieszKernelHormanderDyadicBound {n : ℕ} (j : Fin n) (R : ℝ) (hR : 1 ≤ R) :
    ∃ C : ℝ≥0∞, C ≠ 0 ∧ C ≠ ⊤ ∧
      ∀ (f : EuclideanSpace ℝ (Fin n) → ℝ) (Φ : ℝ≥0∞)
        (x z : EuclideanSpace ℝ (Fin n)) (ε : ℝ),
        ‖x‖ ≤ R → 0 < ε → ε ≤ 1 → ‖x - z‖ < ε / 2 →
        (∀ ρ : ℝ, 0 < ρ → ρ ≤ 2 →
            ∫⁻ y in closedBall x ρ, ‖f y‖ₑ ≤ Φ * volume (closedBall x ρ)) →
        ∫⁻ y in {y : EuclideanSpace ℝ (Fin n) | ε < ‖x - y‖ ∧ ‖x - y‖ ≤ 1},
            ‖GaussRieszKernel j x y - GaussRieszKernel j z y‖ₑ * ‖f y‖ₑ
          ≤ C * Φ := by
  have hdim : Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) = n := by
    simp
  obtain ⟨Ch, hCh0, -, hHorm⟩ := GaussRieszKernelNearBounds j R (by linarith)
  -- the unit-ball volume, opaque and finite
  obtain ⟨ω, hω0, hωtop, hωval⟩ :
      ∃ ω : ℝ≥0∞, ω ≠ 0 ∧ ω ≠ ⊤ ∧ ω = volume (ball (0 : EuclideanSpace ℝ (Fin n)) 1) := by
    refine ⟨volume (ball (0 : EuclideanSpace ℝ (Fin n)) 1), ?_, ?_, rfl⟩
    · exact (measure_ball_pos volume _ one_pos).ne'
    · exact (measure_ball_lt_top).ne
  refine ⟨ENNReal.ofReal (Ch * 2 ^ n) * ω, by positivity, by finiteness, ?_⟩
  intro f Φ x z ε hxR hε0 hε1 hxz hmax
  -- the dyadic cover of the annulus
  have hcover : {y : EuclideanSpace ℝ (Fin n) | ε < ‖x - y‖ ∧ ‖x - y‖ ≤ 1}
      = ⋃ k : ℕ, ({y : EuclideanSpace ℝ (Fin n) |
          2 ^ k * ε < ‖x - y‖ ∧ ‖x - y‖ ≤ 2 ^ (k + 1) * ε}
        ∩ {y : EuclideanSpace ℝ (Fin n) | ε < ‖x - y‖ ∧ ‖x - y‖ ≤ 1}) := by
    ext y
    simp only [Set.mem_iUnion, Set.mem_inter_iff, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨h1, h2⟩
      classical
      have hP : ∃ k : ℕ, ‖x - y‖ ≤ 2 ^ (k + 1) * ε := by
        obtain ⟨m, hm⟩ := exists_nat_gt (1 / ε)
        refine ⟨m, ?_⟩
        have h3 : (m : ℝ) ≤ 2 ^ m := by
          have := Nat.lt_two_pow_self (n := m)
          exact_mod_cast this.le
        have h4 : (1:ℝ) / ε < 2 ^ m := lt_of_lt_of_le hm h3
        rw [div_lt_iff₀ hε0] at h4
        have h5 : (2:ℝ) ^ m * ε ≤ 2 ^ (m + 1) * ε := by
          have h6 : (2:ℝ) ^ m ≤ 2 ^ (m + 1) := pow_le_pow_right₀ (by norm_num) (by omega)
          nlinarith [hε0]
        linarith
      refine ⟨Nat.find hP, ⟨?_, Nat.find_spec hP⟩, h1, h2⟩
      rcases Nat.eq_zero_or_pos (Nat.find hP) with hk | hk
      · rw [hk]; simpa using h1
      · obtain ⟨m, hm⟩ : ∃ m, Nat.find hP = m + 1 := ⟨Nat.find hP - 1, by omega⟩
        have hmin := Nat.find_min hP (m := m) (by omega)
        rw [not_le] at hmin
        rw [hm]
        exact hmin
    · rintro ⟨k, -, h1, h2⟩
      exact ⟨h1, h2⟩
  -- measurability of the annuli
  have hSm : ∀ a b : ℝ,
      MeasurableSet {y : EuclideanSpace ℝ (Fin n) | a < ‖x - y‖ ∧ ‖x - y‖ ≤ b} := by
    intro a b
    have hc : Continuous fun y : EuclideanSpace ℝ (Fin n) => ‖x - y‖ :=
      (continuous_const.sub continuous_id).norm
    have he : {y : EuclideanSpace ℝ (Fin n) | a < ‖x - y‖ ∧ ‖x - y‖ ≤ b}
        = (fun y : EuclideanSpace ℝ (Fin n) => ‖x - y‖) ⁻¹' Set.Ioc a b := rfl
    rw [he]
    exact hc.measurable measurableSet_Ioc
  -- the per-annulus bound
  have hk : ∀ k : ℕ,
      ∫⁻ y in ({y : EuclideanSpace ℝ (Fin n) |
            2 ^ k * ε < ‖x - y‖ ∧ ‖x - y‖ ≤ 2 ^ (k + 1) * ε}
          ∩ {y : EuclideanSpace ℝ (Fin n) | ε < ‖x - y‖ ∧ ‖x - y‖ ≤ 1}),
          ‖GaussRieszKernel j x y - GaussRieszKernel j z y‖ₑ * ‖f y‖ₑ
        ≤ (ENNReal.ofReal (Ch * 2 ^ n) * ω * Φ) * ((1:ℝ≥0∞) / 2) ^ (k + 1) := by
    intro k
    have hkε : (0:ℝ) < 2 ^ k * ε := by positivity
    have hrk0 : (0:ℝ) < 2 ^ (k + 1) * ε := by positivity
    rcases le_or_gt (2 ^ (k + 1) * ε) 2 with hcase | hcase
    · -- the live range: apply the Hoermander bound and the maximal-function hypothesis
      have hpt : ∀ y ∈ ({y : EuclideanSpace ℝ (Fin n) |
            2 ^ k * ε < ‖x - y‖ ∧ ‖x - y‖ ≤ 2 ^ (k + 1) * ε}
          ∩ {y : EuclideanSpace ℝ (Fin n) | ε < ‖x - y‖ ∧ ‖x - y‖ ≤ 1}),
          ‖GaussRieszKernel j x y - GaussRieszKernel j z y‖ₑ * ‖f y‖ₑ
            ≤ ENNReal.ofReal (Ch * (ε / 2) / (2 ^ k * ε) ^ (n + 1)) * ‖f y‖ₑ := by
        intro y hy
        obtain ⟨⟨hy1, hy2⟩, hy3, hy4⟩ := hy
        refine mul_le_mul' ?_ le_rfl
        have hH := hHorm x y z hxR (by linarith) hy4 (by linarith)
        have hmono : Ch * ‖x - z‖ / ‖x - y‖ ^ (n + 1)
            ≤ Ch * (ε / 2) / (2 ^ k * ε) ^ (n + 1) := by
          refine div_le_div₀ (by positivity) (by nlinarith [hCh0]) (by positivity) ?_
          exact pow_le_pow_left₀ hkε.le hy1.le (n + 1)
        rw [Real.enorm_eq_ofReal_abs]
        exact ENNReal.ofReal_le_ofReal (le_trans hH hmono)
      have hsub : ({y : EuclideanSpace ℝ (Fin n) |
            2 ^ k * ε < ‖x - y‖ ∧ ‖x - y‖ ≤ 2 ^ (k + 1) * ε}
          ∩ {y : EuclideanSpace ℝ (Fin n) | ε < ‖x - y‖ ∧ ‖x - y‖ ≤ 1})
          ⊆ closedBall x (2 ^ (k + 1) * ε) := by
        intro y hy
        simp only [mem_closedBall, dist_eq_norm]
        rw [← norm_sub_rev]
        exact hy.1.2
      calc ∫⁻ y in ({y : EuclideanSpace ℝ (Fin n) |
              2 ^ k * ε < ‖x - y‖ ∧ ‖x - y‖ ≤ 2 ^ (k + 1) * ε}
            ∩ {y : EuclideanSpace ℝ (Fin n) | ε < ‖x - y‖ ∧ ‖x - y‖ ≤ 1}),
            ‖GaussRieszKernel j x y - GaussRieszKernel j z y‖ₑ * ‖f y‖ₑ
          ≤ ∫⁻ y in ({y : EuclideanSpace ℝ (Fin n) |
                2 ^ k * ε < ‖x - y‖ ∧ ‖x - y‖ ≤ 2 ^ (k + 1) * ε}
              ∩ {y : EuclideanSpace ℝ (Fin n) | ε < ‖x - y‖ ∧ ‖x - y‖ ≤ 1}),
              ENNReal.ofReal (Ch * (ε / 2) / (2 ^ k * ε) ^ (n + 1)) * ‖f y‖ₑ :=
            lintegral_mono_ae (by
              filter_upwards [ae_restrict_mem ((hSm _ _).inter (hSm _ _))] with y hy
              exact hpt y hy)
        _ = ENNReal.ofReal (Ch * (ε / 2) / (2 ^ k * ε) ^ (n + 1))
              * ∫⁻ y in ({y : EuclideanSpace ℝ (Fin n) |
                  2 ^ k * ε < ‖x - y‖ ∧ ‖x - y‖ ≤ 2 ^ (k + 1) * ε}
                ∩ {y : EuclideanSpace ℝ (Fin n) | ε < ‖x - y‖ ∧ ‖x - y‖ ≤ 1}),
                ‖f y‖ₑ := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
        _ ≤ ENNReal.ofReal (Ch * (ε / 2) / (2 ^ k * ε) ^ (n + 1))
              * ∫⁻ y in closedBall x (2 ^ (k + 1) * ε), ‖f y‖ₑ :=
            mul_le_mul' le_rfl (lintegral_mono_set hsub)
        _ ≤ ENNReal.ofReal (Ch * (ε / 2) / (2 ^ k * ε) ^ (n + 1))
              * (Φ * volume (closedBall x (2 ^ (k + 1) * ε))) :=
            mul_le_mul' le_rfl (hmax _ hrk0 hcase)
        _ = (ENNReal.ofReal (Ch * 2 ^ n) * ω * Φ) * ((1:ℝ≥0∞) / 2) ^ (k + 1) := by
            rw [Measure.addHaar_closedBall volume x hrk0.le, hdim, ← hωval]
            have hid : ENNReal.ofReal (Ch * (ε / 2) / (2 ^ k * ε) ^ (n + 1))
                  * ENNReal.ofReal ((2 ^ (k + 1) * ε) ^ n)
                = ENNReal.ofReal (Ch * 2 ^ n) * ((1:ℝ≥0∞) / 2) ^ (k + 1) := by
              have hεne : ε ≠ 0 := ne_of_gt hε0
              have h2k : (2:ℝ) ^ k ≠ 0 := by positivity
              have hidr : Ch * (ε / 2) / (2 ^ k * ε) ^ (n + 1) * (2 ^ (k + 1) * ε) ^ n
                  = Ch * 2 ^ n * ((1:ℝ) / 2) ^ (k + 1) := by
                rw [div_pow, one_pow]
                field_simp
                ring
              rw [← ENNReal.ofReal_mul (by positivity), hidr,
                ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow (by norm_num)]
              congr 2
              rw [show ((1:ℝ)/2) = (2:ℝ)⁻¹ from by norm_num,
                ENNReal.ofReal_inv_of_pos (by norm_num)]
              norm_num
            calc ENNReal.ofReal (Ch * (ε / 2) / (2 ^ k * ε) ^ (n + 1))
                  * (Φ * (ENNReal.ofReal ((2 ^ (k + 1) * ε) ^ n) * ω))
                = (ENNReal.ofReal (Ch * (ε / 2) / (2 ^ k * ε) ^ (n + 1))
                    * ENNReal.ofReal ((2 ^ (k + 1) * ε) ^ n)) * (ω * Φ) := by ring
              _ = (ENNReal.ofReal (Ch * 2 ^ n) * ((1:ℝ≥0∞) / 2) ^ (k + 1)) * (ω * Φ) := by
                  rw [hid]
              _ = (ENNReal.ofReal (Ch * 2 ^ n) * ω * Φ) * ((1:ℝ≥0∞) / 2) ^ (k + 1) := by ring
    · -- out of range: the annulus misses the unit-radius cap, so the set is empty
      have hempty : ({y : EuclideanSpace ℝ (Fin n) |
            2 ^ k * ε < ‖x - y‖ ∧ ‖x - y‖ ≤ 2 ^ (k + 1) * ε}
          ∩ {y : EuclideanSpace ℝ (Fin n) | ε < ‖x - y‖ ∧ ‖x - y‖ ≤ 1}) = ∅ := by
        ext y
        simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false,
          not_and]
        intro hy hy3 hy4
        have hpow : (2:ℝ) ^ (k + 1) = 2 * 2 ^ k := by ring
        rw [hpow] at hcase
        linarith [hy.1, hy4, hcase]
      rw [hempty]
      simp
  -- sum the dyadic bounds
  rw [hcover]
  refine le_trans (lintegral_iUnion_le _ _) ?_
  refine le_trans (ENNReal.tsum_le_tsum hk) ?_
  have hhalf : (1:ℝ≥0∞) - 1 / 2 = 1 / 2 := by
    refine ENNReal.sub_eq_of_eq_add (by finiteness) ?_
    rw [ENNReal.div_add_div_same]
    rw [show (1:ℝ≥0∞) + 1 = 2 from by norm_num,
      ENNReal.div_self (by norm_num) (by finiteness)]
  rw [ENNReal.tsum_mul_left, ENNReal.tsum_geometric_add_one, hhalf]
  rw [show ((1:ℝ≥0∞) / 2) * ((1:ℝ≥0∞) / 2)⁻¹ = 1 from
    ENNReal.mul_inv_cancel (by norm_num) (by finiteness)]
  simp
