module

public import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
public import GaussianRiesz.SubordinationWeightIntegral
public import GaussianRiesz.PVTruncatedSliceEnormBound

@[expose] public section
open MeasureTheory
theorem PVTruncatedTimeSliceFinite {n : ℕ} (j : Fin n) (x : EuclideanSpace ℝ (Fin n))
    (ε : ℝ) (hε : 0 < ε) :
    ∫⁻ s in Set.Ioi (0 : ℝ), ENNReal.ofReal ((Real.sqrt s)⁻¹)
        * ∫⁻ y in {y : EuclideanSpace ℝ (Fin n) | ε < ‖x - y‖},
            ‖Real.sqrt 2 * Real.exp (-s) * (y j - Real.exp (-s) * x j) / (1 - Real.exp (-2 * s))
              * (Real.pi ^ (-(n : ℝ) / 2) * (1 - Real.exp (-2 * s)) ^ (-(n : ℝ) / 2)
                  * Real.exp (-‖Real.exp (-s) • x - y‖ ^ 2 / (1 - Real.exp (-2 * s))))‖ₑ < ⊤ := by
  -- the per-time-slice enorm bound, uniform in the slice
  have slicelint := PVTruncatedSliceEnormBound (n := n)
  have main : ∀ (D : ℝ → EuclideanSpace ℝ (Fin n) → ℝ),
      (∀ (s : ℝ) (y : EuclideanSpace ℝ (Fin n)), D s y =
        Real.sqrt 2 * Real.exp (-s) * (y j - Real.exp (-s) * x j) / (1 - Real.exp (-2 * s))
          * (Real.pi ^ (-(n : ℝ) / 2) * (1 - Real.exp (-2 * s)) ^ (-(n : ℝ) / 2)
              * Real.exp (-‖Real.exp (-s) • x - y‖ ^ 2 / (1 - Real.exp (-2 * s))))) →
      ∫⁻ s in Set.Ioi (0 : ℝ), ENNReal.ofReal ((Real.sqrt s)⁻¹)
          * ∫⁻ y in {y : EuclideanSpace ℝ (Fin n) | ε < ‖x - y‖}, ‖D s y‖ₑ < ⊤ := by
    intro D hD
    have hxn : (0:ℝ) ≤ ‖x‖ := norm_nonneg x
    set s₀ : ℝ := min 1 (ε / (2 * (1 + ‖x‖))) with hs₀def
    have hs₀0 : 0 < s₀ := by rw [hs₀def]; exact lt_min one_pos (by positivity)
    have hs₀1 : s₀ ≤ 1 := by rw [hs₀def]; exact min_le_left _ _
    -- STEP 6a: for small times the drift (1 - e^{-s})x cannot reach half the truncation radius
    have hdrift : ∀ s : ℝ, 0 < s → s ≤ s₀ → ‖x - Real.exp (-s) • x‖ ≤ ε / 2 := by
      intro s hs hss
      have h1 : x - Real.exp (-s) • x = (1 - Real.exp (-s)) • x := by rw [sub_smul, one_smul]
      have h2 : 1 - s ≤ Real.exp (-s) := by linarith [Real.add_one_le_exp (-s)]
      have h3 : 0 ≤ 1 - Real.exp (-s) := by
        have : Real.exp (-s) < 1 := by rw [Real.exp_lt_one_iff]; linarith
        linarith
      rw [h1, norm_smul, Real.norm_eq_abs, abs_of_nonneg h3]
      have h5 : s ≤ ε / (2 * (1 + ‖x‖)) := le_trans hss (by rw [hs₀def]; exact min_le_right _ _)
      have h6 : (0:ℝ) < 2 * (1 + ‖x‖) := by positivity
      have h7 : s * ‖x‖ ≤ ε / 2 := by
        refine (mul_le_mul_of_nonneg_right h5 hxn).trans ?_
        rw [div_mul_eq_mul_div, div_le_div_iff₀ h6 (by norm_num)]
        nlinarith [hε, hxn]
      calc (1 - Real.exp (-s)) * ‖x‖ ≤ s * ‖x‖ := by nlinarith
        _ ≤ ε / 2 := h7
    -- the two regime constants
    set K₁ : ℝ := 40 * Real.sqrt 2 * 4 ^ ((n : ℝ) / 2) / ε ^ 2 with hK₁def
    have hK₁0 : 0 ≤ K₁ := by rw [hK₁def]; positivity
    set σ₀ : ℝ := 1 - Real.exp (-2 * s₀) with hσ₀def
    have hσ₀0 : 0 < σ₀ := by
      rw [hσ₀def]
      have : Real.exp (-2 * s₀) < 1 := by rw [Real.exp_lt_one_iff]; linarith
      linarith
    set K₂ : ℝ := 3 * Real.sqrt 2 * 2 ^ ((n : ℝ) / 2) / σ₀ with hK₂def
    have hK₂0 : 0 ≤ K₂ := by rw [hK₂def]; positivity
    have hbd1 : ∀ s : ℝ, 0 < s → s ≤ s₀ →
        ∫⁻ y in {y : EuclideanSpace ℝ (Fin n) | ε < ‖x - y‖}, ‖D s y‖ₑ ≤ ENNReal.ofReal K₁ :=
      fun s hs hss => (slicelint j x ε hε s hs (D s) (hD s)).1 (hdrift s hs hss)
    have hbd2 : ∀ s : ℝ, s₀ ≤ s →
        ∫⁻ y in {y : EuclideanSpace ℝ (Fin n) | ε < ‖x - y‖}, ‖D s y‖ₑ
          ≤ ENNReal.ofReal (K₂ * Real.exp (-s)) := by
      intro s hss
      have hs : 0 < s := lt_of_lt_of_le hs₀0 hss
      refine ((slicelint j x ε hε s hs (D s) (hD s)).2).trans (ENNReal.ofReal_le_ofReal ?_)
      have hσs : σ₀ ≤ 1 - Real.exp (-2 * s) := by
        have := Real.exp_le_exp.2 (show -2 * s ≤ -2 * s₀ by linarith)
        rw [hσ₀def]; linarith
      have hrw : K₂ * Real.exp (-s)
          = 3 * Real.sqrt 2 * 2 ^ ((n : ℝ) / 2) * Real.exp (-s) / σ₀ := by rw [hK₂def]; ring
      rw [hrw]
      have hnum : (0:ℝ) ≤ 3 * Real.sqrt 2 * 2 ^ ((n : ℝ) / 2) * Real.exp (-s) := by positivity
      gcongr
    -- STEP 6b: the two integrable time weights
    have hw1 : ∫⁻ s in Set.Ioc (0:ℝ) s₀, ENNReal.ofReal ((Real.sqrt s)⁻¹) < ⊤ := by
      have hr : IntervalIntegrable (fun s : ℝ => s ^ (-(1:ℝ)/2)) volume 0 1 :=
        intervalIntegral.intervalIntegrable_rpow' (by norm_num)
      rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)] at hr
      have heq : Set.EqOn (fun s : ℝ => s ^ (-(1:ℝ)/2)) (fun s : ℝ => (Real.sqrt s)⁻¹)
          (Set.Ioc (0:ℝ) 1) := by
        intro s hs
        simp only
        rw [Real.sqrt_eq_rpow, show (-(1:ℝ)/2) = -(1/2 : ℝ) by ring, Real.rpow_neg hs.1.le]
      have hI : IntegrableOn (fun s : ℝ => (Real.sqrt s)⁻¹) (Set.Ioc (0:ℝ) s₀) volume :=
        (hr.congr_fun heq measurableSet_Ioc).mono_set (Set.Ioc_subset_Ioc_right hs₀1)
      have h2 := hI.2
      rw [hasFiniteIntegral_iff_enorm] at h2
      refine lt_of_le_of_lt (le_of_eq ?_) h2
      refine lintegral_congr fun s => ?_
      exact (Real.enorm_eq_ofReal (by positivity : (0:ℝ) ≤ (Real.sqrt s)⁻¹)).symm
    have hw2 : ∫⁻ s in Set.Ioi s₀, ENNReal.ofReal ((Real.sqrt s)⁻¹ * Real.exp (-s)) < ⊤ := by
      have hI := SubordinationWeightIntegral.1.mono_set (Set.Ioi_subset_Ioi hs₀0.le)
      have h2 := hI.2
      rw [hasFiniteIntegral_iff_enorm] at h2
      refine lt_of_le_of_lt (le_of_eq ?_) h2
      refine lintegral_congr fun s => ?_
      exact (Real.enorm_eq_ofReal
        (by positivity : (0:ℝ) ≤ (Real.sqrt s)⁻¹ * Real.exp (-s))).symm
    -- STEP 6c: split the time axis at s₀ and bound each piece
    have hdisj : Disjoint (Set.Ioc (0:ℝ) s₀) (Set.Ioi s₀) := by
      rw [Set.disjoint_left]
      intro a ha hb
      exact absurd (Set.mem_Ioi.1 hb) (not_lt.2 ha.2)
    rw [show Set.Ioi (0:ℝ) = Set.Ioc 0 s₀ ∪ Set.Ioi s₀ from (Set.Ioc_union_Ioi_eq_Ioi hs₀0.le).symm,
      lintegral_union measurableSet_Ioi hdisj]
    refine ENNReal.add_lt_top.2 ⟨?_, ?_⟩
    · calc ∫⁻ s in Set.Ioc (0:ℝ) s₀, ENNReal.ofReal ((Real.sqrt s)⁻¹)
              * ∫⁻ y in {y : EuclideanSpace ℝ (Fin n) | ε < ‖x - y‖}, ‖D s y‖ₑ
          ≤ ∫⁻ _s in Set.Ioc (0:ℝ) s₀, ENNReal.ofReal ((Real.sqrt _s)⁻¹) * ENNReal.ofReal K₁ := by
            refine lintegral_mono_ae ((ae_restrict_iff' measurableSet_Ioc).2 ?_)
            exact Filter.Eventually.of_forall fun s hs => mul_le_mul' le_rfl (hbd1 s hs.1 hs.2)
        _ = (∫⁻ s in Set.Ioc (0:ℝ) s₀, ENNReal.ofReal ((Real.sqrt s)⁻¹)) * ENNReal.ofReal K₁ :=
            lintegral_mul_const' _ _ ENNReal.ofReal_ne_top
        _ < ⊤ := ENNReal.mul_lt_top hw1 ENNReal.ofReal_lt_top
    · calc ∫⁻ s in Set.Ioi s₀, ENNReal.ofReal ((Real.sqrt s)⁻¹)
              * ∫⁻ y in {y : EuclideanSpace ℝ (Fin n) | ε < ‖x - y‖}, ‖D s y‖ₑ
          ≤ ∫⁻ s in Set.Ioi s₀, ENNReal.ofReal K₂
              * ENNReal.ofReal ((Real.sqrt s)⁻¹ * Real.exp (-s)) := by
            refine lintegral_mono_ae ((ae_restrict_iff' measurableSet_Ioi).2 ?_)
            refine Filter.Eventually.of_forall fun s hs => ?_
            refine le_trans (mul_le_mul' le_rfl (hbd2 s (le_of_lt (Set.mem_Ioi.1 hs))))
              (le_of_eq ?_)
            rw [← ENNReal.ofReal_mul (by positivity : (0:ℝ) ≤ (Real.sqrt s)⁻¹),
              ← ENNReal.ofReal_mul hK₂0]
            congr 1
            ring
        _ = ENNReal.ofReal K₂
              * ∫⁻ s in Set.Ioi s₀, ENNReal.ofReal ((Real.sqrt s)⁻¹ * Real.exp (-s)) :=
            lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
        _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hw2
  exact main (fun s y =>
    Real.sqrt 2 * Real.exp (-s) * (y j - Real.exp (-s) * x j) / (1 - Real.exp (-2 * s))
      * (Real.pi ^ (-(n : ℝ) / 2) * (1 - Real.exp (-2 * s)) ^ (-(n : ℝ) / 2)
          * Real.exp (-‖Real.exp (-s) • x - y‖ ^ 2 / (1 - Real.exp (-2 * s))))) (fun _ _ => rfl)
