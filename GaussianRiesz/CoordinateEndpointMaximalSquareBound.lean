module

public import GaussianRiesz.LocalMaximalWeakL2
public import GaussianRiesz.CoordinateEndpointBound
public import GaussianRiesz.GaussLebesgueBallComparison

@[expose] public section
open MeasureTheory Metric
open scoped ENNReal
theorem CoordinateEndpointMaximalSquareBound {n : ℕ}
    (T : Lp ℝ 1 (GaussMeasure n) →ₗ[ℝ]
      (EuclideanSpace ℝ (Fin n) →ₘ[GaussMeasure n] EuclideanSpace ℝ (Fin n)))
    (hext : ∀ v : Lp ℝ 2 (GaussMeasure n),
      T (ToL1 v) = (RieszTransform v : EuclideanSpace ℝ (Fin n)
        →ₘ[GaussMeasure n] EuclideanSpace ℝ (Fin n)))
    (hT : ∀ (f : Lp ℝ 1 (GaussMeasure n)) (t : ℝ), 0 < t →
      ENNReal.ofReal t * GaussMeasure n {x | t < ‖T f x‖} ≤ ENNReal.ofReal (2 * ‖f‖))
    (j : Fin n) (R : ℝ) (f : Lp ℝ 1 (GaussMeasure n)) (s : ℝ≥0∞) (hs : s ≠ 0) :
    GaussMeasure n {x : EuclideanSpace ℝ (Fin n) | s <
        (LocalMaximalFunction
          (Set.indicator (closedBall (0 : EuclideanSpace ℝ (Fin n)) (R + 2))
            (fun y => Real.sqrt
              |(T f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) y j|)) x) ^ 2}
      ≤ ENNReal.ofReal (32 * 4 ^ n * Real.exp ((R + 2) ^ 2))
          * ENNReal.ofReal (∫ y, |(f : EuclideanSpace ℝ (Fin n) → ℝ) y| ∂(GaussMeasure n))
          / s := by
  classical
  set u : EuclideanSpace ℝ (Fin n) → ℝ :=
    Set.indicator (closedBall (0 : EuclideanSpace ℝ (Fin n)) (R + 2))
      (fun y => Real.sqrt
        |(T f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) y j|) with hudef
  set N : ℝ := ∫ y, |(f : EuclideanSpace ℝ (Fin n) → ℝ) y| ∂(GaussMeasure n) with hNdef
  have hN0 : 0 ≤ N := integral_nonneg fun y => abs_nonneg _
  have hfnorm : ‖f‖ = N := by
    rw [L1.norm_eq_integral_norm, hNdef]
    simp [Real.norm_eq_abs]
  -- Step 1 of the owner's `.tex`, for `u`: the canonical representative is measurable
  have hsm : StronglyMeasurable (T f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) :=
    AEEqFun.stronglyMeasurable _
  have hcc : Continuous (fun v : EuclideanSpace ℝ (Fin n) => Real.sqrt |v j|) := by fun_prop
  have humeas : Measurable u := by
    rw [hudef]
    exact (hcc.measurable.comp hsm.measurable).indicator measurableSet_closedBall
  have hunn : ∀ y, 0 ≤ u y := fun y => by
    rw [hudef]
    by_cases hy : y ∈ closedBall (0 : EuclideanSpace ℝ (Fin n)) (R + 2)
    · rw [Set.indicator_of_mem hy]; exact Real.sqrt_nonneg _
    · rw [Set.indicator_of_notMem hy]
  have huzero : ∀ y, y ∉ closedBall (0 : EuclideanSpace ℝ (Fin n)) (R + 2) → u y = 0 :=
    fun y hy => by rw [hudef]; exact Set.indicator_of_notMem hy _
  -- the three constants, kept opaque
  obtain ⟨p, hp0, hpdef⟩ : ∃ p : ℝ, 0 < p ∧ p = Real.pi ^ (-(n : ℝ) / 2) :=
    ⟨_, Real.rpow_pos_of_pos Real.pi_pos _, rfl⟩
  obtain ⟨q, hq0, hqdef⟩ : ∃ q : ℝ, 0 < q ∧ q = Real.pi ^ ((n : ℝ) / 2) :=
    ⟨_, Real.rpow_pos_of_pos Real.pi_pos _, rfl⟩
  obtain ⟨a, ha0, hadef⟩ : ∃ a : ℝ, 0 < a ∧
      a = Real.pi ^ (-(n : ℝ) / 2) * Real.exp (-(R + 2) ^ 2) :=
    ⟨_, by positivity, rfl⟩
  have hpq : p * q = 1 := by
    rw [hpdef, hqdef, show (-(n : ℝ) / 2) = -((n : ℝ) / 2) from by ring,
      Real.rpow_neg Real.pi_pos.le]
    exact inv_mul_cancel₀ (Real.rpow_pos_of_pos Real.pi_pos _).ne'
  have haq : a * (q * Real.exp ((R + 2) ^ 2)) = 1 := by
    have hexpq : Real.exp (-(R + 2) ^ 2) * Real.exp ((R + 2) ^ 2) = 1 := by
      rw [← Real.exp_add]; simp
    calc a * (q * Real.exp ((R + 2) ^ 2))
        = (p * q) * (Real.exp (-(R + 2) ^ 2) * Real.exp ((R + 2) ^ 2)) := by
          rw [hadef, hpdef]; ring
      _ = 1 := by rw [hpq, hexpq, mul_one]
  -- display (5) of the owner's `.tex`: the UNIFORM bound on the weak-L² quantity
  have hA : (⨆ σ ∈ Set.Ioi (0 : ℝ≥0∞),
        σ ^ 2 * volume {y : EuclideanSpace ℝ (Fin n) | σ < ‖u y‖ₑ})
      ≤ ENNReal.ofReal (2 * (q * Real.exp ((R + 2) ^ 2)) * N) := by
    refine iSup₂_le fun σ hσ => ?_
    rcases eq_or_ne σ ⊤ with hσt | hσt
    · have hemp : {y : EuclideanSpace ℝ (Fin n) | σ < ‖u y‖ₑ} = ∅ := by
        ext y
        simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_lt, hσt]
        exact le_top
      rw [hemp, measure_empty, mul_zero]
      exact zero_le
    obtain ⟨σ₀, hσ₀0, hσ₀⟩ : ∃ σ₀ : ℝ, 0 < σ₀ ∧ ENNReal.ofReal σ₀ = σ :=
      ⟨σ.toReal, ENNReal.toReal_pos (ne_of_gt hσ) hσt, ENNReal.ofReal_toReal hσt⟩
    have hEsub : {y : EuclideanSpace ℝ (Fin n) | σ < ‖u y‖ₑ}
        ⊆ closedBall (0 : EuclideanSpace ℝ (Fin n)) (R + 2) := by
      intro y hy
      by_contra hout
      rw [Set.mem_ofPred_eq, huzero y hout] at hy
      simp at hy
    have hEmeas : MeasurableSet {y : EuclideanSpace ℝ (Fin n) | σ < ‖u y‖ₑ} :=
      measurableSet_lt measurable_const humeas.enorm
    have hEsub2 : {y : EuclideanSpace ℝ (Fin n) | σ < ‖u y‖ₑ}
        ⊆ {y : EuclideanSpace ℝ (Fin n) | σ₀ ^ 2 <
            |(T f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) y j|} := by
      intro y hy
      have h1 : σ < ‖u y‖ₑ := hy
      rw [Real.enorm_eq_ofReal_abs, abs_of_nonneg (hunn y), ← hσ₀,
        ENNReal.ofReal_lt_ofReal_iff_of_nonneg hσ₀0.le] at h1
      rw [hudef, Set.indicator_of_mem (hEsub hy)] at h1
      have h2 := Real.sq_sqrt (abs_nonneg
        ((T f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) y j))
      show σ₀ ^ 2 < _
      nlinarith
    have hcl2 : ENNReal.ofReal a * volume {y : EuclideanSpace ℝ (Fin n) | σ < ‖u y‖ₑ}
        ≤ GaussMeasure n {y : EuclideanSpace ℝ (Fin n) | σ < ‖u y‖ₑ} := by
      rw [hadef]
      exact (GaussLebesgueBallComparison (n := n)).2.1 (R + 2) _ hEmeas hEsub
    have hceb := CoordinateEndpointBound T hext hT f j (σ₀ ^ 2) (by positivity)
    have hcancel : ENNReal.ofReal a
          * (σ ^ 2 * volume {y : EuclideanSpace ℝ (Fin n) | σ < ‖u y‖ₑ})
        ≤ ENNReal.ofReal a * ENNReal.ofReal (2 * (q * Real.exp ((R + 2) ^ 2)) * N) := by
      calc ENNReal.ofReal a
            * (σ ^ 2 * volume {y : EuclideanSpace ℝ (Fin n) | σ < ‖u y‖ₑ})
          = σ ^ 2 * (ENNReal.ofReal a
              * volume {y : EuclideanSpace ℝ (Fin n) | σ < ‖u y‖ₑ}) := by ring
        _ ≤ σ ^ 2 * GaussMeasure n {y : EuclideanSpace ℝ (Fin n) | σ < ‖u y‖ₑ} :=
            mul_le_mul' le_rfl hcl2
        _ ≤ σ ^ 2 * GaussMeasure n {y : EuclideanSpace ℝ (Fin n) | σ₀ ^ 2 <
              |(T f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) y j|} :=
            mul_le_mul' le_rfl (measure_mono hEsub2)
        _ = ENNReal.ofReal (σ₀ ^ 2) * GaussMeasure n {y : EuclideanSpace ℝ (Fin n) | σ₀ ^ 2 <
              |(T f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) y j|} := by
            rw [← hσ₀, ← ENNReal.ofReal_pow hσ₀0.le]
        _ ≤ ENNReal.ofReal (2 * ‖f‖) := hceb
        _ = ENNReal.ofReal a
              * ENNReal.ofReal (2 * (q * Real.exp ((R + 2) ^ 2)) * N) := by
            rw [← ENNReal.ofReal_mul ha0.le, hfnorm]
            congr 1
            calc 2 * N = 2 * N * (a * (q * Real.exp ((R + 2) ^ 2))) := by rw [haq, mul_one]
              _ = a * (2 * (q * Real.exp ((R + 2) ^ 2)) * N) := by ring
    exact (ENNReal.mul_le_mul_iff_right
        (by simp [ENNReal.ofReal_eq_zero, not_le, ha0]) ENNReal.ofReal_ne_top).1 hcancel
  -- the threshold `s = ⊤` case
  rcases eq_or_ne s ⊤ with hst | hst
  · have hemp : {x : EuclideanSpace ℝ (Fin n) | s < (LocalMaximalFunction u x) ^ 2} = ∅ := by
      ext x
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_lt, hst]
      exact le_top
    rw [hemp, measure_empty]
    exact zero_le
  -- Step 4: the square root of the level, and the weak-L² bound
  obtain ⟨s₀, hs₀0, hs₀⟩ : ∃ s₀ : ℝ, 0 < s₀ ∧ ENNReal.ofReal s₀ = s :=
    ⟨s.toReal, ENNReal.toReal_pos hs hst, ENNReal.ofReal_toReal hst⟩
  obtain ⟨L, hL0, hLsq⟩ : ∃ L : ℝ≥0∞, L ≠ 0 ∧ L ^ 2 = s := by
    refine ⟨ENNReal.ofReal (Real.sqrt s₀), ?_, ?_⟩
    · simp [ENNReal.ofReal_eq_zero, not_le, Real.sqrt_pos, hs₀0]
    · rw [← ENNReal.ofReal_pow (Real.sqrt_nonneg _), Real.sq_sqrt hs₀0.le, hs₀]
  have hsubset : {x : EuclideanSpace ℝ (Fin n) | s < (LocalMaximalFunction u x) ^ 2}
      ⊆ {x : EuclideanSpace ℝ (Fin n) | L < LocalMaximalFunction u x} := by
    intro x hx
    by_contra hnot
    rw [Set.mem_ofPred_eq, not_lt] at hnot
    have : (LocalMaximalFunction u x) ^ 2 ≤ s := by
      rw [← hLsq, pow_two, pow_two]; exact mul_le_mul' hnot hnot
    exact absurd hx (not_lt.2 this)
  calc GaussMeasure n {x : EuclideanSpace ℝ (Fin n) | s < (LocalMaximalFunction u x) ^ 2}
      ≤ GaussMeasure n {x : EuclideanSpace ℝ (Fin n) | L < LocalMaximalFunction u x} :=
        measure_mono hsubset
    _ ≤ ENNReal.ofReal p
          * volume {x : EuclideanSpace ℝ (Fin n) | L < LocalMaximalFunction u x} := by
        rw [hpdef]; exact (GaussLebesgueBallComparison (n := n)).1 _
    _ ≤ ENNReal.ofReal p * (16 * 4 ^ n * (⨆ σ ∈ Set.Ioi (0 : ℝ≥0∞),
            σ ^ 2 * volume {y : EuclideanSpace ℝ (Fin n) | σ < ‖u y‖ₑ}) / L ^ 2) :=
        mul_le_mul' le_rfl (LocalMaximalWeakL2 u humeas.aemeasurable L hL0)
    _ ≤ ENNReal.ofReal p * (16 * 4 ^ n
            * ENNReal.ofReal (2 * (q * Real.exp ((R + 2) ^ 2)) * N) / s) := by
        rw [hLsq]
        exact mul_le_mul' le_rfl (ENNReal.div_le_div_right (mul_le_mul' le_rfl hA) s)
    _ = ENNReal.ofReal (32 * 4 ^ n * Real.exp ((R + 2) ^ 2)) * ENNReal.ofReal N / s := by
        have hreal : p * (16 * 4 ^ n * (2 * (q * Real.exp ((R + 2) ^ 2)) * N))
            = 32 * 4 ^ n * Real.exp ((R + 2) ^ 2) * N := by
          calc p * (16 * 4 ^ n * (2 * (q * Real.exp ((R + 2) ^ 2)) * N))
              = 32 * 4 ^ n * Real.exp ((R + 2) ^ 2) * N * (p * q) := by ring
            _ = 32 * 4 ^ n * Real.exp ((R + 2) ^ 2) * N := by rw [hpq, mul_one]
        rw [← mul_div_assoc, show (16 : ℝ≥0∞) * 4 ^ n = ENNReal.ofReal (16 * 4 ^ n) from by
            rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_pow (by norm_num)]
            norm_num,
          ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul hp0.le,
          ← ENNReal.ofReal_mul (by positivity), hreal]
