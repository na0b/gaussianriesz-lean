module

public import GaussianRiesz.GaussRieszCotlarLocal
public import GaussianRiesz.LocalMaximalWeakL2
public import GaussianRiesz.LocalMaximalWeakType
public import GaussianRiesz.CoordinateEndpointMaximalSquareBound
public import GaussianRiesz.GaussIsProb

@[expose] public section
open MeasureTheory Metric
open scoped ENNReal
theorem GaussMaximalTruncationLocal {n : ℕ}
    (T : Lp ℝ 1 (GaussMeasure n) →ₗ[ℝ]
      (EuclideanSpace ℝ (Fin n) →ₘ[GaussMeasure n] EuclideanSpace ℝ (Fin n)))
    (hext : ∀ v : Lp ℝ 2 (GaussMeasure n),
      T (ToL1 v) = (RieszTransform v : EuclideanSpace ℝ (Fin n)
        →ₘ[GaussMeasure n] EuclideanSpace ℝ (Fin n)))
    (hT : ∀ (f : Lp ℝ 1 (GaussMeasure n)) (t : ℝ), 0 < t →
      ENNReal.ofReal t * GaussMeasure n {x | t < ‖T f x‖} ≤ ENNReal.ofReal (2 * ‖f‖))
    (j : Fin n) (R : ℝ) (hR : 1 ≤ R) :
    ∃ C : ℝ≥0∞, C ≠ 0 ∧ C ≠ ⊤ ∧
      ∀ (f : Lp ℝ 1 (GaussMeasure n)) (t : ℝ≥0∞), t ≠ 0 →
        GaussMeasure n {x : EuclideanSpace ℝ (Fin n) | ‖x‖ ≤ R ∧ t <
            ⨆ ε ∈ Set.Ioi (0 : ℝ), ENNReal.ofReal
              |∫ y in {y : EuclideanSpace ℝ (Fin n) | ε < ‖x - y‖},
                GaussRieszKernel j x y * (f : EuclideanSpace ℝ (Fin n) → ℝ) y|}
          ≤ C * ENNReal.ofReal
              (∫ y, |(f : EuclideanSpace ℝ (Fin n) → ℝ) y| ∂(GaussMeasure n)) / t := by
  classical
  have hn : 0 < n := Fin.pos j
  have : Nonempty (Fin n) := ⟨j⟩
  -- STEP 0: the Cotlar constant, and the single constant of the statement
  obtain ⟨C0, hC00, hC0t, hC0⟩ := GaussRieszCotlarLocal T hext hT j R hR
  obtain ⟨p, hp0, hpdef⟩ : ∃ p : ℝ, 0 < p ∧ p = Real.pi ^ (-(n : ℝ) / 2) :=
    ⟨_, Real.rpow_pos_of_pos Real.pi_pos _, rfl⟩
  obtain ⟨q, hq0, hqdef⟩ : ∃ q : ℝ, 0 < q ∧ q = Real.pi ^ ((n : ℝ) / 2) :=
    ⟨_, Real.rpow_pos_of_pos Real.pi_pos _, rfl⟩
  obtain ⟨a, ha0, hadef⟩ : ∃ a : ℝ, 0 < a ∧
      a = Real.pi ^ (-(n : ℝ) / 2) * Real.exp (-(R + 2) ^ 2) := ⟨_, by positivity, rfl⟩
  have hpq : p * q = 1 := by
    rw [hpdef, hqdef, show (-(n : ℝ) / 2) = -((n : ℝ) / 2) from by ring,
      Real.rpow_neg Real.pi_pos.le]
    exact inv_mul_cancel₀ (Real.rpow_pos_of_pos Real.pi_pos _).ne'
  have haq : (q * Real.exp ((R + 2) ^ 2)) * a = 1 := by
    have hexpq : Real.exp (-(R + 2) ^ 2) * Real.exp ((R + 2) ^ 2) = 1 := by
      rw [← Real.exp_add]; simp
    calc (q * Real.exp ((R + 2) ^ 2)) * a
        = (p * q) * (Real.exp (-(R + 2) ^ 2) * Real.exp ((R + 2) ^ 2)) := by
          rw [hadef, hpdef]; ring
      _ = 1 := by rw [hpq, hexpq, mul_one]
  obtain ⟨D, hDne, hDdef⟩ : ∃ D : ℝ≥0∞, D ≠ ⊤ ∧
      D = ENNReal.ofReal (4 ^ n * Real.exp ((R + 2) ^ 2))
          + ENNReal.ofReal (32 * 4 ^ n * Real.exp ((R + 2) ^ 2)) + 1 := by
    refine ⟨_, ?_, rfl⟩
    rw [ENNReal.add_ne_top, ENNReal.add_ne_top]
    exact ⟨⟨ENNReal.ofReal_ne_top, ENNReal.ofReal_ne_top⟩, ENNReal.one_ne_top⟩
  have hD1 : (1 : ℝ≥0∞) ≤ D := by rw [hDdef]; exact le_add_self
  have hD0 : D ≠ 0 := by
    intro h
    rw [h] at hD1
    exact absurd hD1 (by norm_num)
  have h3C00 : 3 * C0 ≠ 0 := mul_ne_zero (by norm_num) hC00
  have h3C0t : 3 * C0 ≠ ⊤ := ENNReal.mul_ne_top (by norm_num) hC0t
  refine ⟨3 * C0 * D, mul_ne_zero h3C00 hD0, ENNReal.mul_ne_top h3C0t hDne, ?_⟩
  intro f t ht
  set F : EuclideanSpace ℝ (Fin n) → ℝ := (f : EuclideanSpace ℝ (Fin n) → ℝ) with hFdef
  set N : ℝ≥0∞ := ENNReal.ofReal (∫ y, |F y| ∂(GaussMeasure n)) with hNdef
  set w : EuclideanSpace ℝ (Fin n) → ℝ :=
    Set.indicator (closedBall (0 : EuclideanSpace ℝ (Fin n)) (R + 2)) F with hwdef
  set u : EuclideanSpace ℝ (Fin n) → ℝ :=
    Set.indicator (closedBall (0 : EuclideanSpace ℝ (Fin n)) (R + 2))
      (fun y => Real.sqrt
        |(T f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) y j|) with hudef
  obtain ⟨s, hs0, hst⟩ : ∃ s : ℝ≥0∞, s ≠ 0 ∧ 3 * C0 * s = t := by
    refine ⟨t / (3 * C0), ?_, ENNReal.mul_div_cancel' (fun h => absurd h h3C00)
      (fun h => absurd h h3C0t)⟩
    simp [ENNReal.div_eq_zero_iff, ht, h3C0t]
  -- STEP 1: measurability of the two inputs
  have hFmeas : Measurable F := by
    rw [hFdef]
    exact (AEEqFun.stronglyMeasurable
      (f : EuclideanSpace ℝ (Fin n) →ₘ[GaussMeasure n] ℝ)).measurable
  have hwmeas : AEMeasurable w (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
    rw [hwdef]
    exact (hFmeas.indicator measurableSet_closedBall).aemeasurable
  -- STEP 2: the level set is covered by three sets
  have hcover : ∀ x : EuclideanSpace ℝ (Fin n), ‖x‖ ≤ R →
      t < (⨆ ε ∈ Set.Ioi (0 : ℝ), ENNReal.ofReal
        |∫ y in {y : EuclideanSpace ℝ (Fin n) | ε < ‖x - y‖},
          GaussRieszKernel j x y * F y|) →
      x ∈ ({x : EuclideanSpace ℝ (Fin n) | s < LocalMaximalFunction w x}
        ∪ {x : EuclideanSpace ℝ (Fin n) | s < (LocalMaximalFunction u x) ^ 2}
        ∪ {x : EuclideanSpace ℝ (Fin n) | s < N}) := by
    intro x hxR hxt
    by_contra hnot
    simp only [Set.mem_union, not_or, Set.mem_ofPred_eq, not_lt] at hnot
    obtain ⟨⟨h1, h2⟩, h3⟩ := hnot
    have hcot := hC0 f x hxR
    rw [← hudef, ← hwdef, ← hNdef] at hcot
    have hsum : (LocalMaximalFunction u x) ^ 2 + LocalMaximalFunction w x + N ≤ 3 * s := by
      rw [show (3 : ℝ≥0∞) * s = s + s + s from by ring]
      exact add_le_add (add_le_add h2 h1) h3
    refine absurd hxt (not_lt.2 (le_trans hcot (le_trans (mul_le_mul' le_rfl hsum)
      (le_of_eq ?_))))
    rw [← hst]; ring
  -- STEP 3: the term `S₁`
  have hNlin : N = ∫⁻ y, ‖F y‖ₑ ∂(GaussMeasure n) := by
    rw [hNdef, ← ofReal_integral_norm_eq_lintegral_enorm
      (memLp_one_iff_integrable.1 (Lp.memLp f))]
    simp [Real.norm_eq_abs, hFdef]
  have hW : ENNReal.ofReal a
      * (∫⁻ y, ‖w y‖ₑ ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) ≤ N := by
    have hwint : (∫⁻ y, ‖w y‖ₑ ∂(volume : Measure (EuclideanSpace ℝ (Fin n))))
        = ∫⁻ y in closedBall (0 : EuclideanSpace ℝ (Fin n)) (R + 2), ‖F y‖ₑ
            ∂(volume : Measure (EuclideanSpace ℝ (Fin n))) := by
      rw [← lintegral_indicator (μ := (volume : Measure (EuclideanSpace ℝ (Fin n))))
        (f := fun y => ‖F y‖ₑ) measurableSet_closedBall]
      refine lintegral_congr fun y => ?_
      rw [hwdef]
      by_cases hy : y ∈ closedBall (0 : EuclideanSpace ℝ (Fin n)) (R + 2)
      · rw [Set.indicator_of_mem hy, Set.indicator_of_mem hy]
      · rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem hy]; simp
    have hμle : ENNReal.ofReal a • ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict
          (closedBall (0 : EuclideanSpace ℝ (Fin n)) (R + 2)))
        ≤ (GaussMeasure n).restrict (closedBall (0 : EuclideanSpace ℝ (Fin n)) (R + 2)) :=
      Measure.le_iff.2 fun A hA => by
        rw [Measure.smul_apply, smul_eq_mul, Measure.restrict_apply hA,
          Measure.restrict_apply hA, hadef]
        exact (GaussLebesgueBallComparison (n := n)).2.1 (R + 2) _
          (hA.inter measurableSet_closedBall) Set.inter_subset_right
    rw [hwint, hNlin]
    calc ENNReal.ofReal a * ∫⁻ y in closedBall (0 : EuclideanSpace ℝ (Fin n)) (R + 2), ‖F y‖ₑ
          ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))
        = ∫⁻ y, ‖F y‖ₑ ∂(ENNReal.ofReal a
            • ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict
              (closedBall (0 : EuclideanSpace ℝ (Fin n)) (R + 2)))) := by
          rw [lintegral_smul_measure, smul_eq_mul]
      _ ≤ ∫⁻ y, ‖F y‖ₑ
            ∂((GaussMeasure n).restrict (closedBall (0 : EuclideanSpace ℝ (Fin n)) (R + 2))) :=
          lintegral_mono' hμle le_rfl
      _ ≤ ∫⁻ y, ‖F y‖ₑ ∂(GaussMeasure n) := lintegral_mono' Measure.restrict_le_self le_rfl
  have hWle : (∫⁻ y, ‖w y‖ₑ ∂(volume : Measure (EuclideanSpace ℝ (Fin n))))
      ≤ ENNReal.ofReal (q * Real.exp ((R + 2) ^ 2)) * N := by
    calc (∫⁻ y, ‖w y‖ₑ ∂(volume : Measure (EuclideanSpace ℝ (Fin n))))
        = ENNReal.ofReal (q * Real.exp ((R + 2) ^ 2))
            * (ENNReal.ofReal a
              * ∫⁻ y, ‖w y‖ₑ ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) := by
          rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity), haq, ENNReal.ofReal_one,
            one_mul]
      _ ≤ _ := mul_le_mul' le_rfl hW
  have hnum1 : ENNReal.ofReal p * ((4 : ℝ≥0∞) ^ n
        * (ENNReal.ofReal (q * Real.exp ((R + 2) ^ 2)) * N))
      = ENNReal.ofReal (4 ^ n * Real.exp ((R + 2) ^ 2)) * N := by
    rw [show (4 : ℝ≥0∞) ^ n = ENNReal.ofReal ((4 : ℝ) ^ n) from by
        rw [ENNReal.ofReal_pow (by norm_num)]; norm_num,
      show ENNReal.ofReal p * (ENNReal.ofReal ((4 : ℝ) ^ n)
            * (ENNReal.ofReal (q * Real.exp ((R + 2) ^ 2)) * N))
          = (ENNReal.ofReal p * ENNReal.ofReal ((4 : ℝ) ^ n)
              * ENNReal.ofReal (q * Real.exp ((R + 2) ^ 2))) * N from by ring,
      ← ENNReal.ofReal_mul hp0.le, ← ENNReal.ofReal_mul (by positivity),
      show p * (4 : ℝ) ^ n * (q * Real.exp ((R + 2) ^ 2))
          = 4 ^ n * Real.exp ((R + 2) ^ 2) from by
        calc p * (4 : ℝ) ^ n * (q * Real.exp ((R + 2) ^ 2))
            = 4 ^ n * Real.exp ((R + 2) ^ 2) * (p * q) := by ring
          _ = 4 ^ n * Real.exp ((R + 2) ^ 2) := by rw [hpq, mul_one]]
  have hS1 : GaussMeasure n {x : EuclideanSpace ℝ (Fin n) | s < LocalMaximalFunction w x}
      ≤ ENNReal.ofReal (4 ^ n * Real.exp ((R + 2) ^ 2)) * N / s := by
    calc GaussMeasure n {x : EuclideanSpace ℝ (Fin n) | s < LocalMaximalFunction w x}
        ≤ ENNReal.ofReal p
            * volume {x : EuclideanSpace ℝ (Fin n) | s < LocalMaximalFunction w x} := by
          rw [hpdef]; exact (GaussLebesgueBallComparison (n := n)).1 _
      _ ≤ ENNReal.ofReal p * ((4 : ℝ≥0∞) ^ n
            * (∫⁻ y, ‖w y‖ₑ ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) / s) :=
          mul_le_mul' le_rfl (LocalMaximalWeakType w hwmeas s hs0)
      _ ≤ ENNReal.ofReal p * ((4 : ℝ≥0∞) ^ n
            * (ENNReal.ofReal (q * Real.exp ((R + 2) ^ 2)) * N) / s) :=
          mul_le_mul' le_rfl (ENNReal.div_le_div_right (mul_le_mul' le_rfl hWle) s)
      _ = ENNReal.ofReal (4 ^ n * Real.exp ((R + 2) ^ 2)) * N / s := by
          rw [← mul_div_assoc, hnum1]
  -- STEP 4: the term `S₂`, from the pre-built helper
  have hS2 : GaussMeasure n {x : EuclideanSpace ℝ (Fin n) | s < (LocalMaximalFunction u x) ^ 2}
      ≤ ENNReal.ofReal (32 * 4 ^ n * Real.exp ((R + 2) ^ 2)) * N / s := by
    rw [hudef, hNdef]
    exact CoordinateEndpointMaximalSquareBound T hext hT j R f s hs0
  -- STEP 5: the term `S₃`
  have hS3 : GaussMeasure n {x : EuclideanSpace ℝ (Fin n) | s < N} ≤ 1 * N / s := by
    rcases le_or_gt N s with hNs | hNs
    · have hemp : {x : EuclideanSpace ℝ (Fin n) | s < N} = ∅ := by
        ext x
        simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_lt]
        exact hNs
      rw [hemp, measure_empty]
      exact zero_le
    · have hsne : s ≠ ⊤ := by
        intro h
        rw [h] at hNs
        exact absurd hNs (not_lt.2 le_top)
      calc GaussMeasure n {x : EuclideanSpace ℝ (Fin n) | s < N}
          ≤ GaussMeasure n Set.univ := measure_mono (Set.subset_univ _)
        _ = 1 := measure_univ
        _ ≤ 1 * N / s := by
            rw [one_mul, ENNReal.le_div_iff_mul_le (Or.inl hs0) (Or.inl hsne), one_mul]
            exact hNs.le
  -- the conclusion
  refine le_trans (measure_mono fun x hx => hcover x hx.1 hx.2) ?_
  calc GaussMeasure n ({x : EuclideanSpace ℝ (Fin n) | s < LocalMaximalFunction w x}
          ∪ {x : EuclideanSpace ℝ (Fin n) | s < (LocalMaximalFunction u x) ^ 2}
          ∪ {x : EuclideanSpace ℝ (Fin n) | s < N})
      ≤ GaussMeasure n {x : EuclideanSpace ℝ (Fin n) | s < LocalMaximalFunction w x}
          + GaussMeasure n {x : EuclideanSpace ℝ (Fin n) | s < (LocalMaximalFunction u x) ^ 2}
          + GaussMeasure n {x : EuclideanSpace ℝ (Fin n) | s < N} :=
        le_trans (measure_union_le _ _) (add_le_add (measure_union_le _ _) le_rfl)
    _ ≤ ENNReal.ofReal (4 ^ n * Real.exp ((R + 2) ^ 2)) * N / s
          + ENNReal.ofReal (32 * 4 ^ n * Real.exp ((R + 2) ^ 2)) * N / s + 1 * N / s :=
        add_le_add (add_le_add hS1 hS2) hS3
    _ = D * N / s := by
        rw [ENNReal.div_add_div_same, ENNReal.div_add_div_same,
          show ENNReal.ofReal (4 ^ n * Real.exp ((R + 2) ^ 2)) * N
              + ENNReal.ofReal (32 * 4 ^ n * Real.exp ((R + 2) ^ 2)) * N + 1 * N
            = D * N from by rw [hDdef]; ring]
    _ = 3 * C0 * D * N / t := by
        rw [← hst, show 3 * C0 * D * N = 3 * C0 * (D * N) from by ring,
          ENNReal.mul_div_mul_left (D * N) s h3C00 h3C0t]
