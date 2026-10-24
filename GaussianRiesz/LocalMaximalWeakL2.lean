import GaussianRiesz.LocalMaximalWeakType
open MeasureTheory Metric
open scoped ENNReal
theorem LocalMaximalWeakL2 {n : ℕ} (w : EuclideanSpace ℝ (Fin n) → ℝ)
    (hw : AEMeasurable w volume) (s : ℝ≥0∞) (hs : s ≠ 0) :
    volume {x : EuclideanSpace ℝ (Fin n) | s < LocalMaximalFunction w x}
      ≤ 16 * 4 ^ n
          * (⨆ σ ∈ Set.Ioi (0 : ℝ≥0∞),
              σ ^ 2 * volume {y : EuclideanSpace ℝ (Fin n) | σ < ‖w y‖ₑ})
          / s ^ 2 := by
  classical
  -- Step 0, part one: the case `s = +∞`, where the level set is empty.
  rcases eq_or_ne s ⊤ with rfl | hstop
  · have hempty : {x : EuclideanSpace ℝ (Fin n) | (⊤ : ℝ≥0∞) < LocalMaximalFunction w x} = ∅ := by
      ext x; simp [not_top_lt]
    rw [hempty, measure_empty]
    exact zero_le
  -- Step 0, part two: replace `w` by a Borel representative `u`.  Both sides of the
  -- asserted inequality are unchanged: the local maximal function is a supremum of
  -- lower integrals, which only see `w` almost everywhere, and the level sets
  -- `{σ < ‖w ·‖ₑ}` are modified inside a null set, which Lebesgue outer measure ignores.
  obtain ⟨u, hu, hwu⟩ := hw
  have hLMF : LocalMaximalFunction w = LocalMaximalFunction u := by
    funext x
    rw [LocalMaximalFunction, LocalMaximalFunction]
    refine iSup_congr fun ρ => iSup_congr fun _ => ?_
    congr 1
    exact lintegral_congr_ae (ae_restrict_of_ae (hwu.mono fun y hy => by simp only [hy]))
  have hlev : ∀ σ : ℝ≥0∞, volume {y : EuclideanSpace ℝ (Fin n) | σ < ‖w y‖ₑ}
      = volume {y : EuclideanSpace ℝ (Fin n) | σ < ‖u y‖ₑ} := by
    intro σ
    refine measure_congr ?_
    filter_upwards [hwu] with y hy
    simp only [eq_iff_iff]
    show σ < ‖w y‖ₑ ↔ σ < ‖u y‖ₑ
    rw [hy]
  rw [hLMF, show (⨆ σ ∈ Set.Ioi (0 : ℝ≥0∞),
        σ ^ 2 * volume {y : EuclideanSpace ℝ (Fin n) | σ < ‖w y‖ₑ})
      = ⨆ σ ∈ Set.Ioi (0 : ℝ≥0∞),
          σ ^ 2 * volume {y : EuclideanSpace ℝ (Fin n) | σ < ‖u y‖ₑ} from
    iSup_congr fun σ => iSup_congr fun _ => by rw [hlev]]
  set A := ⨆ σ ∈ Set.Ioi (0 : ℝ≥0∞),
    σ ^ 2 * volume {y : EuclideanSpace ℝ (Fin n) | σ < ‖u y‖ₑ} with hA
  -- Step 0, part three: the truncation level `l = s/2` and the truncation `u₁`.
  obtain ⟨l, hldef⟩ : ∃ l : ℝ≥0∞, l = s / 2 := ⟨_, rfl⟩
  have hl0 : l ≠ 0 := by rw [hldef]; simp [ENNReal.div_eq_zero_iff, hs]
  have hltop : l ≠ ⊤ := by rw [hldef]; simp [ENNReal.div_eq_top, hs, hstop]
  have hsl : s = 2 * l := by
    rw [hldef, ENNReal.mul_div_cancel (by norm_num) (by norm_num)]
  have hhalves : l + l = s := by rw [hldef, ENNReal.add_halves]
  set u₁ : EuclideanSpace ℝ (Fin n) → ℝ := fun y => if l < ‖u y‖ₑ then u y else 0 with hu₁def
  have hu₁meas : Measurable u₁ := by
    rw [hu₁def]
    exact Measurable.ite (measurableSet_lt measurable_const hu.enorm) hu measurable_const
  have hu₁enorm : ∀ y, ‖u₁ y‖ₑ = if l < ‖u y‖ₑ then ‖u y‖ₑ else 0 := by
    intro y
    simp only [hu₁def]
    split <;> simp
  -- Step 1: `‖u‖ₑ ≤ ‖u₁‖ₑ + l` pointwise, hence `M₂u ≤ M₂u₁ + l` pointwise.
  have hptwise : ∀ y, ‖u y‖ₑ ≤ ‖u₁ y‖ₑ + l := by
    intro y
    rw [hu₁enorm y]
    split
    · exact le_self_add
    · rename_i h
      simpa using not_lt.mp h
  have hstep1 : ∀ x, LocalMaximalFunction u x ≤ LocalMaximalFunction u₁ x + l := by
    intro x
    rw [LocalMaximalFunction]
    refine iSup_le fun ρ => iSup_le fun hρ => ?_
    have hB0 : volume (closedBall x ρ) ≠ 0 := (measure_closedBall_pos volume x hρ.1).ne'
    have hBtop : volume (closedBall x ρ) ≠ ⊤ := measure_closedBall_lt_top.ne
    have hint : ∫⁻ y in closedBall x ρ, ‖u y‖ₑ
        ≤ (∫⁻ y in closedBall x ρ, ‖u₁ y‖ₑ) + l * volume (closedBall x ρ) := by
      calc ∫⁻ y in closedBall x ρ, ‖u y‖ₑ
          ≤ ∫⁻ y in closedBall x ρ, (‖u₁ y‖ₑ + l) := lintegral_mono hptwise
        _ = (∫⁻ y in closedBall x ρ, ‖u₁ y‖ₑ) + l * volume (closedBall x ρ) := by
            rw [lintegral_add_right _ measurable_const, setLIntegral_const]
    calc (volume (closedBall x ρ))⁻¹ * ∫⁻ y in closedBall x ρ, ‖u y‖ₑ
        ≤ (volume (closedBall x ρ))⁻¹
            * ((∫⁻ y in closedBall x ρ, ‖u₁ y‖ₑ) + l * volume (closedBall x ρ)) := by
          gcongr
      _ = (volume (closedBall x ρ))⁻¹ * (∫⁻ y in closedBall x ρ, ‖u₁ y‖ₑ) + l := by
          rw [mul_add]
          congr 1
          rw [mul_comm l (volume (closedBall x ρ)), ← mul_assoc,
            ENNReal.inv_mul_cancel hB0 hBtop, one_mul]
      _ ≤ LocalMaximalFunction u₁ x + l := by
          gcongr
          rw [LocalMaximalFunction]
          exact le_biSup
            (fun r => (volume (closedBall x r))⁻¹ * ∫⁻ y in closedBall x r, ‖u₁ y‖ₑ) hρ
  have hsub : {x : EuclideanSpace ℝ (Fin n) | s < LocalMaximalFunction u x}
      ⊆ {x : EuclideanSpace ℝ (Fin n) | l < LocalMaximalFunction u₁ x} := by
    intro x hx
    rw [Set.mem_ofPred_eq] at hx ⊢
    by_contra hc
    rw [not_lt] at hc
    refine absurd hx (not_lt.mpr ?_)
    calc LocalMaximalFunction u x ≤ LocalMaximalFunction u₁ x + l := hstep1 x
      _ ≤ l + l := by gcongr
      _ = s := hhalves
  -- Step 2: the dyadic decomposition of `{l < ‖u‖ₑ}` and the `L¹` bound on `u₁`.
  have hdy0 : ∀ k : ℕ, (2 : ℝ≥0∞) ^ k * l ≠ 0 := fun k =>
    mul_ne_zero (pow_ne_zero k two_ne_zero) hl0
  have hdytop : ∀ k : ℕ, (2 : ℝ≥0∞) ^ k * l ≠ ⊤ := fun k =>
    ENNReal.mul_ne_top (ENNReal.pow_ne_top (by norm_num)) hltop
  set E : ℕ → Set (EuclideanSpace ℝ (Fin n)) :=
    fun k => {y | 2 ^ k * l < ‖u y‖ₑ ∧ ‖u y‖ₑ ≤ 2 ^ (k + 1) * l} with hEdef
  have hEmeas : ∀ k, MeasurableSet (E k) := by
    intro k
    rw [hEdef]
    exact (measurableSet_lt measurable_const hu.enorm).inter
      (measurableSet_le hu.enorm measurable_const)
  have hEdisj : Pairwise (Function.onFun Disjoint E) := by
    intro j k hjk
    rw [Function.onFun, Set.disjoint_left]
    intro y hyj hyk
    have hstep : ∀ a b : ℕ, a < b → (2 : ℝ≥0∞) ^ (a + 1) * l ≤ 2 ^ b * l := by
      intro a b hab
      gcongr
      · exact one_le_two
      · omega
    rcases lt_or_gt_of_ne hjk with h | h
    · exact absurd (lt_of_le_of_lt (le_trans hyj.2 (hstep j k h)) hyk.1) (lt_irrefl _)
    · exact absurd (lt_of_le_of_lt (le_trans hyk.2 (hstep k j h)) hyj.1) (lt_irrefl _)
  have hEunion : {y : EuclideanSpace ℝ (Fin n) | l < ‖u y‖ₑ} = ⋃ k, E k := by
    ext y
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, hEdef]
    constructor
    · intro hy
      -- Exhaustiveness uses that `u` is REAL valued, so `‖u y‖ₑ ≠ ⊤`: there is no
      -- `σ = +∞` fibre to account for.
      have hex : ∃ k : ℕ, ‖u y‖ₑ ≤ 2 ^ (k + 1) * l := by
        obtain ⟨m, hm⟩ := ENNReal.exists_nat_gt (r := ‖u y‖ₑ / l)
          (by simp [ENNReal.div_eq_top, hl0, enorm_ne_top])
        have hlt : ‖u y‖ₑ < (m : ℝ≥0∞) * l :=
          (ENNReal.div_lt_iff (Or.inl hl0) (Or.inl hltop)).mp hm
        have hmle : ((m : ℕ) : ℝ≥0∞) ≤ 2 ^ m := by
          calc ((m : ℕ) : ℝ≥0∞) ≤ ((2 ^ m : ℕ) : ℝ≥0∞) :=
                Nat.cast_le.mpr (Nat.lt_two_pow_self).le
            _ = 2 ^ m := by push_cast; ring
        have hA1 : (m : ℝ≥0∞) * l ≤ 2 ^ m * l := by gcongr
        have hA2 : (2 : ℝ≥0∞) ^ m * l ≤ 2 ^ (m + 1) * l := by
          gcongr
          · exact one_le_two
          · omega
        exact ⟨m, le_trans hlt.le (le_trans hA1 hA2)⟩
      refine ⟨Nat.find hex, ?_, Nat.find_spec hex⟩
      rcases Nat.eq_zero_or_pos (Nat.find hex) with h0 | hpos
      · rw [h0]; simpa using hy
      · have hmin := Nat.find_min hex (m := Nat.find hex - 1) (by omega)
        rw [not_le] at hmin
        have he : Nat.find hex - 1 + 1 = Nat.find hex := by omega
        rwa [he] at hmin
    · rintro ⟨k, hk1, -⟩
      refine lt_of_le_of_lt ?_ hk1
      nth_rewrite 1 [← one_mul l]
      exact mul_le_mul' (one_le_pow₀ one_le_two) le_rfl
  have hL1eq : ∫⁻ y, ‖u₁ y‖ₑ
      = ∫⁻ y in {y : EuclideanSpace ℝ (Fin n) | l < ‖u y‖ₑ}, ‖u y‖ₑ := by
    rw [← lintegral_indicator (measurableSet_lt measurable_const hu.enorm)]
    refine lintegral_congr fun y => ?_
    by_cases h : l < ‖u y‖ₑ <;> simp [hu₁enorm y, h]
  have hmu : ∀ σ : ℝ≥0∞, σ ≠ 0 → σ ≠ ⊤ →
      volume {y : EuclideanSpace ℝ (Fin n) | σ < ‖u y‖ₑ} ≤ A / σ ^ 2 := by
    intro σ h0 htop
    have hb : σ ^ 2 * volume {y : EuclideanSpace ℝ (Fin n) | σ < ‖u y‖ₑ} ≤ A := by
      rw [hA]
      exact le_biSup (fun σ : ℝ≥0∞ => σ ^ 2 * volume {y : EuclideanSpace ℝ (Fin n) | σ < ‖u y‖ₑ})
        (Set.mem_Ioi.mpr (pos_iff_ne_zero.mpr h0))
    refine (ENNReal.le_div_iff_mul_le (Or.inl (pow_ne_zero 2 h0))
      (Or.inl (ENNReal.pow_ne_top htop))).mpr ?_
    rwa [mul_comm]
  have hstep2 : ∫⁻ y, ‖u₁ y‖ₑ ≤ 4 * A / l := by
    rw [hL1eq, hEunion, lintegral_iUnion hEmeas hEdisj]
    have hterm : ∀ k : ℕ,
        ∫⁻ y in E k, ‖u y‖ₑ ≤ 2 * A * l⁻¹ * ((2 : ℝ≥0∞)⁻¹) ^ k := by
      intro k
      have h1 : ∫⁻ y in E k, ‖u y‖ₑ ≤ 2 ^ (k + 1) * l * volume (E k) := by
        calc ∫⁻ y in E k, ‖u y‖ₑ ≤ ∫⁻ _ in E k, (2 : ℝ≥0∞) ^ (k + 1) * l :=
              lintegral_mono_ae (ae_restrict_of_forall_mem (hEmeas k) fun y hy => hy.2)
          _ = 2 ^ (k + 1) * l * volume (E k) := setLIntegral_const _ _
      have h2 : volume (E k) ≤ A / ((2 : ℝ≥0∞) ^ k * l) ^ 2 := by
        refine le_trans (measure_mono ?_) (hmu _ (hdy0 k) (hdytop k))
        intro y hy
        exact hy.1
      have hinv : ((2 : ℝ≥0∞) ^ k * l)⁻¹ = ((2 : ℝ≥0∞)⁻¹) ^ k * l⁻¹ := by
        rw [ENNReal.mul_inv (Or.inl (pow_ne_zero k two_ne_zero)) (Or.inr hl0),
          ENNReal.inv_pow]
      have hsqinv : (((2 : ℝ≥0∞) ^ k * l) ^ 2)⁻¹
          = ((2 : ℝ≥0∞) ^ k * l)⁻¹ * ((2 : ℝ≥0∞) ^ k * l)⁻¹ := by
        rw [sq, ENNReal.mul_inv (Or.inl (hdy0 k)) (Or.inl (hdytop k))]
      have hcancel : (2 : ℝ≥0∞) ^ k * l * ((2 : ℝ≥0∞) ^ k * l)⁻¹ = 1 :=
        ENNReal.mul_inv_cancel (hdy0 k) (hdytop k)
      calc ∫⁻ y in E k, ‖u y‖ₑ ≤ 2 ^ (k + 1) * l * volume (E k) := h1
        _ ≤ 2 ^ (k + 1) * l * (A / ((2 : ℝ≥0∞) ^ k * l) ^ 2) := by gcongr
        _ = 2 * A * ((2 : ℝ≥0∞) ^ k * l * ((2 : ℝ≥0∞) ^ k * l)⁻¹)
              * ((2 : ℝ≥0∞) ^ k * l)⁻¹ := by
            rw [div_eq_mul_inv, hsqinv, pow_succ]
            ring
        _ = 2 * A * (((2 : ℝ≥0∞)⁻¹) ^ k * l⁻¹) := by rw [hcancel, hinv]; ring
        _ = 2 * A * l⁻¹ * ((2 : ℝ≥0∞)⁻¹) ^ k := by ring
    calc ∑' k : ℕ, ∫⁻ y in E k, ‖u y‖ₑ
        ≤ ∑' k : ℕ, 2 * A * l⁻¹ * ((2 : ℝ≥0∞)⁻¹) ^ k := ENNReal.tsum_le_tsum hterm
      _ = 2 * A * l⁻¹ * ∑' k : ℕ, ((2 : ℝ≥0∞)⁻¹) ^ k := ENNReal.tsum_mul_left
      _ = 2 * A * l⁻¹ * 2 := by rw [ENNReal.tsum_geometric_two]
      _ = 4 * A / l := by rw [div_eq_mul_inv]; ring
  -- Step 3: apply `LocalMaximalWeakType` at `t = l` and compose, entirely in product
  -- form so that no ENNReal division has to be manipulated.
  have hV : volume {x : EuclideanSpace ℝ (Fin n) | l < LocalMaximalFunction u₁ x} * l
      ≤ 4 ^ n * ∫⁻ y, ‖u₁ y‖ₑ :=
    (ENNReal.le_div_iff_mul_le (Or.inl hl0) (Or.inl hltop)).mp
      (LocalMaximalWeakType u₁ hu₁meas.aemeasurable l hl0)
  have hI : (∫⁻ y, ‖u₁ y‖ₑ) * l ≤ 4 * A :=
    (ENNReal.le_div_iff_mul_le (Or.inl hl0) (Or.inl hltop)).mp hstep2
  rw [ENNReal.le_div_iff_mul_le (Or.inl (pow_ne_zero 2 hs))
    (Or.inl (ENNReal.pow_ne_top hstop))]
  calc volume {x : EuclideanSpace ℝ (Fin n) | s < LocalMaximalFunction u x} * s ^ 2
      ≤ volume {x : EuclideanSpace ℝ (Fin n) | l < LocalMaximalFunction u₁ x} * s ^ 2 := by
        gcongr
    _ = 4 * (volume {x : EuclideanSpace ℝ (Fin n) | l < LocalMaximalFunction u₁ x} * l) * l := by
        rw [hsl]; ring
    _ ≤ 4 * (4 ^ n * ∫⁻ y, ‖u₁ y‖ₑ) * l := by gcongr
    _ = 4 * 4 ^ n * ((∫⁻ y, ‖u₁ y‖ₑ) * l) := by ring
    _ ≤ 4 * 4 ^ n * (4 * A) := by gcongr
    _ = 16 * 4 ^ n * A := by ring
