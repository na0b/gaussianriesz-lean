module

public import GaussianRiesz.EnergyBil

@[expose] public section
open MeasureTheory
theorem EnergyFormBilinear {n : ℕ} :
    (∀ v w : Lp ℝ 2 (GaussMeasure n), Energy v ≠ ⊤ → Energy w ≠ ⊤ →
        Summable (fun α : {α : Fin n → ℕ // α ≠ 0} =>
          (MultiIndexSum (α : Fin n → ℕ) : ℝ) ^ ((1 : ℝ) / 2)
            * ((HermiteBasis n).repr v (α : Fin n → ℕ))
            * ((HermiteBasis n).repr w (α : Fin n → ℕ))))
      ∧ (∀ v : Lp ℝ 2 (GaussMeasure n), Energy v ≠ ⊤ →
          EnergyBil v v = (Energy v).toReal)
      ∧ (∀ (v₁ v₂ w : Lp ℝ 2 (GaussMeasure n)) (c : ℝ), Energy v₁ ≠ ⊤ → Energy v₂ ≠ ⊤ →
          Energy w ≠ ⊤ →
            EnergyBil (v₁ + v₂) w = EnergyBil v₁ w + EnergyBil v₂ w
              ∧ EnergyBil (c • v₁) w = c * EnergyBil v₁ w
              ∧ EnergyBil v₁ w = EnergyBil w v₁)
      ∧ (∀ (v₁ v₂ : Lp ℝ 2 (GaussMeasure n)) (c : ℝ), Energy v₁ ≠ ⊤ → Energy v₂ ≠ ⊤ →
          Energy (v₁ + v₂) ≠ ⊤ ∧ Energy (c • v₁) ≠ ⊤) := by
  classical
  -- abbreviations: `E α v` is the `α`-th energy summand
  set S := {α : Fin n → ℕ // α ≠ 0} with hS
  set wt : S → ℝ := fun α => (MultiIndexSum (α : Fin n → ℕ) : ℝ) ^ ((1 : ℝ) / 2) with hwt
  set cf : Lp ℝ 2 (GaussMeasure n) → S → ℝ :=
    fun v α => (HermiteBasis n).repr v (α : Fin n → ℕ) with hcf
  have hwt0 : ∀ α : S, 0 ≤ wt α := fun α => Real.rpow_nonneg (Nat.cast_nonneg _) _
  -- the energy as an `ENNReal` tsum of the summands
  have hEn : ∀ v : Lp ℝ 2 (GaussMeasure n),
      Energy v = ∑' α : S, ENNReal.ofReal (wt α * (cf v α) ^ 2) := fun v => rfl
  have hEnn : ∀ (v : Lp ℝ 2 (GaussMeasure n)) (α : S), 0 ≤ wt α * (cf v α) ^ 2 := by
    intro v α
    exact mul_nonneg (hwt0 α) (sq_nonneg _)
  -- the real-valued form as a real tsum
  have hBil : ∀ v w : Lp ℝ 2 (GaussMeasure n),
      EnergyBil v w = ∑' α : S, wt α * cf v α * cf w α := fun v w => rfl
  -- (A) finite energy is equivalent to summability of the real summands
  have hAfwd : ∀ v : Lp ℝ 2 (GaussMeasure n), Energy v ≠ ⊤ →
      Summable (fun α : S => wt α * (cf v α) ^ 2) := by
    intro v hv
    rw [hEn v] at hv
    have h2 : ∀ α : S, ENNReal.ofReal (wt α * (cf v α) ^ 2)
        = (((wt α * (cf v α) ^ 2).toNNReal : NNReal) : ENNReal) := fun α => rfl
    simp only [h2] at hv
    have h3 := ENNReal.tsum_coe_ne_top_iff_summable.mp hv
    have h4 : Summable (fun α : S => (((wt α * (cf v α) ^ 2).toNNReal : NNReal) : ℝ)) :=
      NNReal.summable_coe.mpr h3
    exact h4.congr fun α => Real.coe_toNNReal _ (hEnn v α)
  have hAbwd : ∀ v : Lp ℝ 2 (GaussMeasure n),
      Summable (fun α : S => wt α * (cf v α) ^ 2) → Energy v ≠ ⊤ := by
    intro v hs
    rw [hEn v]
    exact hs.tsum_ofReal_ne_top
  -- (B) the diagonal value is the energy
  have hdiag : ∀ v : Lp ℝ 2 (GaussMeasure n), Energy v ≠ ⊤ →
      EnergyBil v v = (Energy v).toReal := by
    intro v hv
    have hsum := hAfwd v hv
    have h1 : Energy v = ENNReal.ofReal (∑' α : S, wt α * (cf v α) ^ 2) := by
      rw [hEn v, ← ENNReal.ofReal_tsum_of_nonneg (hEnn v) hsum]
    rw [hBil v v, h1,
      ENNReal.toReal_ofReal (tsum_nonneg (hEnn v))]
    exact tsum_congr fun α => by ring
  -- (C) absolute summability of the mixed family, by the elementary AM-GM bound
  have hmix : ∀ v w : Lp ℝ 2 (GaussMeasure n), Energy v ≠ ⊤ → Energy w ≠ ⊤ →
      Summable (fun α : S => wt α * cf v α * cf w α) := by
    intro v w hv hw
    refine Summable.of_abs ?_
    have hdom : Summable (fun α : S =>
        (1 / 2 : ℝ) * (wt α * (cf v α) ^ 2 + wt α * (cf w α) ^ 2)) :=
      ((hAfwd v hv).add (hAfwd w hw)).mul_left _
    refine Summable.of_nonneg_of_le (fun α => abs_nonneg _) (fun α => ?_) hdom
    have h2 : |wt α * cf v α * cf w α| = wt α * (|cf v α| * |cf w α|) := by
      rw [abs_mul, abs_mul, abs_of_nonneg (hwt0 α), mul_assoc]
    rw [h2]
    have hb : |cf v α| * |cf w α|
        ≤ (1 / 2 : ℝ) * ((cf v α) ^ 2 + (cf w α) ^ 2) := by
      nlinarith [sq_nonneg (|cf v α| - |cf w α|), sq_abs (cf v α), sq_abs (cf w α)]
    calc wt α * (|cf v α| * |cf w α|)
        ≤ wt α * ((1 / 2 : ℝ) * ((cf v α) ^ 2 + (cf w α) ^ 2)) :=
          mul_le_mul_of_nonneg_left hb (hwt0 α)
      _ = (1 / 2 : ℝ) * (wt α * (cf v α) ^ 2 + wt α * (cf w α) ^ 2) := by ring
  refine ⟨hmix, hdiag, ?_, ?_⟩
  · -- (D) bilinearity and symmetry
    intro v₁ v₂ w c hv₁ hv₂ hw
    refine ⟨?_, ?_, ?_⟩
    · rw [hBil, hBil, hBil, ← (hmix v₁ w hv₁ hw).tsum_add (hmix v₂ w hv₂ hw)]
      refine tsum_congr fun α => ?_
      have : cf (v₁ + v₂) α = cf v₁ α + cf v₂ α := by
        simp only [hcf, map_add, lp.coeFn_add, Pi.add_apply]
      rw [this]; ring
    · rw [hBil, hBil, ← tsum_mul_left]
      refine tsum_congr fun α => ?_
      have : cf (c • v₁) α = c * cf v₁ α := by
        simp only [hcf, map_smul, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul]
      rw [this]; ring
    · rw [hBil, hBil]
      exact tsum_congr fun α => by ring
  · -- (E) finite energy is preserved by the vector-space operations
    intro v₁ v₂ c hv₁ hv₂
    constructor
    · refine hAbwd _ (Summable.of_nonneg_of_le (hEnn _) (fun α => ?_)
        (((hAfwd v₁ hv₁).mul_left 2).add ((hAfwd v₂ hv₂).mul_left 2)))
      have hc : cf (v₁ + v₂) α = cf v₁ α + cf v₂ α := by
        simp only [hcf, map_add, lp.coeFn_add, Pi.add_apply]
      rw [hc]
      have hsq : (cf v₁ α + cf v₂ α) ^ 2 ≤ 2 * (cf v₁ α) ^ 2 + 2 * (cf v₂ α) ^ 2 := by
        nlinarith [sq_nonneg (cf v₁ α - cf v₂ α)]
      calc wt α * (cf v₁ α + cf v₂ α) ^ 2
          ≤ wt α * (2 * (cf v₁ α) ^ 2 + 2 * (cf v₂ α) ^ 2) :=
            mul_le_mul_of_nonneg_left hsq (hwt0 α)
        _ = 2 * (wt α * (cf v₁ α) ^ 2) + 2 * (wt α * (cf v₂ α) ^ 2) := by ring
    · refine hAbwd _ ((((hAfwd v₁ hv₁).mul_left (c ^ 2))).congr fun α => ?_)
      have hc : cf (c • v₁) α = c * cf v₁ α := by
        simp only [hcf, map_smul, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul]
      rw [hc]; ring
