module

public import GaussianRiesz.ObstacleSublevelBounded
public import GaussianRiesz.ConeWeaklyClosed
public import GaussianRiesz.EnergyWeaklyLSC
public import GaussianRiesz.GaussL2WeakSeqCompact
public import GaussianRiesz.L2InnerGaussIntegral
public import GaussianRiesz.HermiteL2ZeroAEOne

@[expose] public section
open MeasureTheory
-- binder retained for statement fidelity to the paper; intentionally unused in the proof
set_option linter.unusedVariables false
theorem ObstacleMinimizerExists {n : ℕ} (F : Lp ℝ 2 (GaussMeasure n))
    (hF : 0 ≤ᵐ[GaussMeasure n] (F : EuclideanSpace ℝ (Fin n) → ℝ)) (m a : ℝ)
    (hm : m = ∫ x, (F : EuclideanSpace ℝ (Fin n) → ℝ) x ∂(GaussMeasure n)) (ha : m < a) :
    ∃ u ∈ ObstacleCone n, ∀ v ∈ ObstacleCone n,
      ObstacleFunctional F a u ≤ ObstacleFunctional F a v := by
  classical
  have hprob : IsProbabilityMeasure (GaussMeasure n) := GaussIsProb n
  have ham : (0 : ℝ) < a - m := sub_pos.mpr ha
  obtain ⟨hco1, -, hco3⟩ := ObstacleCoercivity F m a hm ha
  -- STEP (a1): the cone is nonempty, so the infimum is over a nonempty set
  have hE0 : Energy (0 : Lp ℝ 2 (GaussMeasure n)) = 0 := by
    have hz : ∀ x : {α : Fin n → ℕ // α ≠ 0},
        ENNReal.ofReal ((MultiIndexSum (x : Fin n → ℕ) : ℝ) ^ ((1 : ℝ) / 2)
          * ((HermiteBasis n).repr (0 : Lp ℝ 2 (GaussMeasure n))
              (x : Fin n → ℕ)) ^ 2) = 0 := by
      intro x
      simp
    rw [Energy, tsum_congr hz, tsum_zero]
  have hcone0 : (0 : Lp ℝ 2 (GaussMeasure n)) ∈ ObstacleCone n := by
    refine ⟨by rw [hE0]; exact ENNReal.zero_ne_top, ?_⟩
    filter_upwards [Lp.coeFn_zero ℝ 2 (GaussMeasure n)] with x hx
    rw [hx]
  have hne : (ObstacleFunctional F a '' ObstacleCone n).Nonempty :=
    ⟨ObstacleFunctional F a 0, ⟨0, hcone0, rfl⟩⟩
  -- STEP (a2): `J` is bounded below on the cone, by coercivity part (1)
  have hbdd : BddBelow (ObstacleFunctional F a '' ObstacleCone n) := by
    refine ⟨-‖F - m • HermiteL2 (0 : Fin n → ℕ)‖ ^ 2, ?_⟩
    rintro y ⟨w, hw, rfl⟩
    have h1 := hco1 w hw
    have h2 : (0 : ℝ) ≤ (Energy w).toReal := ENNReal.toReal_nonneg
    have h3 : (0 : ℝ) ≤ ∫ x, (w : EuclideanSpace ℝ (Fin n) → ℝ) x ∂(GaussMeasure n) :=
      integral_nonneg_of_ae hw.2
    nlinarith [mul_nonneg ham.le h3]
  set I : ℝ := sInf (ObstacleFunctional F a '' ObstacleCone n) with hIdef
  have hIle : ∀ w ∈ ObstacleCone n, I ≤ ObstacleFunctional F a w :=
    fun w hw => csInf_le hbdd ⟨w, hw, rfl⟩
  -- STEP (b): a minimizing sequence, from the definition of the infimum
  have hex : ∀ k : ℕ, ∃ w : Lp ℝ 2 (GaussMeasure n), w ∈ ObstacleCone n ∧
      ObstacleFunctional F a w < I + 1 / ((k : ℝ) + 1) := by
    intro k
    obtain ⟨y, hyS, hy⟩ := Real.lt_sInf_add_pos hne
      (show (0 : ℝ) < 1 / ((k : ℝ) + 1) by positivity)
    obtain ⟨w, hw, rfl⟩ := hyS
    exact ⟨w, hw, hy⟩
  choose v hvcone hvlt using hex
  -- each `J (v k)` is at most `1`, so the sublevel bound applies with `C = 1`
  have hv1 : ∀ k, ObstacleFunctional F a (v k) ≤ 1 := by
    intro k
    have h1 : 1 / ((k : ℝ) + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]
      have : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
      linarith
    linarith [hvlt k, hco3]
  set B : ℝ := (1 + ‖F - m • HermiteL2 (0 : Fin n → ℕ)‖ ^ 2) ^ 2 / (a - m) ^ 2
      + 8 * (1 + ‖F - m • HermiteL2 (0 : Fin n → ℕ)‖ ^ 2) with hBdef
  have hvB : ∀ k, ‖v k‖ ^ 2 + (Energy (v k)).toReal ≤ B := fun k =>
    ObstacleSublevelBounded F m a hm ha 1 (v k) (hvcone k) (hv1 k)
  have hnormle : ∀ k, ‖v k‖ ≤ Real.sqrt B := by
    intro k
    have h2 : ‖v k‖ ^ 2 ≤ B := by
      have h3 : (0 : ℝ) ≤ (Energy (v k)).toReal := ENNReal.toReal_nonneg
      linarith [hvB k]
    calc ‖v k‖ = Real.sqrt (‖v k‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
      _ ≤ Real.sqrt B := Real.sqrt_le_sqrt h2
  -- STEP (c): weak sequential compactness in `L²(γₙ)`
  obtain ⟨σ, u, hσ, -, hconv⟩ := GaussL2WeakSeqCompact v (Real.sqrt B) hnormle
  have hunn : 0 ≤ᵐ[GaussMeasure n] (u : EuclideanSpace ℝ (Fin n) → ℝ) :=
    ConeWeaklyClosed (fun j => v (σ j)) u (fun j => (hvcone (σ j)).2) hconv
  have hlsc := EnergyWeaklyLSC (fun j => v (σ j)) u hconv
  -- the linear term of `J` is an inner product against `a·1 - F`
  set Φ : Lp ℝ 2 (GaussMeasure n) := a • HermiteL2 (0 : Fin n → ℕ) - F with hΦdef
  have hΦc : (Φ : EuclideanSpace ℝ (Fin n) → ℝ) =ᵐ[GaussMeasure n]
      fun x => a - (F : EuclideanSpace ℝ (Fin n) → ℝ) x := by
    rw [hΦdef]
    filter_upwards [Lp.coeFn_sub (a • HermiteL2 (0 : Fin n → ℕ)) F,
      Lp.coeFn_smul a (HermiteL2 (0 : Fin n → ℕ)), HermiteL2ZeroAEOne] with x e1 e2 e3
    rw [e1, Pi.sub_apply, e2, Pi.smul_apply, smul_eq_mul, e3, mul_one]
  have hL : ∀ w : Lp ℝ 2 (GaussMeasure n), (inner ℝ w Φ : ℝ)
      = ∫ x, (a - (F : EuclideanSpace ℝ (Fin n) → ℝ) x)
          * (w : EuclideanSpace ℝ (Fin n) → ℝ) x ∂(GaussMeasure n) := by
    intro w
    rw [L2InnerGaussIntegral]
    refine integral_congr_ae ?_
    filter_upwards [hΦc] with x hx
    rw [hx]
    ring
  -- STEP (d): `J (v k) → I`, hence the energy term has an honest limit
  have hJtend : Filter.Tendsto (fun k => ObstacleFunctional F a (v k)) Filter.atTop
      (nhds I) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le (g := fun _ : ℕ => I)
      (h := fun k : ℕ => I + 1 / ((k : ℝ) + 1)) tendsto_const_nhds ?_
      (fun k => hIle (v k) (hvcone k)) (fun k => (hvlt k).le)
    have h := tendsto_const_nhds (x := I) (f := Filter.atTop (α := ℕ))
      |>.add tendsto_one_div_add_atTop_nhds_zero_nat
    simpa using h
  have hJσ : Filter.Tendsto (fun j => ObstacleFunctional F a (v (σ j))) Filter.atTop
      (nhds I) := hJtend.comp hσ.tendsto_atTop
  have hEtend : Filter.Tendsto (fun j => (Energy (v (σ j))).toReal) Filter.atTop
      (nhds (2 * (I - (inner ℝ u Φ : ℝ)))) := by
    have h := (hJσ.sub (hconv Φ)).const_mul (2 : ℝ)
    refine h.congr fun j => ?_
    rw [ObstacleFunctional, hL (v (σ j))]
    ring
  have hX0 : (0 : ℝ) ≤ 2 * (I - (inner ℝ u Φ : ℝ)) :=
    ge_of_tendsto hEtend (Filter.Eventually.of_forall fun j => ENNReal.toReal_nonneg)
  have hEenn : Filter.Tendsto (fun j => Energy (v (σ j))) Filter.atTop
      (nhds (ENNReal.ofReal (2 * (I - (inner ℝ u Φ : ℝ))))) := by
    refine (ENNReal.tendsto_ofReal hEtend).congr fun j => ?_
    exact ENNReal.ofReal_toReal (hvcone (σ j)).1
  rw [hEenn.liminf_eq] at hlsc
  -- STEP (e): the limit is admissible and `J u ≤ I`
  have huE : Energy u ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hlsc
  have hutoReal : (Energy u).toReal ≤ 2 * (I - (inner ℝ u Φ : ℝ)) :=
    ENNReal.toReal_le_of_le_ofReal hX0 hlsc
  have hJu : ObstacleFunctional F a u ≤ I := by
    rw [ObstacleFunctional, ← hL u]
    linarith
  exact ⟨u, ⟨huE, hunn⟩, fun w hw => le_trans hJu (hIle w hw)⟩
