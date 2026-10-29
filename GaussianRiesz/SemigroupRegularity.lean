module

public import Mathlib.Analysis.Normed.Group.Tannery
public import GaussianRiesz.OUSemigroupSpectral
public import GaussianRiesz.OneLeMultiIndexSum

@[expose] public section
open MeasureTheory
theorem SemigroupRegularity {n : ℕ} (v : Lp ℝ 2 (GaussMeasure n)) :
    (∀ s : ℝ, 0 < s → Energy (OUSemigroup s v) ≠ ⊤)
      ∧ Filter.Tendsto (fun s : ℝ => OUSemigroup s v)
          (nhdsWithin 0 (Set.Ioi 0)) (nhds v) := by
  -- `‖·‖ ^ p.toReal` is the ordinary square on `ℝ`
  have c1 : ∀ x : ℝ, ‖x‖ ^ ((2 : ENNReal).toReal) = x ^ (2 : ℕ) := by
    intro x
    rw [show ((2 : ENNReal)).toReal = ((2 : ℕ) : ℝ) from by norm_num, Real.rpow_natCast,
      Real.norm_eq_abs, ← abs_pow, abs_of_nonneg (by positivity)]
  -- Parseval: the Hermite coefficient family of `v` is square summable
  have hsq : Summable (fun α : Fin n → ℕ => ((HermiteBasis n).repr v α) ^ 2) := by
    have hv : Summable fun β : Fin n → ℕ =>
        ‖(HermiteBasis n).repr v β‖ ^ ((2 : ENNReal).toReal) :=
      (memℓp_gen_iff (p := (2 : ENNReal)) (by norm_num)).mp (lp.memℓp ((HermiteBasis n).repr v))
    exact hv.congr fun β => c1 _
  have hnn : ∀ α : Fin n → ℕ, (0 : ℝ) ≤ (MultiIndexSum α : ℝ) := fun α => Nat.cast_nonneg _
  refine ⟨?_, ?_⟩
  · -- Part (1): instantaneous form-domain regularity
    intro s hs
    -- termwise comparison against `(1/(2s)) |v_α|²`
    have hle : Energy (OUSemigroup s v)
        ≤ ∑' α : {α : Fin n → ℕ // α ≠ 0},
            ENNReal.ofReal (1 / (2 * s) * ((HermiteBasis n).repr v (α : Fin n → ℕ)) ^ 2) := by
      rw [Energy]
      refine ENNReal.tsum_le_tsum fun x => ENNReal.ofReal_le_ofReal ?_
      set L : ℝ := (MultiIndexSum (x : Fin n → ℕ) : ℝ) with hL
      set c : ℝ := (HermiteBasis n).repr v (x : Fin n → ℕ) with hc
      have hL1 : (1 : ℝ) ≤ L := OneLeMultiIndexSum _ x.2
      -- `L^{1/2} ≤ L`
      have hhalf : L ^ ((1 : ℝ) / 2) ≤ L := by
        have h := Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num : (1 : ℝ) / 2 ≤ 1)
        rwa [Real.rpow_one] at h
      -- `e^{-sL}² = (e^{2sL})⁻¹`
      have h2e : Real.exp (-s * L) ^ 2 = (Real.exp (2 * s * L))⁻¹ := by
        rw [sq, ← Real.exp_add, show -s * L + -s * L = -(2 * s * L) by ring, Real.exp_neg]
      have hEpos : (0 : ℝ) < Real.exp (2 * s * L) := Real.exp_pos _
      have hEinv : (0 : ℝ) < (Real.exp (2 * s * L))⁻¹ := inv_pos.mpr hEpos
      -- `L e^{-2sL} ≤ 1/(2s)`, from `x + 1 ≤ e^x`
      have hgoal : L * (Real.exp (2 * s * L))⁻¹ ≤ 1 / (2 * s) := by
        have h2s : (0 : ℝ) < 2 * s := by linarith
        have hb : L * (2 * s) ≤ Real.exp (2 * s * L) := by
          have := Real.add_one_le_exp (2 * s * L)
          nlinarith
        have step : (Real.exp (2 * s * L))⁻¹ * (L * (2 * s)) ≤ 1 := by
          calc (Real.exp (2 * s * L))⁻¹ * (L * (2 * s))
              ≤ (Real.exp (2 * s * L))⁻¹ * Real.exp (2 * s * L) :=
                mul_le_mul_of_nonneg_left hb hEinv.le
            _ = 1 := inv_mul_cancel₀ (ne_of_gt hEpos)
        rw [le_div_iff₀ h2s]
        calc L * (Real.exp (2 * s * L))⁻¹ * (2 * s)
            = (Real.exp (2 * s * L))⁻¹ * (L * (2 * s)) := by ring
          _ ≤ 1 := step
      have hkey : L ^ ((1 : ℝ) / 2) * Real.exp (-s * L) ^ 2 ≤ 1 / (2 * s) := by
        calc L ^ ((1 : ℝ) / 2) * Real.exp (-s * L) ^ 2
            ≤ L * Real.exp (-s * L) ^ 2 :=
              mul_le_mul_of_nonneg_right hhalf (by positivity)
          _ = L * (Real.exp (2 * s * L))⁻¹ := by rw [h2e]
          _ ≤ 1 / (2 * s) := hgoal
      rw [OUSemigroupSpectral s hs.le v (x : Fin n → ℕ)]
      calc L ^ ((1 : ℝ) / 2) * (Real.exp (-s * L) * c) ^ 2
          = (L ^ ((1 : ℝ) / 2) * Real.exp (-s * L) ^ 2) * c ^ 2 := by ring
        _ ≤ 1 / (2 * s) * c ^ 2 := mul_le_mul_of_nonneg_right hkey (sq_nonneg c)
    -- the comparison series is finite
    have hsub : Summable fun x : {α : Fin n → ℕ // α ≠ 0} =>
        1 / (2 * s) * ((HermiteBasis n).repr v (x : Fin n → ℕ)) ^ 2 :=
      (hsq.subtype (fun α : Fin n → ℕ => α ≠ 0)).mul_left _
    have hfin : ∑' α : {α : Fin n → ℕ // α ≠ 0},
        ENNReal.ofReal (1 / (2 * s) * ((HermiteBasis n).repr v (α : Fin n → ℕ)) ^ 2) ≠ ⊤ := by
      rw [← ENNReal.ofReal_tsum_of_nonneg (fun x => by positivity) hsub]
      exact ENNReal.ofReal_ne_top
    exact ne_top_of_le_ne_top hfin hle
  · -- Part (2): strong continuity at `s = 0⁺`
    -- coefficients of the difference
    have hrepr : ∀ s : ℝ, 0 ≤ s → ∀ α : Fin n → ℕ,
        (HermiteBasis n).repr (OUSemigroup s v - v) α
          = (Real.exp (-s * (MultiIndexSum α : ℝ)) - 1) * (HermiteBasis n).repr v α := by
      intro s hs α
      rw [map_sub, lp.coeFn_sub, Pi.sub_apply, OUSemigroupSpectral s hs v α]
      ring
    -- Parseval for the difference
    have hnormsq : ∀ s : ℝ, 0 ≤ s → ‖OUSemigroup s v - v‖ ^ 2
        = ∑' α : Fin n → ℕ,
            ((Real.exp (-s * (MultiIndexSum α : ℝ)) - 1) * (HermiteBasis n).repr v α) ^ 2 := by
      intro s hs
      have h := lp.hasSum_norm (p := (2 : ENNReal)) (by norm_num)
        ((HermiteBasis n).repr (OUSemigroup s v - v))
      rw [show ((2 : ENNReal)).toReal = ((2 : ℕ) : ℝ) from by norm_num] at h
      simp only [Real.rpow_natCast] at h
      have h' : HasSum (fun α : Fin n → ℕ =>
          ((Real.exp (-s * (MultiIndexSum α : ℝ)) - 1) * (HermiteBasis n).repr v α) ^ 2)
          (‖(HermiteBasis n).repr (OUSemigroup s v - v)‖ ^ 2) := by
        refine h.congr_fun fun α => ?_
        rw [Real.norm_eq_abs, ← abs_pow, abs_of_nonneg (sq_nonneg _), hrepr s hs α]
      have ht := h'.tsum_eq
      rw [LinearIsometryEquiv.norm_map] at ht
      exact ht.symm
    -- Tannery / dominated convergence for sums
    have htan : Filter.Tendsto (fun s : ℝ => ∑' α : Fin n → ℕ,
          ((Real.exp (-s * (MultiIndexSum α : ℝ)) - 1) * (HermiteBasis n).repr v α) ^ 2)
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
      have key := tendsto_tsum_of_dominated_convergence
        (𝓕 := nhdsWithin (0 : ℝ) (Set.Ioi 0))
        (f := fun (s : ℝ) (α : Fin n → ℕ) =>
          ((Real.exp (-s * (MultiIndexSum α : ℝ)) - 1) * (HermiteBasis n).repr v α) ^ 2)
        (g := fun _ : Fin n → ℕ => (0 : ℝ))
        (bound := fun α : Fin n → ℕ => ((HermiteBasis n).repr v α) ^ 2) hsq ?_ ?_
      · simpa using key
      · intro α
        have hcont : Continuous fun s : ℝ =>
            ((Real.exp (-s * (MultiIndexSum α : ℝ)) - 1) * (HermiteBasis n).repr v α) ^ 2 := by
          fun_prop
        have h0 : ((Real.exp (-(0 : ℝ) * (MultiIndexSum α : ℝ)) - 1)
            * (HermiteBasis n).repr v α) ^ 2 = 0 := by
          simp
        exact ((hcont.tendsto' 0 0 h0).mono_left nhdsWithin_le_nhds)
      · refine eventually_nhdsWithin_of_forall fun s hs α => ?_
        have hs0 : (0 : ℝ) < s := hs
        have hE1 : Real.exp (-s * (MultiIndexSum α : ℝ)) ≤ 1 := by
          rw [Real.exp_le_one_iff]
          nlinarith [hnn α]
        have hEp : (0 : ℝ) < Real.exp (-s * (MultiIndexSum α : ℝ)) := Real.exp_pos _
        have hfac : (0 : ℝ) ≤ Real.exp (-s * (MultiIndexSum α : ℝ))
            * (2 - Real.exp (-s * (MultiIndexSum α : ℝ))) := by nlinarith
        have hprod := mul_nonneg (sq_nonneg ((HermiteBasis n).repr v α)) hfac
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        nlinarith [hprod]
    -- transfer to the `L²` norm, then to the limit statement
    have h1 : Filter.Tendsto (fun s : ℝ => ‖OUSemigroup s v - v‖ ^ 2)
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
      refine htan.congr' ?_
      refine eventually_nhdsWithin_of_forall fun s hs => ?_
      exact (hnormsq s (le_of_lt hs)).symm
    have h2 : Filter.Tendsto (fun s : ℝ => ‖OUSemigroup s v - v‖)
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
      have h := (Real.continuous_sqrt.tendsto (0 : ℝ)).comp h1
      simp only [Real.sqrt_zero, Function.comp_def] at h
      refine h.congr fun s => ?_
      exact Real.sqrt_sq (norm_nonneg _)
    have h3 : Filter.Tendsto (fun s : ℝ => OUSemigroup s v - v)
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) :=
      tendsto_zero_iff_norm_tendsto_zero.mpr h2
    have h4 : Filter.Tendsto (fun s : ℝ => (OUSemigroup s v - v) + v)
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (0 + v)) := h3.add tendsto_const_nhds
    simpa using h4
