module

public import GaussianRiesz.ComplexMainBound
public import GaussianRiesz.ComplexToL1
public import GaussianRiesz.ComplexRieszTransformLinear
public import Mathlib.Topology.Algebra.InfiniteSum.Real

@[expose] public section
open MeasureTheory
theorem ComplexRieszTransformAELimitUnique {n : ℕ}
    (f : Lp ℂ 1 (GaussMeasure n)) (v : ℕ → Lp ℂ 2 (GaussMeasure n))
    (hA : ∀ (u w : Lp ℂ 2 (GaussMeasure n)) (ε : ℝ), 0 < ε →
          GaussMeasure n {x : EuclideanSpace ℝ (Fin n) | ε ≤
              ‖(ComplexRieszTransform u : EuclideanSpace ℝ (Fin n)
                  → EuclideanSpace ℂ (Fin n)) x
                - (ComplexRieszTransform w : EuclideanSpace ℝ (Fin n)
                    → EuclideanSpace ℂ (Fin n)) x‖}
            ≤ ENNReal.ofReal ((16 / Real.pi)
                * (‖ComplexToL1 u - ComplexToL1 w‖ / ε)))
    (hlim : Filter.Tendsto (fun k => ComplexToL1 (v k)) Filter.atTop (nhds f))
    (hCeq : ∀ j, ‖ComplexToL1 (v j) - ComplexToL1 (v (j + 1))‖ ≤ (1/8 : ℝ) ^ j) :
    ∃ g : EuclideanSpace ℝ (Fin n) →ₘ[GaussMeasure n] EuclideanSpace ℂ (Fin n),
      (∀ᵐ x ∂(GaussMeasure n), Filter.Tendsto
          (fun k => (ComplexRieszTransform (v k) : EuclideanSpace ℝ (Fin n)
            → EuclideanSpace ℂ (Fin n)) x) Filter.atTop
          (nhds ((g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℂ (Fin n)) x)))
      ∧ ∀ w : ℕ → Lp ℂ 2 (GaussMeasure n),
          Filter.Tendsto (fun k => ComplexToL1 (w k)) Filter.atTop (nhds f) →
          TendstoInMeasure (GaussMeasure n)
            (fun k => (ComplexRieszTransform (w k) : EuclideanSpace ℝ (Fin n)
              → EuclideanSpace ℂ (Fin n)))
            Filter.atTop (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℂ (Fin n)) := by
  classical
  have hpi := Real.pi_pos
  -- PART D: the exceptional sets and their summable measures
  have hEbd : ∀ j : ℕ, GaussMeasure n {x : EuclideanSpace ℝ (Fin n) | (1/2 : ℝ) ^ j ≤
        ‖(ComplexRieszTransform (v j) : EuclideanSpace ℝ (Fin n)
            → EuclideanSpace ℂ (Fin n)) x
          - (ComplexRieszTransform (v (j + 1)) : EuclideanSpace ℝ (Fin n)
              → EuclideanSpace ℂ (Fin n)) x‖}
      ≤ ENNReal.ofReal ((16 / Real.pi) * (1/4 : ℝ) ^ j) := by
    intro j
    refine le_trans (hA (v j) (v (j + 1)) ((1/2 : ℝ) ^ j) (by positivity)) ?_
    refine ENNReal.ofReal_le_ofReal ?_
    have hden : (0:ℝ) < (1/2 : ℝ) ^ j := by positivity
    have hq : ‖ComplexToL1 (v j) - ComplexToL1 (v (j + 1))‖ / (1/2 : ℝ) ^ j
        ≤ (1/4 : ℝ) ^ j := by
      rw [div_le_iff₀ hden]
      have hpow : (1/4 : ℝ) ^ j * (1/2 : ℝ) ^ j = (1/8 : ℝ) ^ j := by
        rw [← mul_pow]; norm_num
      rw [hpow]
      exact hCeq j
    have h16 : (0:ℝ) < 16 / Real.pi := by positivity
    exact mul_le_mul_of_nonneg_left hq h16.le
  have hsummable : Summable (fun j : ℕ => (16 / Real.pi) * (1/4 : ℝ) ^ j) :=
    (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left _
  have hsum : (∑' j : ℕ, GaussMeasure n {x : EuclideanSpace ℝ (Fin n) | (1/2 : ℝ) ^ j ≤
        ‖(ComplexRieszTransform (v j) : EuclideanSpace ℝ (Fin n)
            → EuclideanSpace ℂ (Fin n)) x
          - (ComplexRieszTransform (v (j + 1)) : EuclideanSpace ℝ (Fin n)
              → EuclideanSpace ℂ (Fin n)) x‖}) ≠ ⊤ := by
    refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum hEbd)
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun j => by positivity) hsummable]
    exact ENNReal.ofReal_ne_top
  -- off a null set the consecutive distances are eventually geometric, hence summable
  have hcauchy : ∀ᵐ x ∂(GaussMeasure n), ∃ L : EuclideanSpace ℂ (Fin n),
      Filter.Tendsto (fun k => (ComplexRieszTransform (v k) : EuclideanSpace ℝ (Fin n)
        → EuclideanSpace ℂ (Fin n)) x) Filter.atTop (nhds L) := by
    filter_upwards [ae_finite_setOfPred_mem hsum] with x hx
    obtain ⟨B, hB⟩ := hx.bddAbove
    refine cauchySeq_tendsto_of_complete (cauchySeq_of_summable_dist ?_)
    rw [← summable_nat_add_iff (B + 1)]
    have hgeo : Summable (fun j : ℕ => (1/2 : ℝ) ^ (j + (B + 1))) := by
      simpa [pow_add] using
        (summable_geometric_of_lt_one (r := (1/2 : ℝ)) (by norm_num)
          (by norm_num)).mul_right ((1/2 : ℝ) ^ (B + 1))
    refine Summable.of_nonneg_of_le (fun j => dist_nonneg) (fun j => ?_) hgeo
    have hnot : x ∉ {y : EuclideanSpace ℝ (Fin n) | (1/2 : ℝ) ^ (j + (B + 1)) ≤
        ‖(ComplexRieszTransform (v (j + (B + 1))) : EuclideanSpace ℝ (Fin n)
            → EuclideanSpace ℂ (Fin n)) y
          - (ComplexRieszTransform (v (j + (B + 1) + 1)) : EuclideanSpace ℝ (Fin n)
              → EuclideanSpace ℂ (Fin n)) y‖} := by
      intro hmem
      exact absurd (hB hmem) (by omega)
    rw [dist_eq_norm]
    exact le_of_lt (not_le.1 (fun hc => hnot hc))
  -- the limit function, and clause (3)
  obtain ⟨g₀, hg₀⟩ : ∃ g₀ : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℂ (Fin n),
      ∀ᵐ x ∂(GaussMeasure n), Filter.Tendsto
        (fun k => (ComplexRieszTransform (v k) : EuclideanSpace ℝ (Fin n)
          → EuclideanSpace ℂ (Fin n)) x) Filter.atTop (nhds (g₀ x)) := by
    refine ⟨fun x => if h : ∃ L : EuclideanSpace ℂ (Fin n), Filter.Tendsto
        (fun k => (ComplexRieszTransform (v k) : EuclideanSpace ℝ (Fin n)
          → EuclideanSpace ℂ (Fin n)) x) Filter.atTop (nhds L) then h.choose else 0, ?_⟩
    filter_upwards [hcauchy] with x hx
    rw [dif_pos hx]
    exact hx.choose_spec
  have hgmeas : AEStronglyMeasurable g₀ (GaussMeasure n) :=
    aestronglyMeasurable_of_tendsto_ae Filter.atTop
      (fun k => Lp.aestronglyMeasurable (ComplexRieszTransform (v k))) hg₀
  have hae3 : ∀ᵐ x ∂(GaussMeasure n), Filter.Tendsto
      (fun k => (ComplexRieszTransform (v k) : EuclideanSpace ℝ (Fin n)
        → EuclideanSpace ℂ (Fin n)) x) Filter.atTop
      (nhds ((AEEqFun.mk g₀ hgmeas : EuclideanSpace ℝ (Fin n)
        → EuclideanSpace ℂ (Fin n)) x)) := by
    filter_upwards [hg₀, AEEqFun.coeFn_mk g₀ hgmeas] with x h1 h2
    rw [h2]
    exact h1
  refine ⟨AEEqFun.mk g₀ hgmeas, hae3, ?_⟩
  -- PART E: every approximating sequence has the same limit in measure
  intro w hw
  have hvmeas : TendstoInMeasure (GaussMeasure n)
      (fun k => (ComplexRieszTransform (v k) : EuclideanSpace ℝ (Fin n)
        → EuclideanSpace ℂ (Fin n))) Filter.atTop
      (AEEqFun.mk g₀ hgmeas : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℂ (Fin n)) :=
    tendstoInMeasure_of_tendsto_ae
      (fun k => Lp.aestronglyMeasurable (ComplexRieszTransform (v k))) hae3
  have hd : Filter.Tendsto (fun k => ‖ComplexToL1 (w k) - ComplexToL1 (v k)‖)
      Filter.atTop (nhds 0) := by
    have h0 := hw.sub hlim
    rw [sub_self] at h0
    simpa using h0.norm
  refine tendstoInMeasure_of_ne_top fun ε hε0 hεtop => ?_
  obtain ⟨ε₀, hε₀0, hε₀⟩ : ∃ ε₀ : ℝ, 0 < ε₀ ∧ ENNReal.ofReal ε₀ = ε :=
    ⟨ε.toReal, ENNReal.toReal_pos hε0.ne' hεtop, ENNReal.ofReal_toReal hεtop⟩
  -- rewrite every `edist` level set as a norm level set
  have hconv : ∀ (δ : ℝ) (u : Lp ℂ 2 (GaussMeasure n)), 0 ≤ δ →
      {x : EuclideanSpace ℝ (Fin n) | ENNReal.ofReal δ ≤
          edist ((ComplexRieszTransform u : EuclideanSpace ℝ (Fin n)
            → EuclideanSpace ℂ (Fin n)) x)
            ((AEEqFun.mk g₀ hgmeas : EuclideanSpace ℝ (Fin n)
              → EuclideanSpace ℂ (Fin n)) x)}
        = {x : EuclideanSpace ℝ (Fin n) | δ ≤
            ‖(ComplexRieszTransform u : EuclideanSpace ℝ (Fin n)
                → EuclideanSpace ℂ (Fin n)) x
              - (AEEqFun.mk g₀ hgmeas : EuclideanSpace ℝ (Fin n)
                  → EuclideanSpace ℂ (Fin n)) x‖} := by
    intro δ u hδ
    ext x
    rw [Set.mem_ofPred_eq, Set.mem_ofPred_eq, edist_dist, dist_eq_norm,
      ENNReal.ofReal_le_ofReal_iff (norm_nonneg _)]
  -- the two-way split
  have hsplit : ∀ k, GaussMeasure n {x : EuclideanSpace ℝ (Fin n) | ε ≤
          edist ((ComplexRieszTransform (w k) : EuclideanSpace ℝ (Fin n)
            → EuclideanSpace ℂ (Fin n)) x)
            ((AEEqFun.mk g₀ hgmeas : EuclideanSpace ℝ (Fin n)
              → EuclideanSpace ℂ (Fin n)) x)}
      ≤ GaussMeasure n {x : EuclideanSpace ℝ (Fin n) | ε₀ / 2 ≤
            ‖(ComplexRieszTransform (w k) : EuclideanSpace ℝ (Fin n)
                → EuclideanSpace ℂ (Fin n)) x
              - (ComplexRieszTransform (v k) : EuclideanSpace ℝ (Fin n)
                  → EuclideanSpace ℂ (Fin n)) x‖}
        + GaussMeasure n {x : EuclideanSpace ℝ (Fin n) | ENNReal.ofReal (ε₀ / 2) ≤
            edist ((ComplexRieszTransform (v k) : EuclideanSpace ℝ (Fin n)
              → EuclideanSpace ℂ (Fin n)) x)
              ((AEEqFun.mk g₀ hgmeas : EuclideanSpace ℝ (Fin n)
                → EuclideanSpace ℂ (Fin n)) x)} := by
    intro k
    rw [← hε₀, hconv ε₀ (w k) hε₀0.le, hconv (ε₀ / 2) (v k) (by positivity)]
    refine le_trans (measure_mono ?_) (measure_union_le _ _)
    intro x hx
    by_cases hc : ε₀ / 2 ≤ ‖(ComplexRieszTransform (w k) : EuclideanSpace ℝ (Fin n)
        → EuclideanSpace ℂ (Fin n)) x
      - (ComplexRieszTransform (v k) : EuclideanSpace ℝ (Fin n)
          → EuclideanSpace ℂ (Fin n)) x‖
    · exact Or.inl hc
    · refine Or.inr ?_
      push Not at hc
      show ε₀ / 2 ≤ _
      have htri := norm_sub_le_norm_sub_add_norm_sub
        ((ComplexRieszTransform (w k) : EuclideanSpace ℝ (Fin n)
          → EuclideanSpace ℂ (Fin n)) x)
        ((ComplexRieszTransform (v k) : EuclideanSpace ℝ (Fin n)
          → EuclideanSpace ℂ (Fin n)) x)
        ((AEEqFun.mk g₀ hgmeas : EuclideanSpace ℝ (Fin n)
          → EuclideanSpace ℂ (Fin n)) x)
      have hxx : ε₀ ≤ _ := hx
      linarith
  -- both summands tend to zero
  have hfirst : Filter.Tendsto (fun k => GaussMeasure n
      {x : EuclideanSpace ℝ (Fin n) | ε₀ / 2 ≤
        ‖(ComplexRieszTransform (w k) : EuclideanSpace ℝ (Fin n)
            → EuclideanSpace ℂ (Fin n)) x
          - (ComplexRieszTransform (v k) : EuclideanSpace ℝ (Fin n)
              → EuclideanSpace ℂ (Fin n)) x‖}) Filter.atTop (nhds 0) := by
    have hreal : Filter.Tendsto (fun k => (16 / Real.pi)
        * (‖ComplexToL1 (w k) - ComplexToL1 (v k)‖ / (ε₀ / 2))) Filter.atTop (nhds 0) := by
      have := (hd.div_const (ε₀ / 2)).const_mul (16 / Real.pi)
      simpa using this
    have hup := (ENNReal.tendsto_ofReal hreal)
    rw [ENNReal.ofReal_zero] at hup
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hup
      (fun k => zero_le) (fun k => hA (w k) (v k) (ε₀ / 2) (by positivity))
  have hsecond := hvmeas (ENNReal.ofReal (ε₀ / 2))
    (by simp only [ENNReal.ofReal_pos]; positivity)
  have hadd : Filter.Tendsto (fun k => GaussMeasure n
        {x : EuclideanSpace ℝ (Fin n) | ε₀ / 2 ≤
          ‖(ComplexRieszTransform (w k) : EuclideanSpace ℝ (Fin n)
              → EuclideanSpace ℂ (Fin n)) x
            - (ComplexRieszTransform (v k) : EuclideanSpace ℝ (Fin n)
                → EuclideanSpace ℂ (Fin n)) x‖}
      + GaussMeasure n {x : EuclideanSpace ℝ (Fin n) | ENNReal.ofReal (ε₀ / 2) ≤
          edist ((ComplexRieszTransform (v k) : EuclideanSpace ℝ (Fin n)
            → EuclideanSpace ℂ (Fin n)) x)
            ((AEEqFun.mk g₀ hgmeas : EuclideanSpace ℝ (Fin n)
              → EuclideanSpace ℂ (Fin n)) x)}) Filter.atTop (nhds 0) := by
    have := hfirst.add hsecond
    rw [add_zero] at this
    exact this
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hadd
    (fun k => zero_le) hsplit
