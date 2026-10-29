module

public import GaussianRiesz.L1Extension
public import GaussianRiesz.L2IntoL1
public import GaussianRiesz.HermiteL2Complete
public import GaussianRiesz.RieszL1Limit

@[expose] public section
open MeasureTheory
theorem EndpointTheorem {n : ℕ} :
    ∃! T : Lp ℝ 1 (GaussMeasure n) →ₗ[ℝ]
        (EuclideanSpace ℝ (Fin n) →ₘ[GaussMeasure n] EuclideanSpace ℝ (Fin n)),
      (∀ v : Lp ℝ 2 (GaussMeasure n),
          T (ToL1 v) = (RieszTransform v : EuclideanSpace ℝ (Fin n)
            →ₘ[GaussMeasure n] EuclideanSpace ℝ (Fin n)))
        ∧ ∀ (f : Lp ℝ 1 (GaussMeasure n)) (t : ℝ), 0 < t →
            ENNReal.ofReal t * GaussMeasure n {x | t < ‖T f x‖}
              ≤ ENNReal.ofReal (2 * ‖f‖) := by
  classical
  have hprob : IsProbabilityMeasure (GaussMeasure n) := GaussIsProb n
  -- EXISTENCE
  obtain ⟨T, hT1, hT2⟩ := L1Extension (n := n)
  refine ⟨T, ⟨hT1, hT2⟩, ?_⟩
  -- UNIQUENESS
  rintro T' ⟨hT1', hT2'⟩
  -- the weak bound, divided out to a bound on the level set alone
  have hlev : ∀ (A : EuclideanSpace ℝ (Fin n) →ₘ[GaussMeasure n] EuclideanSpace ℝ (Fin n))
      (c ε : ℝ), 0 < ε →
      (ENNReal.ofReal ε * GaussMeasure n
          {x | ε < ‖(A : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) x‖}
        ≤ ENNReal.ofReal c) →
      GaussMeasure n
          {x | ε < ‖(A : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) x‖}
        ≤ ENNReal.ofReal (c / ε) := by
    intro A c ε hε h
    have hne0 : ENNReal.ofReal ε ≠ 0 := by
      simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]
      exact hε
    have hdv : GaussMeasure n
        {x | ε < ‖(A : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) x‖}
        ≤ ENNReal.ofReal c / ENNReal.ofReal ε := by
      refine (ENNReal.le_div_iff_mul_le (Or.inl hne0)
        (Or.inl ENNReal.ofReal_ne_top)).mpr ?_
      rw [mul_comm]
      exact h
    refine le_trans hdv (le_of_eq ?_)
    rw [← ENNReal.ofReal_div_of_pos hε]
  refine LinearMap.ext fun f => ?_
  -- an `L²` sequence converging to `f` in `L¹`, taken from `RieszL1Limit`
  obtain ⟨-, v, -, hvc, -, -⟩ := RieszL1Limit f
  have hN : Filter.Tendsto (fun k => ‖f - ToL1 (v k)‖) Filter.atTop (nhds 0) := by
    have h := ((tendsto_const_nhds (x := f) (f := Filter.atTop)).sub hvc).norm
    simpa using h
  -- both maps agree on the approximating sequence, so their difference is carried by the tail
  have hdiff : ∀ k, T' f - T f
      = T' (f - ToL1 (v k)) - T (f - ToL1 (v k)) := by
    intro k
    rw [map_sub, map_sub, hT1 (v k), hT1' (v k)]
    abel
  -- every level set of the difference is null
  have hnull : ∀ ε : ℝ, 0 < ε →
      GaussMeasure n {x | 2 * ε
          < ‖(T' f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) x
            - (T f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) x‖} = 0 := by
    intro ε hε
    refine le_antisymm ?_ zero_le
    have hbd : ∀ k : ℕ, GaussMeasure n {x | 2 * ε
        < ‖(T' f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) x
          - (T f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) x‖}
        ≤ ENNReal.ofReal (2 * ‖f - ToL1 (v k)‖ / ε)
          + ENNReal.ofReal (2 * ‖f - ToL1 (v k)‖ / ε) := by
      intro k
      -- pointwise form of `hdiff k`
      have hc1 : ((T' f - T f : EuclideanSpace ℝ (Fin n)
          →ₘ[GaussMeasure n] EuclideanSpace ℝ (Fin n))
          : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
          =ᵐ[GaussMeasure n]
          (T' f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
            - (T f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) :=
        AEEqFun.coeFn_sub _ _
      have hc2 : ((T' (f - ToL1 (v k)) - T (f - ToL1 (v k)) : EuclideanSpace ℝ (Fin n)
          →ₘ[GaussMeasure n] EuclideanSpace ℝ (Fin n))
          : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
          =ᵐ[GaussMeasure n]
          (T' (f - ToL1 (v k)) : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
            - (T (f - ToL1 (v k)) : EuclideanSpace ℝ (Fin n)
              → EuclideanSpace ℝ (Fin n)) := AEEqFun.coeFn_sub _ _
      rw [hdiff k] at hc1
      have hae := hc1.symm.trans hc2
      -- the `2ε` level set splits into the two `ε` level sets
      have hinc : ({x | 2 * ε
          < ‖(T' f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) x
            - (T f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) x‖}
            : Set (EuclideanSpace ℝ (Fin n)))
          ≤ᵐ[GaussMeasure n]
          (({x | ε < ‖(T' (f - ToL1 (v k)) : EuclideanSpace ℝ (Fin n)
              → EuclideanSpace ℝ (Fin n)) x‖}
            ∪ {x | ε < ‖(T (f - ToL1 (v k)) : EuclideanSpace ℝ (Fin n)
              → EuclideanSpace ℝ (Fin n)) x‖}) : Set (EuclideanSpace ℝ (Fin n))) := by
        filter_upwards [hae] with x hx
        intro hmem
        have h2e : 2 * ε
            < ‖(T' f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) x
              - (T f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) x‖ := hmem
        simp only [Pi.sub_apply] at hx
        rw [hx] at h2e
        by_contra hc
        have hA : ‖(T' (f - ToL1 (v k)) : EuclideanSpace ℝ (Fin n)
            → EuclideanSpace ℝ (Fin n)) x‖ ≤ ε :=
          not_lt.mp fun hh => hc (Or.inl hh)
        have hB : ‖(T (f - ToL1 (v k)) : EuclideanSpace ℝ (Fin n)
            → EuclideanSpace ℝ (Fin n)) x‖ ≤ ε :=
          not_lt.mp fun hh => hc (Or.inr hh)
        have htri := norm_sub_le
          ((T' (f - ToL1 (v k)) : EuclideanSpace ℝ (Fin n)
            → EuclideanSpace ℝ (Fin n)) x)
          ((T (f - ToL1 (v k)) : EuclideanSpace ℝ (Fin n)
            → EuclideanSpace ℝ (Fin n)) x)
        linarith
      refine le_trans (measure_mono_ae hinc) (le_trans (measure_union_le _ _) ?_)
      exact add_le_add
        (hlev (T' (f - ToL1 (v k))) (2 * ‖f - ToL1 (v k)‖) ε hε
          (hT2' (f - ToL1 (v k)) ε hε))
        (hlev (T (f - ToL1 (v k))) (2 * ‖f - ToL1 (v k)‖) ε hε
          (hT2 (f - ToL1 (v k)) ε hε))
    have htend : Filter.Tendsto
        (fun k => ENNReal.ofReal (2 * ‖f - ToL1 (v k)‖ / ε)
          + ENNReal.ofReal (2 * ‖f - ToL1 (v k)‖ / ε)) Filter.atTop (nhds 0) := by
      have h : Filter.Tendsto (fun k => 2 * ‖f - ToL1 (v k)‖ / ε)
          Filter.atTop (nhds 0) := by
        have h0 := (hN.const_mul (2 : ℝ)).div_const ε
        simpa using h0
      have h2 := ENNReal.tendsto_ofReal h
      simp only [ENNReal.ofReal_zero] at h2
      simpa using h2.add h2
    exact ge_of_tendsto htend (Filter.Eventually.of_forall hbd)
  -- a nonzero difference exceeds `2/(j+1)` for some `j`, so the difference vanishes a.e.
  refine AEEqFun.ext (ae_iff.mpr ?_)
  refine measure_mono_null ?_
    (measure_iUnion_null (fun j : ℕ => hnull (1 / ((j : ℝ) + 1)) (by positivity)))
  intro x hx
  have hne : (T' f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) x
      ≠ (T f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) x := hx
  have hpos : (0 : ℝ)
      < ‖(T' f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) x
        - (T f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) x‖ := by
    rw [norm_pos_iff, sub_ne_zero]
    exact hne
  obtain ⟨j, hj⟩ := exists_nat_one_div_lt
    (show (0 : ℝ) < ‖(T' f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) x
      - (T f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) x‖ / 2 by positivity)
  refine Set.mem_iUnion.mpr ⟨j, ?_⟩
  show 2 * (1 / ((j : ℝ) + 1))
    < ‖(T' f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) x
      - (T f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) x‖
  linarith
