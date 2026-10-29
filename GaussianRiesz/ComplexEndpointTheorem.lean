module

public import GaussianRiesz.ComplexL1Extension

@[expose] public section
open MeasureTheory
theorem ComplexEndpointTheorem {n : ℕ} :
    ∃! T : Lp ℂ 1 (GaussMeasure n) →ₗ[ℂ]
        (EuclideanSpace ℝ (Fin n) →ₘ[GaussMeasure n] EuclideanSpace ℂ (Fin n)),
      (∀ v : Lp ℂ 2 (GaussMeasure n),
          T (ComplexToL1 v) = (ComplexRieszTransform v : EuclideanSpace ℝ (Fin n)
            →ₘ[GaussMeasure n] EuclideanSpace ℂ (Fin n)))
        ∧ ∀ (f : Lp ℂ 1 (GaussMeasure n)) (t : ℝ), 0 < t →
            ENNReal.ofReal t * GaussMeasure n {x | t < ‖T f x‖}
              ≤ ENNReal.ofReal ((8 / Real.pi) * ‖f‖) := by
  classical
  -- Existence is the cited node; only uniqueness is work.
  obtain ⟨T, hT1, hT2⟩ := ComplexL1Extension (n := n)
  refine ⟨T, ⟨hT1, hT2⟩, ?_⟩
  intro T' hT'
  refine LinearMap.ext fun f => ?_
  -- Step 1: an approximating sequence for `f`.
  obtain ⟨g, v, -, hv2, -, -⟩ := ComplexRieszL1Limit f
  -- Step 2: the two maps agree on the approximants, so the difference `T' f - T f`
  -- is the difference of the values at `f - ι_ℂ v_k`.
  have hdiff : ∀ k, T' f - T f
      = T' (f - ComplexToL1 (v k)) - T (f - ComplexToL1 (v k)) := by
    intro k
    rw [map_sub, map_sub, hT1 (v k), hT'.1 (v k)]
    abel
  -- Step 3: the level sets.
  have hmono : ∀ (ε : ℝ) (k : ℕ),
      GaussMeasure n {x | 2 * ε < ‖(T' f - T f : EuclideanSpace ℝ (Fin n)
          →ₘ[GaussMeasure n] EuclideanSpace ℂ (Fin n)) x‖}
        ≤ GaussMeasure n {x | ε < ‖(T' (f - ComplexToL1 (v k)) :
              EuclideanSpace ℝ (Fin n) → EuclideanSpace ℂ (Fin n)) x‖}
          + GaussMeasure n {x | ε < ‖(T (f - ComplexToL1 (v k)) :
              EuclideanSpace ℝ (Fin n) → EuclideanSpace ℂ (Fin n)) x‖} := by
    intro ε k
    refine le_trans (measure_mono_ae ?_) (measure_union_le _ _)
    filter_upwards [AEEqFun.coeFn_sub (T' (f - ComplexToL1 (v k)))
      (T (f - ComplexToL1 (v k)))] with x e
    intro hx
    have hx' : 2 * ε < ‖(T' (f - ComplexToL1 (v k)) - T (f - ComplexToL1 (v k)) :
        EuclideanSpace ℝ (Fin n) →ₘ[GaussMeasure n] EuclideanSpace ℂ (Fin n)) x‖ := by
      rw [← hdiff k]
      exact hx
    rw [e, Pi.sub_apply] at hx'
    by_cases h1 : ε < ‖(T' (f - ComplexToL1 (v k)) :
        EuclideanSpace ℝ (Fin n) → EuclideanSpace ℂ (Fin n)) x‖
    · exact Or.inl h1
    · refine Or.inr ?_
      have htri := norm_sub_le ((T' (f - ComplexToL1 (v k)) :
          EuclideanSpace ℝ (Fin n) → EuclideanSpace ℂ (Fin n)) x)
        ((T (f - ComplexToL1 (v k)) :
          EuclideanSpace ℝ (Fin n) → EuclideanSpace ℂ (Fin n)) x)
      have h1' := not_lt.1 h1
      show ε < ‖(T (f - ComplexToL1 (v k)) :
        EuclideanSpace ℝ (Fin n) → EuclideanSpace ℂ (Fin n)) x‖
      linarith [hx', htri, h1']
  -- and clause (2) for each of `T` and `T'` at the input `f - ι_ℂ v_k`
  have hb : ∀ (ε : ℝ) (k : ℕ), 0 < ε →
      ENNReal.ofReal ε * GaussMeasure n {x | 2 * ε < ‖(T' f - T f :
          EuclideanSpace ℝ (Fin n) →ₘ[GaussMeasure n] EuclideanSpace ℂ (Fin n)) x‖}
        ≤ ENNReal.ofReal ((16 / Real.pi) * ‖f - ComplexToL1 (v k)‖) := by
    intro ε k hε
    have e1 := hT'.2 (f - ComplexToL1 (v k)) ε hε
    have e2 := hT2 (f - ComplexToL1 (v k)) ε hε
    calc ENNReal.ofReal ε * GaussMeasure n {x | 2 * ε < ‖(T' f - T f :
            EuclideanSpace ℝ (Fin n) →ₘ[GaussMeasure n] EuclideanSpace ℂ (Fin n)) x‖}
        ≤ ENNReal.ofReal ε * (GaussMeasure n {x | ε < ‖(T' (f - ComplexToL1 (v k)) :
              EuclideanSpace ℝ (Fin n) → EuclideanSpace ℂ (Fin n)) x‖}
            + GaussMeasure n {x | ε < ‖(T (f - ComplexToL1 (v k)) :
              EuclideanSpace ℝ (Fin n) → EuclideanSpace ℂ (Fin n)) x‖}) :=
          mul_right_mono (hmono ε k)
      _ = ENNReal.ofReal ε * GaussMeasure n {x | ε < ‖(T' (f - ComplexToL1 (v k)) :
              EuclideanSpace ℝ (Fin n) → EuclideanSpace ℂ (Fin n)) x‖}
            + ENNReal.ofReal ε * GaussMeasure n {x | ε < ‖(T (f - ComplexToL1 (v k)) :
              EuclideanSpace ℝ (Fin n) → EuclideanSpace ℂ (Fin n)) x‖} := mul_add _ _ _
      _ ≤ ENNReal.ofReal ((8 / Real.pi) * ‖f - ComplexToL1 (v k)‖)
            + ENNReal.ofReal ((8 / Real.pi) * ‖f - ComplexToL1 (v k)‖) := add_le_add e1 e2
      _ = ENNReal.ofReal ((8 / Real.pi) * ‖f - ComplexToL1 (v k)‖
            + (8 / Real.pi) * ‖f - ComplexToL1 (v k)‖) :=
          (ENNReal.ofReal_add (by positivity) (by positivity)).symm
      _ = ENNReal.ofReal ((16 / Real.pi) * ‖f - ComplexToL1 (v k)‖) := by
          rw [show (8 / Real.pi) * ‖f - ComplexToL1 (v k)‖
              + (8 / Real.pi) * ‖f - ComplexToL1 (v k)‖
            = (16 / Real.pi) * ‖f - ComplexToL1 (v k)‖ from by ring]
  -- Step 4: the right-hand side tends to `0`, and the left-hand side is constant.
  have htend : Filter.Tendsto
      (fun k => ENNReal.ofReal ((16 / Real.pi) * ‖f - ComplexToL1 (v k)‖))
      Filter.atTop (nhds 0) := by
    have h0 : Filter.Tendsto (fun k => ‖f - ComplexToL1 (v k)‖) Filter.atTop (nhds 0) := by
      have h1 := (tendsto_const_nhds (f := Filter.atTop (α := ℕ)) (x := f)).sub hv2
      simpa using h1.norm
    have h2 := h0.const_mul ((16 : ℝ) / Real.pi)
    rw [mul_zero] at h2
    simpa using ENNReal.tendsto_ofReal h2
  have hzero : ∀ ε : ℝ, 0 < ε →
      GaussMeasure n {x | 2 * ε < ‖(T' f - T f : EuclideanSpace ℝ (Fin n)
        →ₘ[GaussMeasure n] EuclideanSpace ℂ (Fin n)) x‖} = 0 := by
    intro ε hε
    have hofne0 : ENNReal.ofReal ε ≠ 0 := by
      simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]
      exact hε
    have hle := ge_of_tendsto htend (Filter.Eventually.of_forall fun k => hb ε k hε)
    exact (mul_eq_zero.1 (nonpos_iff_eq_zero.1 hle)).resolve_left hofne0
  have hU : GaussMeasure n (⋃ j : ℕ, {x | 2 * (1 / ((j : ℝ) + 1)) < ‖(T' f - T f :
      EuclideanSpace ℝ (Fin n) →ₘ[GaussMeasure n] EuclideanSpace ℂ (Fin n)) x‖}) = 0 :=
    measure_iUnion_null fun j => hzero _ (by positivity)
  refine AEEqFun.ext (ae_iff.mpr (measure_mono_null_ae ?_ hU))
  filter_upwards [AEEqFun.coeFn_sub (T' f) (T f)] with x e
  intro hx
  have hx' : (T' f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℂ (Fin n)) x
      ≠ (T f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℂ (Fin n)) x := hx
  have hne : (T' f - T f : EuclideanSpace ℝ (Fin n)
      →ₘ[GaussMeasure n] EuclideanSpace ℂ (Fin n)) x ≠ 0 := by
    rw [e, Pi.sub_apply, sub_ne_zero]
    exact hx'
  obtain ⟨j, hj⟩ := exists_nat_one_div_lt (half_pos (norm_pos_iff.2 hne))
  refine Set.mem_iUnion.2 ⟨j, ?_⟩
  show 2 * (1 / ((j : ℝ) + 1)) < ‖(T' f - T f : EuclideanSpace ℝ (Fin n)
    →ₘ[GaussMeasure n] EuclideanSpace ℂ (Fin n)) x‖
  linarith
