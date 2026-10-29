module

public import GaussianRiesz.GaussRieszTruncationSmoothSplit
public import GaussianRiesz.SmoothCoreTruncationBridge
public import GaussianRiesz.GaussMaximalTruncationLocal
public import GaussianRiesz.CoordinateEndpointBound

@[expose] public section
open MeasureTheory Metric Filter
open scoped ENNReal
theorem GaussRieszPrincipalValueIsOperator {n : ℕ}
    (T : Lp ℝ 1 (GaussMeasure n) →ₗ[ℝ]
      (EuclideanSpace ℝ (Fin n) →ₘ[GaussMeasure n] EuclideanSpace ℝ (Fin n)))
    (hext : ∀ v : Lp ℝ 2 (GaussMeasure n),
      T (ToL1 v) = (RieszTransform v : EuclideanSpace ℝ (Fin n)
        →ₘ[GaussMeasure n] EuclideanSpace ℝ (Fin n)))
    (hT : ∀ (h : Lp ℝ 1 (GaussMeasure n)) (t : ℝ), 0 < t →
      ENNReal.ofReal t * GaussMeasure n {x | t < ‖T h x‖} ≤ ENNReal.ofReal (2 * ‖h‖))
    (f : Lp ℝ 1 (GaussMeasure n)) (j : Fin n) :
    ∀ᵐ x ∂(GaussMeasure n), ∀ L : ℝ,
      Filter.Tendsto
        (fun ε : ℝ => ∫ y in {y : EuclideanSpace ℝ (Fin n) | ε < ‖x - y‖},
          GaussRieszKernel j x y * (f : EuclideanSpace ℝ (Fin n) → ℝ) y)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds L) →
      L = (T f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) x j := by
  classical
  choose φ g hsm hcs hmem hsmall hsum hsplit using
    fun k : ℕ => GaussRieszTruncationSmoothSplit f k
  -- the k-th error IS `f` minus the class of `φ k` (clause (iii) of the splitting node)
  have hgeq : ∀ k : ℕ, g k = f - (hmem k).toLp (φ k) := by
    intro k
    refine Lp.ext_iff.mpr ?_
    filter_upwards [hsum k, Lp.coeFn_sub f ((hmem k).toLp (φ k)), (hmem k).coeFn_toLp]
      with y h1 h2 h3
    rw [h2, Pi.sub_apply, h3, h1]
    ring
  have hnorm : ∀ k : ℕ, ‖g k‖ < 1 / ((k : ℝ) + 1) := by
    intro k
    rw [L1.norm_eq_integral_norm]
    simpa [Real.norm_eq_abs] using hsmall k
  -- the two per-`k` almost-everywhere facts
  have hae : ∀ᵐ x ∂(GaussMeasure n), ∀ k : ℕ,
      Filter.Tendsto
          (fun ε : ℝ => ∫ y in {y : EuclideanSpace ℝ (Fin n) | ε < ‖x - y‖},
            GaussRieszKernel j x y * φ k y)
          (nhdsWithin 0 (Set.Ioi 0))
          (nhds ((T ((hmem k).toLp (φ k)) : EuclideanSpace ℝ (Fin n)
            → EuclideanSpace ℝ (Fin n)) x j))
        ∧ (T (g k) : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) x j
            = (T f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) x j
              - (T ((hmem k).toLp (φ k)) : EuclideanSpace ℝ (Fin n)
                → EuclideanSpace ℝ (Fin n)) x j := by
    refine ae_all_iff.mpr fun k => ?_
    have h2 : T (g k) = T f - T ((hmem k).toLp (φ k)) := by rw [hgeq k, map_sub]
    filter_upwards [SmoothCoreTruncationBridge T hext (φ k) (hsm k) (hcs k) (hmem k) j,
      AEEqFun.coeFn_sub (T f) (T ((hmem k).toLp (φ k)))] with x hx1 hx2
    refine ⟨hx1, ?_⟩
    rw [h2, hx2]
    rfl
  rw [ae_iff]
  -- the bad set is covered by the two-way split, plus the null set of `hae`
  have hsub : {x : EuclideanSpace ℝ (Fin n) | ¬ ∀ L : ℝ,
        Filter.Tendsto
          (fun ε : ℝ => ∫ y in {y : EuclideanSpace ℝ (Fin n) | ε < ‖x - y‖},
            GaussRieszKernel j x y * (f : EuclideanSpace ℝ (Fin n) → ℝ) y)
          (nhdsWithin 0 (Set.Ioi 0)) (nhds L) →
        L = (T f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) x j}
      ⊆ (⋃ m : ℕ, ⋃ r : ℕ, ⋂ k : ℕ,
            ({x : EuclideanSpace ℝ (Fin n) | ‖x‖ ≤ (r : ℝ) + 1
                ∧ ENNReal.ofReal (1 / ((m : ℝ) + 1))
                  < ⨆ ε ∈ Set.Ioi (0 : ℝ), ENNReal.ofReal
                    |∫ y in {y : EuclideanSpace ℝ (Fin n) | ε < ‖x - y‖},
                      GaussRieszKernel j x y * (g k : EuclideanSpace ℝ (Fin n) → ℝ) y|}
              ∪ {x : EuclideanSpace ℝ (Fin n) | 1 / ((m : ℝ) + 1)
                  < |(T (g k) : EuclideanSpace ℝ (Fin n)
                      → EuclideanSpace ℝ (Fin n)) x j|}))
        ∪ {x : EuclideanSpace ℝ (Fin n) | ¬ ∀ k : ℕ,
            Filter.Tendsto
                (fun ε : ℝ => ∫ y in {y : EuclideanSpace ℝ (Fin n) | ε < ‖x - y‖},
                  GaussRieszKernel j x y * φ k y)
                (nhdsWithin 0 (Set.Ioi 0))
                (nhds ((T ((hmem k).toLp (φ k)) : EuclideanSpace ℝ (Fin n)
                  → EuclideanSpace ℝ (Fin n)) x j))
              ∧ (T (g k) : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) x j
                  = (T f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) x j
                    - (T ((hmem k).toLp (φ k)) : EuclideanSpace ℝ (Fin n)
                      → EuclideanSpace ℝ (Fin n)) x j} := by
    intro x hx
    by_cases hP : ∀ k : ℕ,
        Filter.Tendsto
            (fun ε : ℝ => ∫ y in {y : EuclideanSpace ℝ (Fin n) | ε < ‖x - y‖},
              GaussRieszKernel j x y * φ k y)
            (nhdsWithin 0 (Set.Ioi 0))
            (nhds ((T ((hmem k).toLp (φ k)) : EuclideanSpace ℝ (Fin n)
              → EuclideanSpace ℝ (Fin n)) x j))
          ∧ (T (g k) : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) x j
              = (T f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) x j
                - (T ((hmem k).toLp (φ k)) : EuclideanSpace ℝ (Fin n)
                  → EuclideanSpace ℝ (Fin n)) x j
    · refine Or.inl ?_
      simp only [Set.mem_ofPred_eq, not_forall] at hx
      obtain ⟨L, hL, hne⟩ := hx
      have hpos : 0 < |L - (T f : EuclideanSpace ℝ (Fin n)
          → EuclideanSpace ℝ (Fin n)) x j| := abs_pos.2 (sub_ne_zero_of_ne hne)
      obtain ⟨m, hm⟩ := exists_nat_one_div_lt
        (show (0:ℝ) < |L - (T f : EuclideanSpace ℝ (Fin n)
          → EuclideanSpace ℝ (Fin n)) x j| / 2 by linarith)
      obtain ⟨r, hr⟩ : ∃ r : ℕ, ‖x‖ ≤ (r : ℝ) + 1 :=
        ⟨⌈‖x‖⌉₊, by have h := (Nat.le_ceil ‖x‖ : ‖x‖ ≤ ((⌈‖x‖⌉₊ : ℕ) : ℝ)); linarith⟩
      refine Set.mem_iUnion.2 ⟨m, Set.mem_iUnion.2 ⟨r, Set.mem_iInter.2 fun k => ?_⟩⟩
      obtain ⟨hx1, hx2⟩ := hP k
      have htri : |L - (T f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) x j|
          ≤ |L - (T ((hmem k).toLp (φ k)) : EuclideanSpace ℝ (Fin n)
                → EuclideanSpace ℝ (Fin n)) x j|
            + |(T (g k) : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) x j| := by
        rw [hx2]
        calc |L - (T f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) x j|
            = |(L - (T ((hmem k).toLp (φ k)) : EuclideanSpace ℝ (Fin n)
                  → EuclideanSpace ℝ (Fin n)) x j)
                + (-((T f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) x j
                  - (T ((hmem k).toLp (φ k)) : EuclideanSpace ℝ (Fin n)
                    → EuclideanSpace ℝ (Fin n)) x j))| := by
              rw [show L - (T f : EuclideanSpace ℝ (Fin n)
                      → EuclideanSpace ℝ (Fin n)) x j
                  = (L - (T ((hmem k).toLp (φ k)) : EuclideanSpace ℝ (Fin n)
                      → EuclideanSpace ℝ (Fin n)) x j)
                    + (-((T f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) x j
                      - (T ((hmem k).toLp (φ k)) : EuclideanSpace ℝ (Fin n)
                        → EuclideanSpace ℝ (Fin n)) x j)) from by ring]
          _ ≤ _ := le_trans (abs_add_le _ _) (by rw [abs_neg])
      rcases lt_or_ge (1 / ((m : ℝ) + 1))
          |L - (T ((hmem k).toLp (φ k)) : EuclideanSpace ℝ (Fin n)
            → EuclideanSpace ℝ (Fin n)) x j| with hc | hc
      · -- the maximal-truncation side
        refine Or.inl ⟨hr, ?_⟩
        have hgl : Filter.Tendsto
            (fun ε : ℝ => ∫ y in {y : EuclideanSpace ℝ (Fin n) | ε < ‖x - y‖},
              GaussRieszKernel j x y * (g k : EuclideanSpace ℝ (Fin n) → ℝ) y)
            (nhdsWithin 0 (Set.Ioi 0))
            (nhds (L - (T ((hmem k).toLp (φ k)) : EuclideanSpace ℝ (Fin n)
              → EuclideanSpace ℝ (Fin n)) x j)) := by
          refine (hL.sub hx1).congr' ?_
          filter_upwards [self_mem_nhdsWithin] with ε hε
          rw [(hsplit k j x ε hε).2.2.2]
          ring
        obtain ⟨ε, hεgt, hεpos⟩ :=
          ((Tendsto.eventually_const_lt hc hgl.abs).and self_mem_nhdsWithin).exists
        refine lt_of_lt_of_le ?_ (le_biSup (fun ε : ℝ => ENNReal.ofReal
          |∫ y in {y : EuclideanSpace ℝ (Fin n) | ε < ‖x - y‖},
            GaussRieszKernel j x y * (g k : EuclideanSpace ℝ (Fin n) → ℝ) y|) hεpos)
        exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg (by positivity)).2 hεgt
      · -- the endpoint side
        refine Or.inr ?_
        simp only [Set.mem_ofPred_eq]
        linarith
    · exact Or.inr hP
  refine measure_mono_null hsub ?_
  refine measure_union_null ?_ (ae_iff.1 hae)
  refine measure_iUnion_null fun m => measure_iUnion_null fun r => ?_
  obtain ⟨Cr, hCr0, hCrt, hCrbd⟩ := GaussMaximalTruncationLocal T hext hT j ((r : ℝ) + 1)
    (by have := Nat.cast_nonneg (α := ℝ) r; linarith)
  have htm : ENNReal.ofReal (1 / ((m : ℝ) + 1)) ≠ 0 := by
    simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]
    positivity
  have halg : ∀ a b c : ℝ≥0∞, a * b / c = a / c * b := fun a b c => by
    rw [div_eq_mul_inv, div_eq_mul_inv]; ring
  obtain ⟨D, hDt, hD1, hD2⟩ : ∃ D : ℝ≥0∞, D ≠ ⊤
      ∧ Cr / ENNReal.ofReal (1 / ((m : ℝ) + 1)) ≤ D
      ∧ ENNReal.ofReal 2 / ENNReal.ofReal (1 / ((m : ℝ) + 1)) ≤ D := by
    refine ⟨Cr / ENNReal.ofReal (1 / ((m : ℝ) + 1))
      + ENNReal.ofReal 2 / ENNReal.ofReal (1 / ((m : ℝ) + 1)), ?_, le_self_add, le_add_self⟩
    exact ENNReal.add_ne_top.2 ⟨ENNReal.div_ne_top hCrt htm,
      ENNReal.div_ne_top ENNReal.ofReal_ne_top htm⟩
  refine le_antisymm ?_ zero_le
  have hlim : Filter.Tendsto
      (fun k : ℕ => (D + D) * ENNReal.ofReal (1 / ((k : ℝ) + 1))) Filter.atTop (nhds 0) := by
    have h1 : Filter.Tendsto (fun k : ℕ => 1 / ((k : ℝ) + 1)) Filter.atTop (nhds 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    have h2 := ENNReal.tendsto_ofReal h1
    rw [ENNReal.ofReal_zero] at h2
    have h3 := ENNReal.Tendsto.const_mul h2 (Or.inr (ENNReal.add_ne_top.2 ⟨hDt, hDt⟩))
    rw [mul_zero] at h3
    exact h3
  refine ge_of_tendsto' hlim fun k => ?_
  have hA1 : GaussMeasure n {x : EuclideanSpace ℝ (Fin n) | ‖x‖ ≤ (r : ℝ) + 1
        ∧ ENNReal.ofReal (1 / ((m : ℝ) + 1))
          < ⨆ ε ∈ Set.Ioi (0 : ℝ), ENNReal.ofReal
            |∫ y in {y : EuclideanSpace ℝ (Fin n) | ε < ‖x - y‖},
              GaussRieszKernel j x y * (g k : EuclideanSpace ℝ (Fin n) → ℝ) y|}
      ≤ D * ENNReal.ofReal (1 / ((k : ℝ) + 1)) := by
    calc GaussMeasure n {x : EuclideanSpace ℝ (Fin n) | ‖x‖ ≤ (r : ℝ) + 1
            ∧ ENNReal.ofReal (1 / ((m : ℝ) + 1))
              < ⨆ ε ∈ Set.Ioi (0 : ℝ), ENNReal.ofReal
                |∫ y in {y : EuclideanSpace ℝ (Fin n) | ε < ‖x - y‖},
                  GaussRieszKernel j x y * (g k : EuclideanSpace ℝ (Fin n) → ℝ) y|}
        ≤ Cr * ENNReal.ofReal (∫ y, |(g k : EuclideanSpace ℝ (Fin n) → ℝ) y|
            ∂(GaussMeasure n)) / ENNReal.ofReal (1 / ((m : ℝ) + 1)) :=
          hCrbd (g k) (ENNReal.ofReal (1 / ((m : ℝ) + 1))) htm
      _ = Cr / ENNReal.ofReal (1 / ((m : ℝ) + 1))
            * ENNReal.ofReal (∫ y, |(g k : EuclideanSpace ℝ (Fin n) → ℝ) y|
              ∂(GaussMeasure n)) := halg _ _ _
      _ ≤ D * ENNReal.ofReal (1 / ((k : ℝ) + 1)) :=
          mul_le_mul' hD1 (ENNReal.ofReal_le_ofReal (hsmall k).le)
  have hA2 : GaussMeasure n {x : EuclideanSpace ℝ (Fin n) | 1 / ((m : ℝ) + 1)
        < |(T (g k) : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) x j|}
      ≤ D * ENNReal.ofReal (1 / ((k : ℝ) + 1)) := by
    have hceb := CoordinateEndpointBound T hext hT (g k) j (1 / ((m : ℝ) + 1))
      (by positivity)
    have hstep : GaussMeasure n {x : EuclideanSpace ℝ (Fin n) | 1 / ((m : ℝ) + 1)
          < |(T (g k) : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) x j|}
        ≤ ENNReal.ofReal (2 * ‖g k‖) / ENNReal.ofReal (1 / ((m : ℝ) + 1)) :=
      (ENNReal.le_div_iff_mul_le (Or.inl htm) (Or.inl ENNReal.ofReal_ne_top)).2
        (by rw [mul_comm]; exact hceb)
    refine le_trans hstep ?_
    calc ENNReal.ofReal (2 * ‖g k‖) / ENNReal.ofReal (1 / ((m : ℝ) + 1))
        = ENNReal.ofReal 2 / ENNReal.ofReal (1 / ((m : ℝ) + 1))
            * ENNReal.ofReal ‖g k‖ := by
          rw [ENNReal.ofReal_mul (by norm_num), halg]
      _ ≤ D * ENNReal.ofReal (1 / ((k : ℝ) + 1)) :=
          mul_le_mul' hD2 (ENNReal.ofReal_le_ofReal (hnorm k).le)
  calc GaussMeasure n (⋂ i : ℕ,
          ({x : EuclideanSpace ℝ (Fin n) | ‖x‖ ≤ (r : ℝ) + 1
              ∧ ENNReal.ofReal (1 / ((m : ℝ) + 1))
                < ⨆ ε ∈ Set.Ioi (0 : ℝ), ENNReal.ofReal
                  |∫ y in {y : EuclideanSpace ℝ (Fin n) | ε < ‖x - y‖},
                    GaussRieszKernel j x y * (g i : EuclideanSpace ℝ (Fin n) → ℝ) y|}
            ∪ {x : EuclideanSpace ℝ (Fin n) | 1 / ((m : ℝ) + 1)
                < |(T (g i) : EuclideanSpace ℝ (Fin n)
                    → EuclideanSpace ℝ (Fin n)) x j|}))
      ≤ GaussMeasure n ({x : EuclideanSpace ℝ (Fin n) | ‖x‖ ≤ (r : ℝ) + 1
            ∧ ENNReal.ofReal (1 / ((m : ℝ) + 1))
              < ⨆ ε ∈ Set.Ioi (0 : ℝ), ENNReal.ofReal
                |∫ y in {y : EuclideanSpace ℝ (Fin n) | ε < ‖x - y‖},
                  GaussRieszKernel j x y * (g k : EuclideanSpace ℝ (Fin n) → ℝ) y|}
          ∪ {x : EuclideanSpace ℝ (Fin n) | 1 / ((m : ℝ) + 1)
              < |(T (g k) : EuclideanSpace ℝ (Fin n)
                  → EuclideanSpace ℝ (Fin n)) x j|}) :=
        measure_mono (Set.iInter_subset _ k)
    _ ≤ _ + _ := measure_union_le _ _
    _ ≤ D * ENNReal.ofReal (1 / ((k : ℝ) + 1))
          + D * ENNReal.ofReal (1 / ((k : ℝ) + 1)) := add_le_add hA1 hA2
    _ = (D + D) * ENNReal.ofReal (1 / ((k : ℝ) + 1)) := by ring
