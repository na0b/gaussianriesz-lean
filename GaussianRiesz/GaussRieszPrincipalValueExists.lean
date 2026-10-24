import GaussianRiesz.GaussRieszTruncationSmoothSplit
import GaussianRiesz.GaussMaximalTruncationLocal
import GaussianRiesz.PVCoreSmooth
open MeasureTheory Metric
open scoped ENNReal
theorem GaussRieszPrincipalValueExists {n : ℕ}
    (T : Lp ℝ 1 (GaussMeasure n) →ₗ[ℝ]
      (EuclideanSpace ℝ (Fin n) →ₘ[GaussMeasure n] EuclideanSpace ℝ (Fin n)))
    (hext : ∀ v : Lp ℝ 2 (GaussMeasure n),
      T (ToL1 v) = (RieszTransform v : EuclideanSpace ℝ (Fin n)
        →ₘ[GaussMeasure n] EuclideanSpace ℝ (Fin n)))
    (hT : ∀ (h : Lp ℝ 1 (GaussMeasure n)) (t : ℝ), 0 < t →
      ENNReal.ofReal t * GaussMeasure n {x | t < ‖T h x‖} ≤ ENNReal.ofReal (2 * ‖h‖))
    (f : Lp ℝ 1 (GaussMeasure n)) (j : Fin n) :
    ∀ᵐ x ∂(GaussMeasure n), ∃ L : ℝ,
      Filter.Tendsto
        (fun ε : ℝ => ∫ y in {y : EuclideanSpace ℝ (Fin n) | ε < ‖x - y‖},
          GaussRieszKernel j x y * (f : EuclideanSpace ℝ (Fin n) → ℝ) y)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds L) := by
  classical
  -- STEP 1-2, from the helper: approximants, their errors, and the splitting
  choose φ g hsm hcs hmem hsmall hsum hsplit using
    fun k : ℕ => GaussRieszTruncationSmoothSplit f k
  -- STEP 6: off a null set, the error's maximal truncation can be made arbitrarily small
  have hgood : ∀ᵐ x ∂(GaussMeasure n), ∀ m : ℕ, ∃ k : ℕ, ∀ ε : ℝ, 0 < ε →
      |∫ y in {y : EuclideanSpace ℝ (Fin n) | ε < ‖x - y‖},
        GaussRieszKernel j x y * (g k : EuclideanSpace ℝ (Fin n) → ℝ) y|
          ≤ 1 / ((m : ℝ) + 1) := by
    rw [ae_iff]
    have hbad : {x : EuclideanSpace ℝ (Fin n) | ¬ ∀ m : ℕ, ∃ k : ℕ, ∀ ε : ℝ, 0 < ε →
          |∫ y in {y : EuclideanSpace ℝ (Fin n) | ε < ‖x - y‖},
            GaussRieszKernel j x y * (g k : EuclideanSpace ℝ (Fin n) → ℝ) y|
              ≤ 1 / ((m : ℝ) + 1)}
        ⊆ ⋃ m : ℕ, ⋃ r : ℕ, {x : EuclideanSpace ℝ (Fin n) | ‖x‖ ≤ (r : ℝ) + 1
            ∧ ∀ k : ℕ, ENNReal.ofReal (1 / ((m : ℝ) + 1))
              < ⨆ ε ∈ Set.Ioi (0 : ℝ), ENNReal.ofReal
                |∫ y in {y : EuclideanSpace ℝ (Fin n) | ε < ‖x - y‖},
                  GaussRieszKernel j x y * (g k : EuclideanSpace ℝ (Fin n) → ℝ) y|} := by
      intro x hx
      simp only [Set.mem_ofPred_eq, not_forall, not_exists] at hx
      obtain ⟨m, hm⟩ := hx
      obtain ⟨r, hr⟩ : ∃ r : ℕ, ‖x‖ ≤ (r : ℝ) + 1 :=
        ⟨⌈‖x‖⌉₊, by have h := (Nat.le_ceil ‖x‖ : ‖x‖ ≤ ((⌈‖x‖⌉₊ : ℕ) : ℝ)); linarith⟩
      refine Set.mem_iUnion.2 ⟨m, Set.mem_iUnion.2 ⟨r, hr, fun k => ?_⟩⟩
      obtain ⟨ε, hε0, hgt⟩ : ∃ ε : ℝ, 0 < ε ∧ 1 / ((m : ℝ) + 1)
          < |∫ y in {y : EuclideanSpace ℝ (Fin n) | ε < ‖x - y‖},
              GaussRieszKernel j x y * (g k : EuclideanSpace ℝ (Fin n) → ℝ) y| := by
        have h := hm k
        push Not at h
        obtain ⟨ε, hε0, hgt⟩ := h
        exact ⟨ε, hε0, hgt⟩
      refine lt_of_lt_of_le ?_ (le_biSup (fun ε : ℝ => ENNReal.ofReal
        |∫ y in {y : EuclideanSpace ℝ (Fin n) | ε < ‖x - y‖},
          GaussRieszKernel j x y * (g k : EuclideanSpace ℝ (Fin n) → ℝ) y|)
        (Set.mem_Ioi.2 hε0))
      exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg (by positivity)).2 hgt
    refine measure_mono_null hbad ?_
    refine measure_iUnion_null fun m => measure_iUnion_null fun r => ?_
    obtain ⟨Cr, hCr0, hCrt, hCrbd⟩ := GaussMaximalTruncationLocal T hext hT j ((r : ℝ) + 1)
      (by have := Nat.cast_nonneg (α := ℝ) r; linarith)
    have htm : ENNReal.ofReal (1 / ((m : ℝ) + 1)) ≠ 0 := by
      simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]
      positivity
    obtain ⟨D, hDt, hDdef⟩ : ∃ D : ℝ≥0∞, D ≠ ⊤
        ∧ D = Cr / ENNReal.ofReal (1 / ((m : ℝ) + 1)) :=
      ⟨Cr / ENNReal.ofReal (1 / ((m : ℝ) + 1)), ENNReal.div_ne_top hCrt htm, rfl⟩
    have hAbd : ∀ k : ℕ, GaussMeasure n {x : EuclideanSpace ℝ (Fin n) | ‖x‖ ≤ (r : ℝ) + 1
          ∧ ∀ i : ℕ, ENNReal.ofReal (1 / ((m : ℝ) + 1))
            < ⨆ ε ∈ Set.Ioi (0 : ℝ), ENNReal.ofReal
              |∫ y in {y : EuclideanSpace ℝ (Fin n) | ε < ‖x - y‖},
                GaussRieszKernel j x y * (g i : EuclideanSpace ℝ (Fin n) → ℝ) y|}
        ≤ D * ENNReal.ofReal (1 / ((k : ℝ) + 1)) := by
      intro k
      have halg : ∀ a b c : ℝ≥0∞, a * b / c = a / c * b := fun a b c => by
        rw [div_eq_mul_inv, div_eq_mul_inv]; ring
      calc GaussMeasure n {x : EuclideanSpace ℝ (Fin n) | ‖x‖ ≤ (r : ℝ) + 1
              ∧ ∀ i : ℕ, ENNReal.ofReal (1 / ((m : ℝ) + 1))
                < ⨆ ε ∈ Set.Ioi (0 : ℝ), ENNReal.ofReal
                  |∫ y in {y : EuclideanSpace ℝ (Fin n) | ε < ‖x - y‖},
                    GaussRieszKernel j x y * (g i : EuclideanSpace ℝ (Fin n) → ℝ) y|}
          ≤ GaussMeasure n {x : EuclideanSpace ℝ (Fin n) | ‖x‖ ≤ (r : ℝ) + 1
              ∧ ENNReal.ofReal (1 / ((m : ℝ) + 1))
                < ⨆ ε ∈ Set.Ioi (0 : ℝ), ENNReal.ofReal
                  |∫ y in {y : EuclideanSpace ℝ (Fin n) | ε < ‖x - y‖},
                    GaussRieszKernel j x y * (g k : EuclideanSpace ℝ (Fin n) → ℝ) y|} :=
            measure_mono fun x hx => ⟨hx.1, hx.2 k⟩
        _ ≤ Cr * ENNReal.ofReal (∫ y, |(g k : EuclideanSpace ℝ (Fin n) → ℝ) y|
              ∂(GaussMeasure n)) / ENNReal.ofReal (1 / ((m : ℝ) + 1)) :=
            hCrbd (g k) (ENNReal.ofReal (1 / ((m : ℝ) + 1))) htm
        _ = D * ENNReal.ofReal (∫ y, |(g k : EuclideanSpace ℝ (Fin n) → ℝ) y|
              ∂(GaussMeasure n)) := by
            rw [hDdef, halg]
        _ ≤ D * ENNReal.ofReal (1 / ((k : ℝ) + 1)) :=
            mul_le_mul' le_rfl (ENNReal.ofReal_le_ofReal (hsmall k).le)
    refine le_antisymm ?_ zero_le
    have hlim : Filter.Tendsto (fun k : ℕ => D * ENNReal.ofReal (1 / ((k : ℝ) + 1)))
        Filter.atTop (nhds 0) := by
      have h1 : Filter.Tendsto (fun k : ℕ => 1 / ((k : ℝ) + 1)) Filter.atTop (nhds 0) :=
        tendsto_one_div_add_atTop_nhds_zero_nat
      have h2 := (ENNReal.tendsto_ofReal h1)
      rw [ENNReal.ofReal_zero] at h2
      have h3 := ENNReal.Tendsto.const_mul h2 (Or.inr hDt)
      rw [mul_zero] at h3
      exact h3
    exact ge_of_tendsto' hlim hAbd
  -- STEPS 5 and 7: at a good point the truncations are Cauchy, hence converge
  filter_upwards [hgood] with x hx
  have hcauchy : ∀ η : ℝ, 0 < η → ∃ ρ : ℝ, 0 < ρ ∧ ∀ ε δ : ℝ, ε ∈ Set.Ioo 0 ρ →
      δ ∈ Set.Ioo 0 ρ →
      |(∫ y in {y : EuclideanSpace ℝ (Fin n) | ε < ‖x - y‖},
            GaussRieszKernel j x y * (f : EuclideanSpace ℝ (Fin n) → ℝ) y)
          - ∫ y in {y : EuclideanSpace ℝ (Fin n) | δ < ‖x - y‖},
            GaussRieszKernel j x y * (f : EuclideanSpace ℝ (Fin n) → ℝ) y| ≤ η := by
    intro η hη
    obtain ⟨m, hm⟩ := exists_nat_one_div_lt (show (0:ℝ) < η / 8 by linarith)
    obtain ⟨k, hk⟩ := hx m
    obtain ⟨-, hcore⟩ := PVCoreSmooth (φ k) (hsm k) (hcs k) j x
    obtain ⟨Φ, hΦ⟩ : ∃ Φ : ℝ, Filter.Tendsto
        (fun ε : ℝ => ∫ y in {y : EuclideanSpace ℝ (Fin n) | ε < ‖x - y‖},
          GaussRieszKernel j x y * φ k y) (nhdsWithin 0 (Set.Ioi 0)) (nhds Φ) := ⟨_, hcore⟩
    rw [Metric.tendsto_nhdsWithin_nhds] at hΦ
    obtain ⟨ρ, hρ0, hρ⟩ := hΦ (η / 8) (by linarith)
    refine ⟨ρ, hρ0, fun ε δ hε hδ => ?_⟩
    have hsε := (hsplit k j x ε hε.1).2.2.2
    have hsδ := (hsplit k j x δ hδ.1).2.2.2
    have hcε := hρ (Set.mem_Ioi.2 hε.1) (by rw [Real.dist_eq, sub_zero, abs_of_pos hε.1]; exact hε.2)
    have hcδ := hρ (Set.mem_Ioi.2 hδ.1) (by rw [Real.dist_eq, sub_zero, abs_of_pos hδ.1]; exact hδ.2)
    rw [Real.dist_eq] at hcε hcδ
    have hgε := hk ε hε.1
    have hgδ := hk δ hδ.1
    rw [hsε, hsδ]
    have htri : |(∫ y in {y : EuclideanSpace ℝ (Fin n) | ε < ‖x - y‖},
            GaussRieszKernel j x y * φ k y)
          + (∫ y in {y : EuclideanSpace ℝ (Fin n) | ε < ‖x - y‖},
            GaussRieszKernel j x y * (g k : EuclideanSpace ℝ (Fin n) → ℝ) y)
          - ((∫ y in {y : EuclideanSpace ℝ (Fin n) | δ < ‖x - y‖},
              GaussRieszKernel j x y * φ k y)
            + ∫ y in {y : EuclideanSpace ℝ (Fin n) | δ < ‖x - y‖},
              GaussRieszKernel j x y * (g k : EuclideanSpace ℝ (Fin n) → ℝ) y)|
        ≤ (η / 8 + η / 8) + (1 / ((m : ℝ) + 1) + 1 / ((m : ℝ) + 1)) := by
      have e1 : ∀ a b c d e : ℝ, |a + b - (c + d)| ≤ |a - e| + |c - e| + |b| + |d| := by
        intro a b c d e
        calc |a + b - (c + d)|
            = |((a - e) + (e - c)) + (b + (-d))| := by
              rw [show a + b - (c + d) = ((a - e) + (e - c)) + (b + (-d)) from by ring]
          _ ≤ |(a - e) + (e - c)| + |b + (-d)| := abs_add_le _ _
          _ ≤ (|a - e| + |e - c|) + (|b| + |(-d)|) :=
              add_le_add (abs_add_le _ _) (abs_add_le _ _)
          _ = |a - e| + |c - e| + |b| + |d| := by
              rw [abs_sub_comm e c, abs_neg]; ring
      refine le_trans (e1 _ _ _ _ Φ) ?_
      linarith
    refine le_trans htri ?_
    linarith
  obtain ⟨L, hL⟩ : ∃ L : ℝ, Filter.Tendsto
      (fun ε : ℝ => ∫ y in {y : EuclideanSpace ℝ (Fin n) | ε < ‖x - y‖},
        GaussRieszKernel j x y * (f : EuclideanSpace ℝ (Fin n) → ℝ) y)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds L) := by
    have hc : Cauchy (Filter.map
        (fun ε : ℝ => ∫ y in {y : EuclideanSpace ℝ (Fin n) | ε < ‖x - y‖},
          GaussRieszKernel j x y * (f : EuclideanSpace ℝ (Fin n) → ℝ) y)
        (nhdsWithin (0 : ℝ) (Set.Ioi 0))) := by
      refine Metric.cauchy_iff.2 ⟨Filter.map_neBot, fun η hη => ?_⟩
      obtain ⟨ρ, hρ0, hρ⟩ := hcauchy (η / 2) (by linarith)
      refine ⟨(fun ε : ℝ => ∫ y in {y : EuclideanSpace ℝ (Fin n) | ε < ‖x - y‖},
        GaussRieszKernel j x y * (f : EuclideanSpace ℝ (Fin n) → ℝ) y) '' Set.Ioo 0 ρ, ?_, ?_⟩
      · exact Filter.mem_map.2 (Filter.mem_of_superset
          (Ioo_mem_nhdsGT hρ0) fun y hy => Set.mem_image_of_mem _ hy)
      · rintro a ⟨ε, hε, rfl⟩ b ⟨δ, hδ, rfl⟩
        rw [Real.dist_eq]
        exact lt_of_le_of_lt (hρ ε δ hε hδ) (by linarith)
    exact CompleteSpace.complete hc
  exact ⟨L, hL⟩
