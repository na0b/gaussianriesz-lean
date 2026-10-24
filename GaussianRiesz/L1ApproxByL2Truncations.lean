import GaussianRiesz.ToL1
import GaussianRiesz.GaussIsProb
open MeasureTheory
theorem L1ApproxByL2Truncations {n : ℕ} (f : Lp ℝ 1 (GaussMeasure n)) :
    ∃ v : ℕ → Lp ℝ 2 (GaussMeasure n),
      (∀ k, ‖ToL1 (v k)‖ ≤ ‖f‖)
        ∧ Filter.Tendsto (fun k => ToL1 (v k)) Filter.atTop (nhds f) := by
  classical
  set F : EuclideanSpace ℝ (Fin n) → ℝ := (f : EuclideanSpace ℝ (Fin n) → ℝ) with hFdef
  set tr : ℕ → EuclideanSpace ℝ (Fin n) → ℝ :=
    fun k x => max (-(k : ℝ)) (min (F x) (k : ℝ)) with htrdef
  have hk0 : ∀ k : ℕ, (0 : ℝ) ≤ (k : ℝ) := fun k => Nat.cast_nonneg k
  have htrk : ∀ (k : ℕ) (x), |tr k x| ≤ (k : ℝ) := by
    intro k x
    rw [htrdef]
    refine abs_le.mpr ⟨le_max_left _ _, max_le (by linarith [hk0 k]) (min_le_right _ _)⟩
  have htrF : ∀ (k : ℕ) (x), |tr k x| ≤ |F x| := by
    intro k x
    rw [htrdef]
    refine abs_le.mpr ⟨?_, ?_⟩
    · refine le_trans (le_min (neg_abs_le (F x)) ?_) (le_max_right _ _)
      linarith [abs_nonneg (F x), hk0 k]
    · refine max_le ?_ (le_trans (min_le_left _ _) (le_abs_self _))
      linarith [abs_nonneg (F x), hk0 k]
  have htrlim : ∀ x, Filter.Tendsto (fun k => tr k x) Filter.atTop (nhds (F x)) := by
    intro x
    refine Filter.Tendsto.congr' ?_ (tendsto_const_nhds (x := F x) (f := Filter.atTop))
    refine Filter.eventually_atTop.mpr ⟨⌈|F x|⌉₊, fun k hk => ?_⟩
    have hle : |F x| ≤ (k : ℝ) :=
      le_trans (Nat.le_ceil _) (by exact_mod_cast Nat.cast_le.mpr hk)
    have h1 : F x ≤ (k : ℝ) := le_trans (le_abs_self _) hle
    have h2 : -(k : ℝ) ≤ F x := by linarith [neg_abs_le (F x)]
    rw [htrdef]
    simp only [min_eq_left h1, max_eq_right h2]
  have hmeas : ∀ k : ℕ, AEStronglyMeasurable (tr k) (GaussMeasure n) := by
    intro k
    rw [htrdef]
    exact aestronglyMeasurable_const.sup
      ((Lp.aestronglyMeasurable f).inf aestronglyMeasurable_const)
  have hmem : ∀ k : ℕ, MemLp (tr k) 2 (GaussMeasure n) := by
    intro k
    refine MemLp.of_bound (hmeas k) (k : ℝ) ?_
    filter_upwards with x
    rw [Real.norm_eq_abs]
    exact htrk k x
  have hc1 : ∀ k : ℕ, (((ToL1 ((hmem k).toLp (tr k)) : Lp ℝ 1 (GaussMeasure n)))
      : EuclideanSpace ℝ (Fin n) → ℝ) =ᵐ[GaussMeasure n] tr k := by
    intro k
    refine Filter.EventuallyEq.trans ?_ ((hmem k).coeFn_toLp)
    rw [ToL1]
    exact MemLp.coeFn_toLp _
  have hvn0 : ∀ k : ℕ, ‖ToL1 ((hmem k).toLp (tr k))‖ ≤ ‖f‖ := by
    intro k
    rw [L1.norm_eq_integral_norm, L1.norm_eq_integral_norm]
    refine integral_mono_ae ((L1.integrable_coeFn _).norm)
      ((L1.integrable_coeFn f).norm) ?_
    filter_upwards [hc1 k] with x hx
    rw [hx, Real.norm_eq_abs, Real.norm_eq_abs]
    exact htrF k x
  have hvc0 : Filter.Tendsto (fun k => ToL1 ((hmem k).toLp (tr k)))
      Filter.atTop (nhds f) := by
    have hnorm : Filter.Tendsto
        (fun k => ‖ToL1 ((hmem k).toLp (tr k)) - f‖) Filter.atTop (nhds 0) := by
      have hdct := tendsto_integral_of_dominated_convergence
        (F := fun (k : ℕ) (x : EuclideanSpace ℝ (Fin n)) => ‖tr k x - F x‖)
        (f := fun _ : EuclideanSpace ℝ (Fin n) => (0 : ℝ))
        (bound := fun x => 2 * ‖F x‖)
        (fun k => ((hmeas k).sub (Lp.aestronglyMeasurable f)).norm)
        ((L1.integrable_coeFn f).norm.const_mul 2)
        (fun k => Filter.Eventually.of_forall fun x => by
          rw [norm_norm]
          have h1 : ‖tr k x‖ ≤ ‖F x‖ := by
            rw [Real.norm_eq_abs, Real.norm_eq_abs]; exact htrF k x
          calc ‖tr k x - F x‖ ≤ ‖tr k x‖ + ‖F x‖ := norm_sub_le _ _
            _ ≤ 2 * ‖F x‖ := by linarith)
        (Filter.Eventually.of_forall fun x => by
          have h := (htrlim x).sub (tendsto_const_nhds (x := F x) (f := Filter.atTop))
          simpa using h.norm)
      simp only [integral_zero] at hdct
      refine hdct.congr fun k => ?_
      have hc2 : (((ToL1 ((hmem k).toLp (tr k)) - f : Lp ℝ 1 (GaussMeasure n)))
          : EuclideanSpace ℝ (Fin n) → ℝ)
          =ᵐ[GaussMeasure n] fun x => tr k x - F x := by
        filter_upwards [hc1 k, Lp.coeFn_sub (ToL1 ((hmem k).toLp (tr k))) f] with x e1 e2
        rw [e2, Pi.sub_apply, e1]
      rw [L1.norm_eq_integral_norm]
      refine integral_congr_ae ?_
      filter_upwards [hc2] with x hx
      rw [hx]
    have h3 := tendsto_zero_iff_norm_tendsto_zero.mpr hnorm
    have h4 := h3.add (tendsto_const_nhds (x := f) (f := Filter.atTop))
    simpa using h4
  exact ⟨fun k => (hmem k).toLp (tr k), hvn0, hvc0⟩
