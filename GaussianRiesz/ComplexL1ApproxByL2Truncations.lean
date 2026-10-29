module

public import GaussianRiesz.ComplexToL1
public import Mathlib.Topology.Algebra.InfiniteSum.Real

@[expose] public section
open MeasureTheory
theorem ComplexL1ApproxByL2Truncations {n : ℕ} (f : Lp ℂ 1 (GaussMeasure n))
    (hCL1 : ∀ u : Lp ℂ 2 (GaussMeasure n),
        ‖ComplexToL1 u‖ = ∫ x, ‖(u : EuclideanSpace ℝ (Fin n) → ℂ) x‖ ∂(GaussMeasure n))
    :
    ∃ v : ℕ → Lp ℂ 2 (GaussMeasure n),
      (∀ k, ‖ComplexToL1 (v k)‖ ≤ ‖f‖)
        ∧ Filter.Tendsto (fun k => ComplexToL1 (v k)) Filter.atTop (nhds f)
        ∧ ∀ j, ‖ComplexToL1 (v j) - ComplexToL1 (v (j + 1))‖ ≤ (1/8 : ℝ) ^ j := by
  classical
  have hFmeas : Measurable (f : EuclideanSpace ℝ (Fin n) → ℂ) :=
    (AEEqFun.stronglyMeasurable
      (f : EuclideanSpace ℝ (Fin n) →ₘ[GaussMeasure n] ℂ)).measurable
  have hfint : Integrable (f : EuclideanSpace ℝ (Fin n) → ℂ) (GaussMeasure n) :=
    memLp_one_iff_integrable.1 (Lp.memLp f)
  have hfnorm : ‖f‖ = ∫ x, ‖(f : EuclideanSpace ℝ (Fin n) → ℂ) x‖ ∂(GaussMeasure n) :=
    L1.norm_eq_integral_norm f
  -- (B1) and (B2): the radial truncation, measurable, with its modulus identity
  obtain ⟨φ, hφmeas, hφnorm, hφeq⟩ : ∃ φ : ℕ → ℂ → ℂ,
      (∀ k, Measurable (φ k)) ∧ (∀ (k : ℕ) (z : ℂ), ‖φ k z‖ = min ‖z‖ (k : ℝ))
        ∧ (∀ (k : ℕ) (z : ℂ), ‖z‖ ≤ (k : ℝ) → φ k z = z) := by
    refine ⟨fun k z => if ‖z‖ ≤ (k : ℝ) then z else ((k : ℝ) / ‖z‖) • z, ?_, ?_, ?_⟩
    · intro k
      exact Measurable.ite (measurableSet_le (by fun_prop) measurable_const)
        measurable_id (by fun_prop)
    · intro k z
      by_cases h : ‖z‖ ≤ (k : ℝ)
      · show ‖if ‖z‖ ≤ (k : ℝ) then z else ((k : ℝ) / ‖z‖) • z‖ = _
        rw [if_pos h, min_eq_left h]
      · push Not at h
        have hz : (0 : ℝ) < ‖z‖ := lt_of_le_of_lt (Nat.cast_nonneg k) h
        show ‖if ‖z‖ ≤ (k : ℝ) then z else ((k : ℝ) / ‖z‖) • z‖ = _
        rw [if_neg (not_le.2 h), norm_smul, Real.norm_eq_abs,
          abs_of_nonneg (by positivity : (0:ℝ) ≤ (k : ℝ) / ‖z‖), min_eq_right h.le,
          div_mul_cancel₀ _ (ne_of_gt hz)]
    · intro k z hz
      show (if ‖z‖ ≤ (k : ℝ) then z else ((k : ℝ) / ‖z‖) • z) = z
      rw [if_pos hz]
  -- (B3): each truncation is in `L²`
  have hτmem : ∀ k : ℕ, MemLp (fun x => φ k ((f : EuclideanSpace ℝ (Fin n) → ℂ) x)) 2
      (GaussMeasure n) := by
    intro k
    refine MemLp.of_bound ((hφmeas k).comp hFmeas).aestronglyMeasurable (k : ℝ)
      (Filter.Eventually.of_forall fun x => ?_)
    rw [hφnorm]
    exact min_le_right _ _
  obtain ⟨vt, hvtcoe⟩ : ∃ vt : ℕ → Lp ℂ 2 (GaussMeasure n),
      ∀ k, (vt k : EuclideanSpace ℝ (Fin n) → ℂ)
        =ᵐ[GaussMeasure n] fun x => φ k ((f : EuclideanSpace ℝ (Fin n) → ℂ) x) :=
    ⟨fun k => (hτmem k).toLp _, fun k => MemLp.coeFn_toLp _⟩
  have hvtint : ∀ k, Integrable (fun x => ‖(vt k : EuclideanSpace ℝ (Fin n) → ℂ) x‖)
      (GaussMeasure n) :=
    fun k => (memLp_one_iff_integrable.1
      ((Lp.memLp (vt k)).mono_exponent (by norm_num : (1 : ENNReal) ≤ 2))).norm
  -- clause (1) for the full sequence
  have hB3 : ∀ k, ‖ComplexToL1 (vt k)‖ ≤ ‖f‖ := by
    intro k
    rw [hCL1, hfnorm]
    refine integral_mono_ae (hvtint k) hfint.norm ?_
    filter_upwards [hvtcoe k] with x hx
    show ‖(vt k : EuclideanSpace ℝ (Fin n) → ℂ) x‖ ≤ _
    rw [hx, hφnorm]
    exact min_le_left _ _
  -- (B4): `L¹` convergence, clause (2) for the full sequence
  have hclcoe : ∀ k, (ComplexToL1 (vt k) : EuclideanSpace ℝ (Fin n) → ℂ)
      =ᵐ[GaussMeasure n] (vt k : EuclideanSpace ℝ (Fin n) → ℂ) := by
    intro k
    rw [ComplexToL1]
    exact MemLp.coeFn_toLp (p := 1)
      ((Lp.memLp (vt k)).mono_exponent (by norm_num : (1 : ENNReal) ≤ 2))
  have hrep : ∀ k, ‖ComplexToL1 (vt k) - f‖
      = ∫ x, ‖φ k ((f : EuclideanSpace ℝ (Fin n) → ℂ) x)
          - (f : EuclideanSpace ℝ (Fin n) → ℂ) x‖ ∂(GaussMeasure n) := by
    intro k
    rw [L1.norm_eq_integral_norm]
    refine integral_congr_ae ?_
    filter_upwards [Lp.coeFn_sub (ComplexToL1 (vt k)) f, hclcoe k, hvtcoe k] with x e1 e2 e3
    show ‖((ComplexToL1 (vt k) - f : Lp ℂ 1 (GaussMeasure n))
      : EuclideanSpace ℝ (Fin n) → ℂ) x‖ = _
    rw [e1, Pi.sub_apply, e2, e3]
  -- (B4): `L¹` convergence, clause (2) for the full sequence
  have hB4 : Filter.Tendsto (fun k => ComplexToL1 (vt k)) Filter.atTop (nhds f) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have hlim := tendsto_integral_of_dominated_convergence
      (μ := GaussMeasure n)
      (F := fun (k : ℕ) (x : EuclideanSpace ℝ (Fin n)) =>
        ‖φ k ((f : EuclideanSpace ℝ (Fin n) → ℂ) x)
          - (f : EuclideanSpace ℝ (Fin n) → ℂ) x‖)
      (f := fun _ : EuclideanSpace ℝ (Fin n) => (0:ℝ))
      (bound := fun x => 2 * ‖(f : EuclideanSpace ℝ (Fin n) → ℂ) x‖)
      (fun k => (((hφmeas k).comp hFmeas).sub hFmeas).norm.aestronglyMeasurable)
      (hfint.norm.const_mul 2)
      (fun k => Filter.Eventually.of_forall fun x => ?_)
      (Filter.Eventually.of_forall fun x => ?_)
    · simpa using hlim.congr (fun k => (hrep k).symm)
    · rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
      calc ‖φ k ((f : EuclideanSpace ℝ (Fin n) → ℂ) x)
            - (f : EuclideanSpace ℝ (Fin n) → ℂ) x‖
          ≤ ‖φ k ((f : EuclideanSpace ℝ (Fin n) → ℂ) x)‖
            + ‖(f : EuclideanSpace ℝ (Fin n) → ℂ) x‖ := norm_sub_le _ _
        _ ≤ 2 * ‖(f : EuclideanSpace ℝ (Fin n) → ℂ) x‖ := by
            rw [hφnorm]
            have := min_le_left ‖(f : EuclideanSpace ℝ (Fin n) → ℂ) x‖ ((k:ℕ) : ℝ)
            linarith
    · refine tendsto_atTop_of_eventually_const
        (i₀ := ⌈‖(f : EuclideanSpace ℝ (Fin n) → ℂ) x‖⌉₊) fun k hk => ?_
      rw [hφeq k _ (le_trans (Nat.le_ceil _) (by exact_mod_cast hk)), sub_self, norm_zero]
  -- PART C: a rapidly converging subsequence
  have hC : ∀ j : ℕ, ∃ K : ℕ, ‖ComplexToL1 (vt K) - f‖ ≤ (1/2) * (1/8 : ℝ) ^ j := by
    intro j
    have hT := hB4
    rw [tendsto_iff_norm_sub_tendsto_zero] at hT
    have hpos : (0:ℝ) < (1/2) * (1/8 : ℝ) ^ j := by positivity
    obtain ⟨K, hK⟩ := (hT.eventually_lt_const hpos).exists
    exact ⟨K, hK.le⟩
  choose σ hσ using hC
  refine ⟨fun j => vt (σ j), fun j => hB3 (σ j), ?_, ?_⟩
  · rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero (fun j => norm_nonneg _) (fun j => hσ j) ?_
    have : Filter.Tendsto (fun j : ℕ => (1/8 : ℝ) ^ j) Filter.atTop (nhds 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
    simpa using this.const_mul (1/2 : ℝ)
  · intro j
    calc ‖ComplexToL1 (vt (σ j)) - ComplexToL1 (vt (σ (j + 1)))‖
        ≤ ‖ComplexToL1 (vt (σ j)) - f‖ + ‖f - ComplexToL1 (vt (σ (j + 1)))‖ := by
          simpa using norm_sub_le_norm_sub_add_norm_sub
            (ComplexToL1 (vt (σ j))) f (ComplexToL1 (vt (σ (j + 1))))
      _ ≤ (1/2) * (1/8 : ℝ) ^ j + (1/2) * (1/8 : ℝ) ^ (j + 1) := by
          rw [norm_sub_rev f]
          exact add_le_add (hσ j) (hσ (j + 1))
      _ ≤ (1/8 : ℝ) ^ j := by
          have h1 : (1/8 : ℝ) ^ (j + 1) ≤ (1/8 : ℝ) ^ j := by
            rw [pow_succ]
            nlinarith [pow_pos (show (0:ℝ) < 1/8 by norm_num) j]
          linarith
