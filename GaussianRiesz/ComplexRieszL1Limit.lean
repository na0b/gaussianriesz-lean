module

public import GaussianRiesz.ComplexMainBound
public import GaussianRiesz.ComplexToL1
public import GaussianRiesz.ComplexRieszTransformLinear
public import Mathlib.Topology.Algebra.InfiniteSum.Real
public import GaussianRiesz.ComplexRieszTransformAELimitUnique
public import GaussianRiesz.ComplexL1ApproxByL2Truncations

@[expose] public section
open MeasureTheory
theorem ComplexRieszL1Limit {n : ℕ} (f : Lp ℂ 1 (GaussMeasure n)) :
    ∃ (g : EuclideanSpace ℝ (Fin n) →ₘ[GaussMeasure n] EuclideanSpace ℂ (Fin n))
      (v : ℕ → Lp ℂ 2 (GaussMeasure n)),
      (∀ k, ‖ComplexToL1 (v k)‖ ≤ ‖f‖)
      ∧ Filter.Tendsto (fun k => ComplexToL1 (v k)) Filter.atTop (nhds f)
      ∧ (∀ᵐ x ∂(GaussMeasure n), Filter.Tendsto
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
  -- PART A: the Cauchy-in-measure estimate
  obtain ⟨hCL1, hA⟩ :
    (∀ u : Lp ℂ 2 (GaussMeasure n),
        ‖ComplexToL1 u‖ = ∫ x, ‖(u : EuclideanSpace ℝ (Fin n) → ℂ) x‖ ∂(GaussMeasure n))
      ∧ (∀ (u w : Lp ℂ 2 (GaussMeasure n)) (ε : ℝ), 0 < ε →
          GaussMeasure n {x : EuclideanSpace ℝ (Fin n) | ε ≤
              ‖(ComplexRieszTransform u : EuclideanSpace ℝ (Fin n)
                  → EuclideanSpace ℂ (Fin n)) x
                - (ComplexRieszTransform w : EuclideanSpace ℝ (Fin n)
                    → EuclideanSpace ℂ (Fin n)) x‖}
            ≤ ENNReal.ofReal ((16 / Real.pi)
                * (‖ComplexToL1 u - ComplexToL1 w‖ / ε))) := by
    have hpi := Real.pi_pos
    have hCL1 : ∀ u : Lp ℂ 2 (GaussMeasure n),
        ‖ComplexToL1 u‖ = ∫ x, ‖(u : EuclideanSpace ℝ (Fin n) → ℂ) x‖ ∂(GaussMeasure n) := by
      intro u
      rw [L1.norm_eq_integral_norm]
      refine integral_congr_ae ?_
      rw [ComplexToL1]
      filter_upwards [MemLp.coeFn_toLp (p := 1) ((Lp.memLp u).mono_exponent (by norm_num))]
        with x hx
      rw [hx]
    refine ⟨hCL1, ?_⟩
    intro u w ε hε
    -- `ComplexToL1` is additive, so the `L¹` distance is the integral of the difference
    have hCL1sub : ComplexToL1 (u - w) = ComplexToL1 u - ComplexToL1 w := by
      refine Lp.ext_iff.mpr ?_
      rw [ComplexToL1, ComplexToL1, ComplexToL1]
      filter_upwards [MemLp.coeFn_toLp (p := 1)
          ((Lp.memLp (u - w)).mono_exponent (by norm_num : (1 : ENNReal) ≤ 2)),
        Lp.coeFn_sub ((MemLp.toLp (u : EuclideanSpace ℝ (Fin n) → ℂ)
          ((Lp.memLp u).mono_exponent (by norm_num : (1 : ENNReal) ≤ 2))))
          ((MemLp.toLp (w : EuclideanSpace ℝ (Fin n) → ℂ)
          ((Lp.memLp w).mono_exponent (by norm_num : (1 : ENNReal) ≤ 2)))),
        MemLp.coeFn_toLp (p := 1) ((Lp.memLp u).mono_exponent (by norm_num)),
        MemLp.coeFn_toLp (p := 1) ((Lp.memLp w).mono_exponent (by norm_num)),
        Lp.coeFn_sub u w] with x e1 e2 e3 e4 e5
      rw [e1, e2, Pi.sub_apply, e3, e4, e5, Pi.sub_apply]
    -- the transform is additive and ℂ-homogeneous, so it respects differences
    have hCRTsub : ComplexRieszTransform (u - w)
        = ComplexRieszTransform u - ComplexRieszTransform w := by
      have hadd := (ComplexRieszTransformLinear (n := n)).1
      have hsmul := (ComplexRieszTransformLinear (n := n)).2.1
      rw [show u - w = u + (-1 : ℂ) • w from by
        rw [neg_one_smul]; exact (sub_eq_add_neg u w), hadd, hsmul, neg_one_smul,
        ← sub_eq_add_neg]
    -- ComplexMainBound at the level ε/2
    have hmb := ComplexMainBound (u - w) (ε / 2) (by positivity)
    -- the level set at ε sits a.e. inside the level set at ε/2 for the difference
    have hmono : GaussMeasure n {x : EuclideanSpace ℝ (Fin n) | ε ≤
          ‖(ComplexRieszTransform u : EuclideanSpace ℝ (Fin n)
              → EuclideanSpace ℂ (Fin n)) x
            - (ComplexRieszTransform w : EuclideanSpace ℝ (Fin n)
                → EuclideanSpace ℂ (Fin n)) x‖}
        ≤ GaussMeasure n {x : EuclideanSpace ℝ (Fin n) | ε / 2 <
            ‖(ComplexRieszTransform (u - w) : EuclideanSpace ℝ (Fin n)
              → EuclideanSpace ℂ (Fin n)) x‖} := by
      refine measure_mono_ae ?_
      filter_upwards [Lp.coeFn_sub (ComplexRieszTransform u) (ComplexRieszTransform w)]
        with x hx hmem
      have hco : (ComplexRieszTransform (u - w) : EuclideanSpace ℝ (Fin n)
            → EuclideanSpace ℂ (Fin n)) x
          = (ComplexRieszTransform u : EuclideanSpace ℝ (Fin n)
              → EuclideanSpace ℂ (Fin n)) x
            - (ComplexRieszTransform w : EuclideanSpace ℝ (Fin n)
                → EuclideanSpace ℂ (Fin n)) x := by
        rw [hCRTsub, hx, Pi.sub_apply]
      show ε / 2 < ‖(ComplexRieszTransform (u - w) : EuclideanSpace ℝ (Fin n)
        → EuclideanSpace ℂ (Fin n)) x‖
      rw [hco]
      exact lt_of_lt_of_le (show ε / 2 < ε by linarith) hmem
    -- cancel the `ε/2`
    refine (ENNReal.mul_le_mul_iff_right
      (by simp [ENNReal.ofReal_eq_zero, not_le]; positivity)
      ENNReal.ofReal_ne_top (a := ENNReal.ofReal (ε / 2))).1 ?_
    calc ENNReal.ofReal (ε / 2) * GaussMeasure n {x : EuclideanSpace ℝ (Fin n) | ε ≤
            ‖(ComplexRieszTransform u : EuclideanSpace ℝ (Fin n)
                → EuclideanSpace ℂ (Fin n)) x
              - (ComplexRieszTransform w : EuclideanSpace ℝ (Fin n)
                  → EuclideanSpace ℂ (Fin n)) x‖}
        ≤ ENNReal.ofReal (ε / 2) * GaussMeasure n {x : EuclideanSpace ℝ (Fin n) | ε / 2 <
            ‖(ComplexRieszTransform (u - w) : EuclideanSpace ℝ (Fin n)
              → EuclideanSpace ℂ (Fin n)) x‖} := mul_le_mul' le_rfl hmono
      _ ≤ ENNReal.ofReal ((8 / Real.pi)
            * ∫ x, ‖((u - w : Lp ℂ 2 (GaussMeasure n))
                : EuclideanSpace ℝ (Fin n) → ℂ) x‖ ∂(GaussMeasure n)) := hmb
      _ = ENNReal.ofReal (ε / 2) * ENNReal.ofReal ((16 / Real.pi)
            * (‖ComplexToL1 u - ComplexToL1 w‖ / ε)) := by
          rw [← ENNReal.ofReal_mul (by positivity), ← hCL1sub, hCL1 (u - w)]
          congr 1
          have hrw : (ε / 2) * ((16 / Real.pi)
                * ((∫ x, ‖((u - w : Lp ℂ 2 (GaussMeasure n))
                    : EuclideanSpace ℝ (Fin n) → ℂ) x‖ ∂(GaussMeasure n)) / ε))
              = ((8 / Real.pi) * ∫ x, ‖((u - w : Lp ℂ 2 (GaussMeasure n))
                  : EuclideanSpace ℝ (Fin n) → ℂ) x‖ ∂(GaussMeasure n)) * (ε / ε) := by
            ring
          rw [hrw, div_self (ne_of_gt hε), mul_one]
  -- PARTS B and C: the radial truncations, and a rapidly converging subsequence
  obtain ⟨v, hB3, hlim, hCeq⟩ := ComplexL1ApproxByL2Truncations f hCL1
  -- PARTS D and E: the almost-everywhere limit, and uniqueness in measure
  obtain ⟨g, hae3, hclause4⟩ :=
    ComplexRieszTransformAELimitUnique f v hA hlim hCeq
  exact ⟨g, v, hB3, hlim, hae3, hclause4⟩
