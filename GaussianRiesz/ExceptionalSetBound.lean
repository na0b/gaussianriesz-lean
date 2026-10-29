module

public import GaussianRiesz.GaussIsProb

@[expose] public section
open MeasureTheory
theorem ExceptionalSetBound {n : ℕ} (F : Lp ℝ 2 (GaussMeasure n))
    (hF : 0 ≤ᵐ[GaussMeasure n] (F : EuclideanSpace ℝ (Fin n) → ℝ)) (m a : ℝ) (ha : 0 < a)
    (u η : Lp ℝ 2 (GaussMeasure n))
    (hmass : ∫ x, (a - (η : EuclideanSpace ℝ (Fin n) → ℝ) x) ∂(GaussMeasure n) = m)
    (hbd : ∀ᵐ x ∂(GaussMeasure n), 0 ≤ (η : EuclideanSpace ℝ (Fin n) → ℝ) x
      ∧ (η : EuclideanSpace ℝ (Fin n) → ℝ) x
          ≤ max (a - (F : EuclideanSpace ℝ (Fin n) → ℝ) x) 0)
    (hcomp : ∀ᵐ x ∂(GaussMeasure n), 0 < (u : EuclideanSpace ℝ (Fin n) → ℝ) x
      → (η : EuclideanSpace ℝ (Fin n) → ℝ) x = 0) :
    ENNReal.ofReal a * GaussMeasure n {x | 0 < (u : EuclideanSpace ℝ (Fin n) → ℝ) x}
      ≤ ENNReal.ofReal m := by
  set Ω : Set (EuclideanSpace ℝ (Fin n)) :=
    {x | 0 < (u : EuclideanSpace ℝ (Fin n) → ℝ) x} with hΩdef
  have hΩmeas : NullMeasurableSet Ω (GaussMeasure n) :=
    AEStronglyMeasurable.nullMeasurableSet_lt aestronglyMeasurable_const
      (Lp.aestronglyMeasurable u)
  -- `g = a - η` is bounded between `0` and `a`
  have hgbd : ∀ᵐ x ∂(GaussMeasure n),
      0 ≤ a - (η : EuclideanSpace ℝ (Fin n) → ℝ) x
        ∧ a - (η : EuclideanSpace ℝ (Fin n) → ℝ) x ≤ a := by
    filter_upwards [hbd, hF] with x hx hy
    simp only [Pi.zero_apply] at hy
    have hηa : (η : EuclideanSpace ℝ (Fin n) → ℝ) x ≤ a := by
      refine hx.2.trans ?_
      exact max_le (by linarith) ha.le
    exact ⟨by linarith, by linarith⟩
  have hgnn : 0 ≤ᵐ[GaussMeasure n]
      fun x => a - (η : EuclideanSpace ℝ (Fin n) → ℝ) x := by
    filter_upwards [hgbd] with x hx
    simpa using hx.1
  -- `g` is integrable
  have hηint : Integrable (η : EuclideanSpace ℝ (Fin n) → ℝ) (GaussMeasure n) :=
    (Lp.memLp η).integrable (by norm_num)
  have hgint : Integrable (fun x => a - (η : EuclideanSpace ℝ (Fin n) → ℝ) x)
      (GaussMeasure n) := (integrable_const a).sub hηint
  -- on `Ω` we have `g = a`
  have hstep1 : (GaussMeasure n).real Ω * a
      = ∫ x in Ω, (a - (η : EuclideanSpace ℝ (Fin n) → ℝ) x) ∂(GaussMeasure n) := by
    rw [← smul_eq_mul, ← setIntegral_const (μ := GaussMeasure n) (s := Ω) a]
    refine setIntegral_congr_ae₀ hΩmeas ?_
    filter_upwards [hcomp] with x hx hxΩ
    rw [hx hxΩ, sub_zero]
  -- discarding the nonnegative contribution off `Ω`
  have hstep2 : ∫ x in Ω, (a - (η : EuclideanSpace ℝ (Fin n) → ℝ) x) ∂(GaussMeasure n) ≤ m := by
    rw [← hmass]
    exact setIntegral_le_integral hgint hgnn
  have hreal : a * (GaussMeasure n).real Ω ≤ m := by
    rw [mul_comm]
    exact hstep1.trans_le hstep2
  -- transfer to `ℝ≥0∞`
  have hfin : GaussMeasure n Ω ≠ ⊤ := measure_ne_top _ _
  calc ENNReal.ofReal a * GaussMeasure n Ω
      = ENNReal.ofReal a * ENNReal.ofReal ((GaussMeasure n).real Ω) := by
        rw [Measure.real, ENNReal.ofReal_toReal hfin]
    _ = ENNReal.ofReal (a * (GaussMeasure n).real Ω) :=
        (ENNReal.ofReal_mul ha.le).symm
    _ ≤ ENNReal.ofReal m := ENNReal.ofReal_le_ofReal hreal
