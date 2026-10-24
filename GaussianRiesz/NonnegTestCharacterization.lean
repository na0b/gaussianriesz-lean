import GaussianRiesz.GaussIsProb
open MeasureTheory
theorem NonnegTestCharacterization {n : ℕ} (v : Lp ℝ 2 (GaussMeasure n)) :
    0 ≤ᵐ[GaussMeasure n] (v : EuclideanSpace ℝ (Fin n) → ℝ)
      ↔ ∀ φ : Lp ℝ 2 (GaussMeasure n),
          0 ≤ᵐ[GaussMeasure n] (φ : EuclideanSpace ℝ (Fin n) → ℝ) →
          0 ≤ ∫ x, (v : EuclideanSpace ℝ (Fin n) → ℝ) x
                * (φ : EuclideanSpace ℝ (Fin n) → ℝ) x ∂(GaussMeasure n) := by
  constructor
  · -- (1) ⇒ (2): the integrand is a.e. nonnegative
    intro hv φ hφ
    refine integral_nonneg_of_ae ?_
    filter_upwards [hv, hφ] with x hx hy using mul_nonneg hx hy
  · -- (2) ⇒ (1): test against the negative part of `v`
    intro H
    -- the negative part `w = max(-v, 0)` lies in `L²(γₙ)` because `|w| ≤ |v|`
    have hwm : AEStronglyMeasurable
        (fun x => max (-((v : EuclideanSpace ℝ (Fin n) → ℝ) x)) 0) (GaussMeasure n) :=
      (Lp.aestronglyMeasurable v).neg.sup aestronglyMeasurable_const
    have hwL : MemLp (fun x => max (-((v : EuclideanSpace ℝ (Fin n) → ℝ) x)) 0) 2
        (GaussMeasure n) := by
      refine MemLp.of_le (Lp.memLp v) hwm (Filter.Eventually.of_forall fun x => ?_)
      simp only [Real.norm_eq_abs]
      rw [abs_of_nonneg (le_max_right _ _)]
      exact max_le (neg_le_abs _) (abs_nonneg _)
    set w : Lp ℝ 2 (GaussMeasure n) := hwL.toLp _ with hwdef
    have hwc : (w : EuclideanSpace ℝ (Fin n) → ℝ)
        =ᵐ[GaussMeasure n] fun x => max (-((v : EuclideanSpace ℝ (Fin n) → ℝ) x)) 0 :=
      hwL.coeFn_toLp
    have hwnn : 0 ≤ᵐ[GaussMeasure n] (w : EuclideanSpace ℝ (Fin n) → ℝ) := by
      filter_upwards [hwc] with x hx
      rw [hx]
      exact le_max_right _ _
    -- the tested integral is the negative of the squared norm of `w`
    have hsq : Integrable
        (fun x => (fun y => max (-((v : EuclideanSpace ℝ (Fin n) → ℝ) y)) 0) x ^ 2)
        (GaussMeasure n) := hwL.integrable_sq
    have hptwise : (fun x => (v : EuclideanSpace ℝ (Fin n) → ℝ) x
          * (w : EuclideanSpace ℝ (Fin n) → ℝ) x)
        =ᵐ[GaussMeasure n]
        fun x => -((max (-((v : EuclideanSpace ℝ (Fin n) → ℝ) x)) 0) ^ 2) := by
      filter_upwards [hwc] with x hx
      rw [hx]
      rcases le_or_gt ((v : EuclideanSpace ℝ (Fin n) → ℝ) x) 0 with h | h
      · rw [max_eq_left (by linarith)]
        ring
      · rw [max_eq_right (by linarith)]
        ring
    have hH := H w hwnn
    rw [integral_congr_ae hptwise, integral_neg] at hH
    have hzero : ∫ x, (max (-((v : EuclideanSpace ℝ (Fin n) → ℝ) x)) 0) ^ 2
        ∂(GaussMeasure n) = 0 := by
      have hnn : (0 : ℝ) ≤ ∫ x, (max (-((v : EuclideanSpace ℝ (Fin n) → ℝ) x)) 0) ^ 2
          ∂(GaussMeasure n) :=
        integral_nonneg fun x => sq_nonneg _
      linarith
    have hae := (integral_eq_zero_iff_of_nonneg (fun x => sq_nonneg _) hsq).mp hzero
    filter_upwards [hae] with x hx
    have hx0 : max (-((v : EuclideanSpace ℝ (Fin n) → ℝ) x)) 0 = 0 := by
      have := hx
      simp only [Pi.zero_apply] at this
      exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp this
    have := max_le_iff.mp (le_of_eq hx0)
    simpa using this.1
