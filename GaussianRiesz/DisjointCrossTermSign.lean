import GaussianRiesz.BilinearEnergyFormula
import GaussianRiesz.EnergyFormBilinear
import GaussianRiesz.MehlerFormula
import GaussianRiesz.LatticeContraction
import GaussianRiesz.L2InnerGaussIntegral
open MeasureTheory
theorem DisjointCrossTermSign {n : ℕ} :
    (∀ v w : Lp ℝ 2 (GaussMeasure n), Energy v ≠ ⊤ → Energy w ≠ ⊤ →
        0 ≤ᵐ[GaussMeasure n] (v : EuclideanSpace ℝ (Fin n) → ℝ) →
        0 ≤ᵐ[GaussMeasure n] (w : EuclideanSpace ℝ (Fin n) → ℝ) →
        (∀ᵐ x ∂(GaussMeasure n), (v : EuclideanSpace ℝ (Fin n) → ℝ) x
          * (w : EuclideanSpace ℝ (Fin n) → ℝ) x = 0) →
        EnergyBil v w ≤ 0)
      ∧ (∀ z zm : Lp ℝ 2 (GaussMeasure n), Energy z ≠ ⊤ →
          (zm : EuclideanSpace ℝ (Fin n) → ℝ) =ᵐ[GaussMeasure n]
            (fun x => max (-(z : EuclideanSpace ℝ (Fin n) → ℝ) x) 0) →
          EnergyBil z zm ≤ -(Energy zm).toReal) := by
  classical
  obtain ⟨hmix, hdiag, hbil, hsub⟩ := EnergyFormBilinear (n := n)
  -- PART (1)
  have part1 : ∀ v w : Lp ℝ 2 (GaussMeasure n), Energy v ≠ ⊤ → Energy w ≠ ⊤ →
      0 ≤ᵐ[GaussMeasure n] (v : EuclideanSpace ℝ (Fin n) → ℝ) →
      0 ≤ᵐ[GaussMeasure n] (w : EuclideanSpace ℝ (Fin n) → ℝ) →
      (∀ᵐ x ∂(GaussMeasure n), (v : EuclideanSpace ℝ (Fin n) → ℝ) x
        * (w : EuclideanSpace ℝ (Fin n) → ℝ) x = 0) →
      EnergyBil v w ≤ 0 := by
    intro v w hv hw hv0 hw0 hvw
    -- disjointness kills the plain inner product
    have hzero : inner ℝ v w = (0 : ℝ) := by
      rw [L2InnerGaussIntegral]
      rw [integral_congr_ae (g := fun _ : EuclideanSpace ℝ (Fin n) => (0 : ℝ))
        (by filter_upwards [hvw] with x hx using hx)]
      simp
    -- positivity preservation makes the semigroup term nonnegative
    have hPs : ∀ s : ℝ, 0 < s → 0 ≤ inner ℝ (OUSemigroup s v) w := by
      intro s hs
      rw [L2InnerGaussIntegral]
      refine integral_nonneg_of_ae ?_
      filter_upwards [(MehlerFormula s hs v).2.2 hv0, hw0] with x h1 h2
      exact mul_nonneg h1 h2
    -- hence the integrand of the semigroup representation is nonpositive
    have hintegrand : ∀ s ∈ Set.Ioi (0 : ℝ),
        inner ℝ (v - OUSemigroup s v) w / s ^ ((3 : ℝ) / 2) ≤ 0 := by
      intro s hs
      have hs0 : (0 : ℝ) < s := hs
      have h1 : inner ℝ (v - OUSemigroup s v) w = -inner ℝ (OUSemigroup s v) w := by
        rw [inner_sub_left, hzero]; ring
      rw [h1]
      exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (hPs s hs0))
        (Real.rpow_nonneg (le_of_lt hs0) _)
    have hle : (∫ s in Set.Ioi (0 : ℝ),
        inner ℝ (v - OUSemigroup s v) w / s ^ ((3 : ℝ) / 2)) ≤ 0 := by
      refine integral_nonpos_of_ae ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
      exact hintegrand s hs
    rw [(BilinearEnergyFormula v w hv hw).2]
    have hc : (0 : ℝ) ≤ 1 / (2 * Real.sqrt Real.pi) := by positivity
    have := mul_le_mul_of_nonneg_left hle hc
    simpa using this
  refine ⟨part1, ?_⟩
  -- PART (2)
  intro z zm hz hzm
  -- the positive part of `z`, as an element of `L²(γₙ)`
  have hpm : AEStronglyMeasurable
      (fun x => max ((z : EuclideanSpace ℝ (Fin n) → ℝ) x) 0) (GaussMeasure n) :=
    (Lp.aestronglyMeasurable z).sup aestronglyMeasurable_const
  have hpL : MemLp (fun x => max ((z : EuclideanSpace ℝ (Fin n) → ℝ) x) 0) 2
      (GaussMeasure n) := by
    refine MemLp.of_le (Lp.memLp z) hpm (Filter.Eventually.of_forall fun x => ?_)
    simp only [Real.norm_eq_abs]
    rw [abs_of_nonneg (le_max_right _ _)]
    exact max_le (le_abs_self _) (abs_nonneg _)
  set zp : Lp ℝ 2 (GaussMeasure n) := hpL.toLp _ with hzpdef
  have hzpc : (zp : EuclideanSpace ℝ (Fin n) → ℝ)
      =ᵐ[GaussMeasure n] fun x => max ((z : EuclideanSpace ℝ (Fin n) → ℝ) x) 0 :=
    hpL.coeFn_toLp
  -- both parts lie in `𝒱`
  have hlip1 : LipschitzWith 1 (fun t : ℝ => max t 0) := by
    have h := (LipschitzWith.id (α := ℝ)).max (LipschitzWith.const (α := ℝ) (0 : ℝ))
    simpa [Function.id_def] using h
  have hlip2 : LipschitzWith 1 (fun t : ℝ => max (-t) 0) := by
    have h := ((LipschitzWith.id (α := ℝ)).neg).max (LipschitzWith.const (α := ℝ) (0 : ℝ))
    simpa [Function.id_def] using h
  have hzpV : Energy zp ≠ ⊤ :=
    (LatticeContraction (fun t : ℝ => max t 0) hlip1 (by simp) z zp hz hzpc).1
  have hzmV : Energy zm ≠ ⊤ :=
    (LatticeContraction (fun t : ℝ => max (-t) 0) hlip2 (by simp) z zm hz hzm).1
  have hnegV : Energy ((-1 : ℝ) • zm) ≠ ⊤ := (hsub zm zm (-1) hzmV hzmV).2
  -- `z = z⁺ - z⁻` in `L²(γₙ)`
  have hzeq : z = zp + (-1 : ℝ) • zm := by
    refine Lp.ext ?_
    filter_upwards [hzpc, hzm, Lp.coeFn_add zp ((-1 : ℝ) • zm),
      Lp.coeFn_smul (-1 : ℝ) zm] with x hp hm hadd hsm
    rw [hadd, Pi.add_apply, hsm, Pi.smul_apply, smul_eq_mul, hp, hm]
    rcases le_or_gt ((z : EuclideanSpace ℝ (Fin n) → ℝ) x) 0 with h | h
    · rw [max_eq_right h, max_eq_left (by linarith)]; ring
    · rw [max_eq_left (le_of_lt h), max_eq_right (by linarith)]; ring
  -- the two parts are nonnegative with vanishing product
  have hzpnn : 0 ≤ᵐ[GaussMeasure n] (zp : EuclideanSpace ℝ (Fin n) → ℝ) := by
    filter_upwards [hzpc] with x hx
    rw [hx]; exact le_max_right _ _
  have hzmnn : 0 ≤ᵐ[GaussMeasure n] (zm : EuclideanSpace ℝ (Fin n) → ℝ) := by
    filter_upwards [hzm] with x hx
    rw [hx]; exact le_max_right _ _
  have hprod : ∀ᵐ x ∂(GaussMeasure n), (zp : EuclideanSpace ℝ (Fin n) → ℝ) x
      * (zm : EuclideanSpace ℝ (Fin n) → ℝ) x = 0 := by
    filter_upwards [hzpc, hzm] with x hp hm
    rw [hp, hm]
    rcases le_or_gt ((z : EuclideanSpace ℝ (Fin n) → ℝ) x) 0 with h | h
    · rw [max_eq_right h]; ring
    · rw [max_eq_right (by linarith : -(z : EuclideanSpace ℝ (Fin n) → ℝ) x ≤ 0)]; ring
  -- expand bilinearly and use part (1) on the cross term
  have hexp : EnergyBil z zm = EnergyBil zp zm + (-1) * EnergyBil zm zm := by
    rw [hzeq, (hbil zp ((-1 : ℝ) • zm) zm 0 hzpV hnegV hzmV).1,
      (hbil zm zm zm (-1) hzmV hzmV hzmV).2.1]
  have hcross : EnergyBil zp zm ≤ 0 := part1 zp zm hzpV hzmV hzpnn hzmnn hprod
  rw [hexp, hdiag zm hzmV]
  linarith
