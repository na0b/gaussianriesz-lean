module

public import GaussianRiesz.Hermite1Reproduction
public import GaussianRiesz.HermiteFun
public import GaussianRiesz.GaussMeasure

@[expose] public section
open MeasureTheory
theorem HermiteFunReproduction {n : ℕ} (a : ℝ) (ha0 : (0:ℝ) ≤ a) (ha1 : a ≤ 1)
    (α : Fin n → ℕ) (x : EuclideanSpace ℝ (Fin n)) :
    ∫ y, HermiteFun α (a • x + Real.sqrt (1 - a ^ 2) • y) ∂(GaussMeasure n)
      = a ^ (MultiIndexSum α) * HermiteFun α x := by
  have hdm : Measurable (fun z : EuclideanSpace ℝ (Fin n) =>
      ENNReal.ofReal (Real.pi ^ (-(n : ℝ) / 2) * Real.exp (-‖z‖ ^ 2))) := by fun_prop
  have hfin : ∀ᵐ z ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
      ENNReal.ofReal (Real.pi ^ (-(n : ℝ) / 2) * Real.exp (-‖z‖ ^ 2)) < ⊤ :=
    Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top
  rw [GaussMeasure, integral_withDensity_eq_integral_toReal_smul hdm hfin]
  have hcoord : ∀ y : EuclideanSpace ℝ (Fin n),
      (ENNReal.ofReal (Real.pi ^ (-(n : ℝ) / 2) * Real.exp (-‖y‖ ^ 2))).toReal
          • HermiteFun α (a • x + Real.sqrt (1 - a ^ 2) • y)
        = ∏ j, (Real.pi ^ (-(1 : ℝ) / 2) * Real.exp (-(y j) ^ 2)
            * Hermite1 (α j) (a * x j + Real.sqrt (1 - a ^ 2) * (y j))) := by
    intro y
    have hnorm : ‖y‖ ^ 2 = ∑ j, (y j) ^ 2 := by
      rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity)]
      exact Finset.sum_congr rfl fun j _ => by rw [Real.norm_eq_abs, sq_abs]
    have hpi : Real.pi ^ (-(n : ℝ) / 2) = ∏ _j : Fin n, Real.pi ^ (-(1 : ℝ) / 2) := by
      rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin,
        ← Real.rpow_natCast (Real.pi ^ (-(1 : ℝ) / 2)) n,
        ← Real.rpow_mul Real.pi_pos.le]
      ring_nf
    have hexp : Real.exp (-‖y‖ ^ 2) = ∏ j, Real.exp (-(y j) ^ 2) := by
      rw [hnorm, ← Real.exp_sum, ← Finset.sum_neg_distrib]
    have hH : HermiteFun α (a • x + Real.sqrt (1 - a ^ 2) • y)
        = ∏ j, Hermite1 (α j) (a * x j + Real.sqrt (1 - a ^ 2) * (y j)) := by
      rw [HermiteFun]
      refine Finset.prod_congr rfl fun j _ => ?_
      congr 1
    rw [smul_eq_mul, ENNReal.toReal_ofReal (by positivity), hpi, hexp, hH,
      ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  rw [integral_congr_ae (Filter.Eventually.of_forall hcoord)]
  rw [← (PiLp.volume_preserving_toLp (Fin n)).integral_comp
        (MeasurableEquiv.toLp 2 _).measurableEmbedding, volume_pi,
    integral_fintype_prod_eq_prod (fun j s => Real.pi ^ (-(1 : ℝ) / 2) * Real.exp (-s ^ 2)
      * Hermite1 (α j) (a * x j + Real.sqrt (1 - a ^ 2) * s))]
  simp_rw [Hermite1Reproduction _ a _ ha0 ha1]
  rw [Finset.prod_mul_distrib, MultiIndexSum, HermiteFun, ← Finset.prod_pow_eq_pow_sum]
