module

public import GaussianRiesz.HermiteL2
public import GaussianRiesz.Hermite1Orthonormal

@[expose] public section
open MeasureTheory
theorem HermiteL2Orthonormal (n : ℕ) : Orthonormal ℝ (HermiteL2 (n := n)) := by
  classical
  rw [orthonormal_iff_ite]
  intro α β
  -- (1) the inner product is the Gaussian integral of the product of the two Hermite functions
  have hI : inner ℝ (HermiteL2 α) (HermiteL2 β)
      = ∫ x, HermiteFun α x * HermiteFun β x ∂(GaussMeasure n) := by
    rw [L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [MemLp.coeFn_toLp (HermiteFunMemLp α),
      MemLp.coeFn_toLp (HermiteFunMemLp β)] with x hx hy
    rw [show ((HermiteL2 α : Lp ℝ 2 (GaussMeasure n)) :
        EuclideanSpace ℝ (Fin n) → ℝ) x = HermiteFun α x from hx,
      show ((HermiteL2 β : Lp ℝ 2 (GaussMeasure n)) :
        EuclideanSpace ℝ (Fin n) → ℝ) x = HermiteFun β x from hy]
    simp only [RCLike.inner_apply, conj_trivial]
    ring
  rw [hI]
  -- (2) move to Lebesgue measure against the explicit Gaussian density
  have hdm : Measurable (fun x : EuclideanSpace ℝ (Fin n) =>
      ENNReal.ofReal (Real.pi ^ (-(n : ℝ) / 2) * Real.exp (-‖x‖ ^ 2))) := by fun_prop
  have hfin : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
      ENNReal.ofReal (Real.pi ^ (-(n : ℝ) / 2) * Real.exp (-‖x‖ ^ 2)) < ⊤ :=
    Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top
  rw [GaussMeasure, integral_withDensity_eq_integral_toReal_smul hdm hfin]
  -- (3) the weighted integrand factorizes over the coordinates
  have hcoord : ∀ x : EuclideanSpace ℝ (Fin n),
      (ENNReal.ofReal (Real.pi ^ (-(n : ℝ) / 2) * Real.exp (-‖x‖ ^ 2))).toReal
          • (HermiteFun α x * HermiteFun β x)
        = ∏ j, (Real.pi ^ (-(1 : ℝ) / 2) * Real.exp (-(x j) ^ 2)
            * (Hermite1 (α j) (x j) * Hermite1 (β j) (x j))) := by
    intro x
    have hnorm : ‖x‖ ^ 2 = ∑ j, (x j) ^ 2 := by
      rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity)]
      exact Finset.sum_congr rfl fun j _ => by rw [Real.norm_eq_abs, sq_abs]
    have hpi : Real.pi ^ (-(n : ℝ) / 2) = ∏ _j : Fin n, Real.pi ^ (-(1 : ℝ) / 2) := by
      rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin,
        ← Real.rpow_natCast (Real.pi ^ (-(1 : ℝ) / 2)) n,
        ← Real.rpow_mul Real.pi_pos.le]
      ring_nf
    have hexp : Real.exp (-‖x‖ ^ 2) = ∏ j, Real.exp (-(x j) ^ 2) := by
      rw [hnorm, ← Real.exp_sum, ← Finset.sum_neg_distrib]
    have hsplit : (∏ _j : Fin n, Real.pi ^ (-(1 : ℝ) / 2)) * (∏ j, Real.exp (-(x j) ^ 2))
          * ((∏ j, Hermite1 (α j) (x j)) * (∏ j, Hermite1 (β j) (x j)))
        = ∏ j, (Real.pi ^ (-(1 : ℝ) / 2) * Real.exp (-(x j) ^ 2)
            * (Hermite1 (α j) (x j) * Hermite1 (β j) (x j))) := by
      rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    rw [smul_eq_mul, ENNReal.toReal_ofReal (by positivity), HermiteFun, HermiteFun,
      hpi, hexp, hsplit]
  rw [integral_congr_ae (Filter.Eventually.of_forall hcoord)]
  -- (4) tensorization: transport to `Fin n → ℝ` and split the product integral
  rw [← (PiLp.volume_preserving_toLp (Fin n)).integral_comp
        (MeasurableEquiv.toLp 2 _).measurableEmbedding, volume_pi,
    integral_fintype_prod_eq_prod (fun j s => Real.pi ^ (-(1 : ℝ) / 2) * Real.exp (-s ^ 2)
      * (Hermite1 (α j) s * Hermite1 (β j) s))]
  -- (5) each one-dimensional factor is the Kronecker delta
  simp_rw [Hermite1Orthonormal]
  -- (6) a product of Kronecker deltas is the Kronecker delta of the multi-indices
  by_cases hab : α = β
  · subst hab; simp
  · rw [if_neg hab]
    obtain ⟨j, hj⟩ := Function.ne_iff.mp hab
    exact Finset.prod_eq_zero (Finset.mem_univ j) (if_neg hj)
