module

public import GaussianRiesz.HermiteFun
public import GaussianRiesz.GaussIsProb

@[expose] public section
open MeasureTheory
theorem HermiteFunMemLp {n : ℕ} (α : Fin n → ℕ) :
    MemLp (HermiteFun α) 2 (GaussMeasure n) := by
  classical
  -- (0) one-variable integrability: any polynomial in `√2 s` against the Gaussian weight
  have hint0 : ∀ m : ℕ, Integrable (fun s : ℝ => s ^ m * Real.exp (-s ^ 2)) := by
    intro m
    have h := integrable_rpow_mul_exp_neg_mul_sq (b := (1 : ℝ)) one_pos (s := (m : ℝ))
      (lt_of_lt_of_le (by norm_num) (Nat.cast_nonneg m))
    simpa [Real.rpow_natCast] using h
  have hintP : ∀ q : Polynomial ℤ,
      Integrable (fun s : ℝ => Polynomial.aeval (Real.sqrt 2 * s) q * Real.exp (-s ^ 2)) := by
    intro q
    refine Polynomial.induction_on' q (fun p r hp hr => ?_) (fun m a => ?_)
    · refine (hp.add hr).congr (Filter.Eventually.of_forall fun s => ?_)
      simp only [Pi.add_apply, map_add]
      ring
    · have hre : (fun s : ℝ => Polynomial.aeval (Real.sqrt 2 * s)
            (Polynomial.monomial m a) * Real.exp (-s ^ 2))
          = fun s : ℝ => ((a : ℝ) * Real.sqrt 2 ^ m) * (s ^ m * Real.exp (-s ^ 2)) := by
        funext s
        simp [Polynomial.aeval_monomial, mul_pow]
        ring
      rw [hre]
      exact (hint0 m).const_mul _
  -- (1) each one-variable factor is integrable against the one-dimensional Gaussian weight
  have hfac : ∀ k : ℕ, Integrable (fun s : ℝ => Real.pi ^ (-(1 : ℝ) / 2)
      * Real.exp (-s ^ 2) * (Hermite1 k s) ^ 2) := by
    intro k
    have hre : (fun s : ℝ => Real.pi ^ (-(1 : ℝ) / 2) * Real.exp (-s ^ 2) * (Hermite1 k s) ^ 2)
        = fun s : ℝ => (Real.pi ^ (-(1 : ℝ) / 2) / (Nat.factorial k : ℝ))
          * (Polynomial.aeval (Real.sqrt 2 * s) (Polynomial.hermite k ^ 2)
              * Real.exp (-s ^ 2)) := by
      funext s
      simp only [Hermite1, div_pow, map_pow]
      rw [Real.sq_sqrt (by positivity : (0 : ℝ) ≤ (Nat.factorial k : ℝ))]
      ring
    rw [hre]
    exact (hintP _).const_mul _
  -- (2) continuity, hence measurability
  have hc1 : ∀ k : ℕ, Continuous (Hermite1 k) := by
    intro k
    unfold Hermite1
    exact ((Polynomial.continuous_aeval (Polynomial.hermite k)).comp
      (continuous_const.mul continuous_id)).div_const _
  have hcF : Continuous (HermiteFun α) := by
    unfold HermiteFun
    exact continuous_finsetProd _ fun j _ =>
      (hc1 (α j)).comp (EuclideanSpace.proj (𝕜 := ℝ) j).continuous
  -- (3) reduce `MemLp _ 2` to integrability of the square
  rw [memLp_two_iff_integrable_sq hcF.aestronglyMeasurable]
  -- (4) pass from `γₙ` to Lebesgue measure with the explicit density
  have hdm : Measurable (fun x : EuclideanSpace ℝ (Fin n) =>
      ENNReal.ofReal (Real.pi ^ (-(n : ℝ) / 2) * Real.exp (-‖x‖ ^ 2))) := by fun_prop
  have hfin : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
      ENNReal.ofReal (Real.pi ^ (-(n : ℝ) / 2) * Real.exp (-‖x‖ ^ 2)) < ⊤ :=
    Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top
  rw [GaussMeasure, integrable_withDensity_iff hdm hfin]
  -- (5) the weighted square factorizes over the coordinates
  have hcoord : ∀ x : EuclideanSpace ℝ (Fin n),
      HermiteFun α x ^ 2
          * (ENNReal.ofReal (Real.pi ^ (-(n : ℝ) / 2) * Real.exp (-‖x‖ ^ 2))).toReal
        = ∏ j, (Real.pi ^ (-(1 : ℝ) / 2) * Real.exp (-(x j) ^ 2)
            * (Hermite1 (α j) (x j)) ^ 2) := by
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
          * (∏ j, (Hermite1 (α j) (x j)) ^ 2)
        = ∏ j, (Real.pi ^ (-(1 : ℝ) / 2) * Real.exp (-(x j) ^ 2)
            * (Hermite1 (α j) (x j)) ^ 2) := by
      rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    rw [ENNReal.toReal_ofReal (by positivity), HermiteFun, hpi, hexp,
      ← Finset.prod_pow, ← hsplit]
    ring
  rw [integrable_congr (Filter.Eventually.of_forall hcoord)]
  -- (6) transport to `Fin n → ℝ` and apply the product criterion
  rw [← (PiLp.volume_preserving_toLp (Fin n)).integrable_comp_emb
        (MeasurableEquiv.toLp 2 _).measurableEmbedding, volume_pi]
  exact Integrable.fintype_prod (fun j => hfac (α j))
