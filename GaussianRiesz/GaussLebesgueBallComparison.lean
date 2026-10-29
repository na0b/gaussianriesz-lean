module

public import GaussianRiesz.GaussMeasure

@[expose] public section
open MeasureTheory Metric
open scoped ENNReal
theorem GaussLebesgueBallComparison {n : ℕ} :
    (∀ E : Set (EuclideanSpace ℝ (Fin n)),
        GaussMeasure n E ≤ ENNReal.ofReal (Real.pi ^ (-(n : ℝ) / 2)) * volume E)
      ∧ (∀ (R : ℝ) (E : Set (EuclideanSpace ℝ (Fin n))), MeasurableSet E →
          E ⊆ closedBall 0 R →
          ENNReal.ofReal (Real.pi ^ (-(n : ℝ) / 2) * Real.exp (-R ^ 2)) * volume E
            ≤ GaussMeasure n E)
      ∧ (∀ (R ρ : ℝ) (x : EuclideanSpace ℝ (Fin n)), ‖x‖ ≤ R → 0 < ρ → ρ ≤ 2 →
          ENNReal.ofReal (Real.pi ^ (-(n : ℝ) / 2) * Real.exp (-(R + 2) ^ 2))
              * volume (closedBall x ρ)
            ≤ GaussMeasure n (closedBall x ρ))
      ∧ (∀ A : Set (EuclideanSpace ℝ (Fin n)), GaussMeasure n A = 0 ↔ volume A = 0) := by
  -- clause (2), proved first so that clause (3) can reuse it at `R := R + 2`
  have cl2 : ∀ (R : ℝ) (E : Set (EuclideanSpace ℝ (Fin n))), MeasurableSet E →
      E ⊆ closedBall 0 R →
      ENNReal.ofReal (Real.pi ^ (-(n : ℝ) / 2) * Real.exp (-R ^ 2)) * volume E
        ≤ GaussMeasure n E := by
    intro R E hE hER
    rw [GaussMeasure, withDensity_apply _ hE]
    calc ENNReal.ofReal (Real.pi ^ (-(n : ℝ) / 2) * Real.exp (-R ^ 2)) * volume E
        = ∫⁻ _ in E, ENNReal.ofReal (Real.pi ^ (-(n : ℝ) / 2) * Real.exp (-R ^ 2)) := by
          rw [setLIntegral_const]
      _ ≤ ∫⁻ x in E, ENNReal.ofReal (Real.pi ^ (-(n : ℝ) / 2) * Real.exp (-‖x‖ ^ 2)) := by
          refine setLIntegral_mono' hE fun x hx => ?_
          refine ENNReal.ofReal_le_ofReal ?_
          have hxR : ‖x‖ ≤ R := by
            have := hER hx
            simpa [Metric.mem_closedBall, dist_zero_right] using this
          have hsq : -R ^ 2 ≤ -‖x‖ ^ 2 := by
            have h0 : (0:ℝ) ≤ ‖x‖ := norm_nonneg x
            nlinarith
          have hp : (0:ℝ) < Real.pi ^ (-(n : ℝ) / 2) := Real.rpow_pos_of_pos Real.pi_pos _
          exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 hsq) hp.le
  refine ⟨?_, cl2, ?_, ?_⟩
  · -- clause (1): the global upper comparison, at the MEASURE level so that it
    -- holds for an arbitrary (not necessarily measurable) set
    intro E
    have hmono : GaussMeasure n
        ≤ ENNReal.ofReal (Real.pi ^ (-(n : ℝ) / 2))
            • (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
      rw [GaussMeasure, ← withDensity_const]
      refine withDensity_mono (Filter.Eventually.of_forall fun x => ?_)
      refine ENNReal.ofReal_le_ofReal ?_
      have hp : (0:ℝ) < Real.pi ^ (-(n : ℝ) / 2) := Real.rpow_pos_of_pos Real.pi_pos _
      nlinarith [Real.exp_le_one_iff.2 (neg_nonpos.2 (sq_nonneg ‖x‖)), Real.exp_pos (-‖x‖ ^ 2)]
    simpa using hmono E
  · -- clause (3): clause (2) at `R := R + 2` with `E := closedBall x ρ`
    intro R ρ x hx hρ hρ2
    refine cl2 (R + 2) _ measurableSet_closedBall ?_
    intro y hy
    have hxy : dist y x ≤ ρ := by simpa [Metric.mem_closedBall] using hy
    have hny : ‖y‖ ≤ ‖x‖ + ρ := by
      have h1 := norm_sub_norm_le y x
      have hd : ‖y - x‖ ≤ ρ := by simpa [dist_eq_norm] using hxy
      linarith
    simp only [Metric.mem_closedBall, dist_zero_right]
    linarith
  · -- clause (4): the null-set equivalence, for an arbitrary set
    intro A
    have hdens : AEMeasurable
        (fun x : EuclideanSpace ℝ (Fin n) =>
          ENNReal.ofReal (Real.pi ^ (-(n : ℝ) / 2) * Real.exp (-‖x‖ ^ 2))) volume := by
      refine (Measurable.ennreal_ofReal ?_).aemeasurable
      exact (measurable_const.mul ((measurable_neg.comp
        ((continuous_norm (E := EuclideanSpace ℝ (Fin n))).measurable.pow_const 2)).exp))
    have hpos : ∀ x : EuclideanSpace ℝ (Fin n),
        ENNReal.ofReal (Real.pi ^ (-(n : ℝ) / 2) * Real.exp (-‖x‖ ^ 2)) ≠ 0 := by
      intro x
      simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]
      exact mul_pos (Real.rpow_pos_of_pos Real.pi_pos _) (Real.exp_pos _)
    rw [GaussMeasure, withDensity_apply_eq_zero' hdens]
    have hset : {x : EuclideanSpace ℝ (Fin n) |
        ENNReal.ofReal (Real.pi ^ (-(n : ℝ) / 2) * Real.exp (-‖x‖ ^ 2)) ≠ 0} = Set.univ :=
      Set.eq_univ_of_forall fun x => hpos x
    rw [hset, Set.univ_inter]
