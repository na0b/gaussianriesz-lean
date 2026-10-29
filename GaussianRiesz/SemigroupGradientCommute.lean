module

public import GaussianRiesz.MehlerFormula

@[expose] public section
open MeasureTheory
theorem SemigroupGradientCommute {n : ℕ} (s : ℝ) (hs : 0 < s)
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hfc : HasCompactSupport f) (j : Fin n) :
    (∀ x : EuclideanSpace ℝ (Fin n),
        Integrable (fun z : EuclideanSpace ℝ (Fin n) =>
          f (Real.exp (-s) • x + Real.sqrt (1 - Real.exp (-2 * s)) • z)) (GaussMeasure n))
      ∧ (∀ x : EuclideanSpace ℝ (Fin n),
          Integrable (fun z : EuclideanSpace ℝ (Fin n) =>
            fderiv ℝ f (Real.exp (-s) • x + Real.sqrt (1 - Real.exp (-2 * s)) • z)
              (EuclideanSpace.single j (1 : ℝ))) (GaussMeasure n))
      ∧ Continuous (fun x : EuclideanSpace ℝ (Fin n) =>
          ∫ z, fderiv ℝ f (Real.exp (-s) • x + Real.sqrt (1 - Real.exp (-2 * s)) • z)
            (EuclideanSpace.single j (1 : ℝ)) ∂(GaussMeasure n))
      ∧ (∀ x : EuclideanSpace ℝ (Fin n),
          DifferentiableAt ℝ (fun w : EuclideanSpace ℝ (Fin n) =>
            ∫ z, f (Real.exp (-s) • w + Real.sqrt (1 - Real.exp (-2 * s)) • z)
              ∂(GaussMeasure n)) x
          ∧ fderiv ℝ (fun w : EuclideanSpace ℝ (Fin n) =>
                ∫ z, f (Real.exp (-s) • w + Real.sqrt (1 - Real.exp (-2 * s)) • z)
                  ∂(GaussMeasure n)) x (EuclideanSpace.single j (1 : ℝ))
              = Real.exp (-s) *
                  ∫ z, fderiv ℝ f (Real.exp (-s) • x
                      + Real.sqrt (1 - Real.exp (-2 * s)) • z)
                    (EuclideanSpace.single j (1 : ℝ)) ∂(GaussMeasure n)) := by
  have hprob : IsProbabilityMeasure (GaussMeasure n) := GaussIsProb n
  have hfcont : Continuous f := hf.continuous
  have hfd : Continuous (fderiv ℝ f) := hf.continuous_fderiv (by simp)
  have hfdcs : HasCompactSupport (fderiv ℝ f) := hfc.fderiv ℝ
  obtain ⟨M, hM⟩ : ∃ M : ℝ, ∀ y, ‖f y‖ ≤ M := by
    obtain ⟨M, hMb⟩ := (hfc.isCompact_range hfcont).isBounded.subset_closedBall 0
    exact ⟨M, fun y => by simpa using hMb (Set.mem_range_self y)⟩
  obtain ⟨N, hN⟩ : ∃ N : ℝ, ∀ y, ‖fderiv ℝ f y‖ ≤ N := by
    obtain ⟨N, hNb⟩ := (hfdcs.isCompact_range hfd).isBounded.subset_closedBall 0
    exact ⟨N, fun y => by simpa using hNb (Set.mem_range_self y)⟩
  have haff : ∀ x : EuclideanSpace ℝ (Fin n),
      Continuous (fun z : EuclideanSpace ℝ (Fin n) =>
        Real.exp (-s) • x + Real.sqrt (1 - Real.exp (-2 * s)) • z) := by
    intro x; fun_prop
  -- clause (1)
  have c1 : ∀ x : EuclideanSpace ℝ (Fin n),
      Integrable (fun z : EuclideanSpace ℝ (Fin n) =>
        f (Real.exp (-s) • x + Real.sqrt (1 - Real.exp (-2 * s)) • z)) (GaussMeasure n) := by
    intro x
    refine Integrable.mono' (integrable_const M)
      ((hfcont.comp (haff x)).aestronglyMeasurable) ?_
    exact Filter.Eventually.of_forall fun z => hM _
  -- clause (2)
  have c2 : ∀ x : EuclideanSpace ℝ (Fin n),
      Integrable (fun z : EuclideanSpace ℝ (Fin n) =>
        fderiv ℝ f (Real.exp (-s) • x + Real.sqrt (1 - Real.exp (-2 * s)) • z)
          (EuclideanSpace.single j (1 : ℝ))) (GaussMeasure n) := by
    intro x
    refine Integrable.mono' (integrable_const (N * ‖EuclideanSpace.single j (1 : ℝ)‖))
      (((hfd.comp (haff x)).clm_apply continuous_const).aestronglyMeasurable) ?_
    refine Filter.Eventually.of_forall fun z => ?_
    exact (ContinuousLinearMap.le_opNorm _ _).trans
      (mul_le_mul_of_nonneg_right (hN _) (norm_nonneg _))
  refine ⟨c1, c2, ?_, ?_⟩
  · -- clause (3)
    refine continuous_of_dominated
      (fun x => ((hfd.comp (haff x)).clm_apply continuous_const).aestronglyMeasurable)
      (fun x => Filter.Eventually.of_forall fun z =>
        (ContinuousLinearMap.le_opNorm _ _).trans
          (mul_le_mul_of_nonneg_right (hN _) (norm_nonneg _)))
      (integrable_const (N * ‖EuclideanSpace.single j (1 : ℝ)‖)) ?_
    refine Filter.Eventually.of_forall fun z => ?_
    exact (hfd.comp (by fun_prop)).clm_apply continuous_const
  · -- clause (4)
    intro x
    set r : ℝ := Real.exp (-s) with hrdef
    set tau : ℝ := Real.sqrt (1 - Real.exp (-2 * s)) with htaudef
    set A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) :=
      r • ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n)) with hAdef
    have hdifff : ∀ y : EuclideanSpace ℝ (Fin n),
        HasFDerivAt f (fderiv ℝ f y) y :=
      fun y => (hf.differentiable (by simp) y).hasFDerivAt
    have haffd : ∀ w z : EuclideanSpace ℝ (Fin n),
        HasFDerivAt (fun w : EuclideanSpace ℝ (Fin n) => r • w + tau • z) A w := by
      intro w z
      simpa [hAdef] using (((hasFDerivAt_id w).const_smul r).add_const (tau • z))
    have hchain : ∀ w z : EuclideanSpace ℝ (Fin n),
        HasFDerivAt (fun w : EuclideanSpace ℝ (Fin n) => f (r • w + tau • z))
          ((fderiv ℝ f (r • w + tau • z)).comp A) w :=
      fun w z => (hdifff _).comp w (haffd w z)
    have hF'cont : ∀ w : EuclideanSpace ℝ (Fin n),
        Continuous (fun z : EuclideanSpace ℝ (Fin n) =>
          (fderiv ℝ f (r • w + tau • z)).comp A) :=
      fun w => (hfd.comp (haff w)).clm_comp continuous_const
    have hbd : ∀ w z : EuclideanSpace ℝ (Fin n),
        ‖(fderiv ℝ f (r • w + tau • z)).comp A‖ ≤ N * ‖A‖ :=
      fun w z => (ContinuousLinearMap.opNorm_comp_le _ _).trans
        (mul_le_mul_of_nonneg_right (hN _) (norm_nonneg _))
    have hF'int : Integrable
        (fun z : EuclideanSpace ℝ (Fin n) => (fderiv ℝ f (r • x + tau • z)).comp A)
        (GaussMeasure n) :=
      Integrable.mono' (integrable_const (N * ‖A‖)) (hF'cont x).aestronglyMeasurable
        (Filter.Eventually.of_forall fun z => hbd x z)
    have key : HasFDerivAt
        (fun w : EuclideanSpace ℝ (Fin n) =>
          ∫ z, f (r • w + tau • z) ∂(GaussMeasure n))
        (∫ z, (fderiv ℝ f (r • x + tau • z)).comp A ∂(GaussMeasure n)) x := by
      refine hasFDerivAt_integral_of_dominated_of_fderiv_le
        (bound := fun _ => N * ‖A‖) (s := Set.univ) Filter.univ_mem
        (Filter.Eventually.of_forall fun w => (hfcont.comp (haff w)).aestronglyMeasurable)
        (c1 x) (hF'cont x).aestronglyMeasurable
        (Filter.Eventually.of_forall fun z w _ => hbd w z)
        (integrable_const _)
        (Filter.Eventually.of_forall fun z w _ => hchain w z)
    refine ⟨key.differentiableAt, ?_⟩
    rw [key.fderiv, ContinuousLinearMap.integral_apply hF'int]
    have happ : ∀ z : EuclideanSpace ℝ (Fin n),
        ((fderiv ℝ f (r • x + tau • z)).comp A) (EuclideanSpace.single j (1 : ℝ))
          = r * fderiv ℝ f (r • x + tau • z) (EuclideanSpace.single j (1 : ℝ)) := by
      intro z
      simp [hAdef]
    simp_rw [happ]
    rw [integral_const_mul]
