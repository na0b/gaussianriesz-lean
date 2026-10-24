import GaussianRiesz.SemigroupGradientCommute
import GaussianRiesz.GaussIsProb
import GaussianRiesz.SubordinationWeightIntegral
open MeasureTheory
theorem MehlerGradientSubordination {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hfc : HasCompactSupport f) (j : Fin n) :
    (∀ x : EuclideanSpace ℝ (Fin n),
        IntegrableOn (fun s : ℝ => (Real.sqrt s)⁻¹ * (Real.exp (-s) *
          ((Real.sqrt 2)⁻¹ * ∫ z, fderiv ℝ f (Real.exp (-s) • x
              + Real.sqrt (1 - Real.exp (-2 * s)) • z)
            (EuclideanSpace.single j (1 : ℝ)) ∂(GaussMeasure n))))
          (Set.Ioi (0 : ℝ)))
      ∧ Continuous (fun x : EuclideanSpace ℝ (Fin n) =>
          (Real.sqrt Real.pi)⁻¹ * ∫ s in Set.Ioi (0 : ℝ), (Real.sqrt s)⁻¹ * (Real.exp (-s) *
            ((Real.sqrt 2)⁻¹ * ∫ z, fderiv ℝ f (Real.exp (-s) • x
                + Real.sqrt (1 - Real.exp (-2 * s)) • z)
              (EuclideanSpace.single j (1 : ℝ)) ∂(GaussMeasure n)))) := by
  have hprob : IsProbabilityMeasure (GaussMeasure n) := GaussIsProb n
  -- Step 0: the sup-norm bound on the gradient of `f`.  `fderiv ℝ f` is continuous
  -- because `f` is smooth, and compactly supported because `f` is, so its norm is
  -- bounded; this is the paper's `‖Df‖_∞ < ∞`.  Note the use of `hf` here is what makes
  -- `fderiv ℝ f` an honest derivative rather than a junk value (pm-0013).
  have hfd : Continuous (fderiv ℝ f) := hf.continuous_fderiv (by simp)
  have hfdcs : HasCompactSupport (fderiv ℝ f) := hfc.fderiv ℝ
  obtain ⟨N, hN⟩ : ∃ N : ℝ, ∀ y, ‖fderiv ℝ f y‖ ≤ N := by
    obtain ⟨N, hNb⟩ := (hfdcs.isCompact_range hfd).isBounded.subset_closedBall 0
    exact ⟨N, fun y => by simpa using hNb (Set.mem_range_self y)⟩
  have hNd : ∀ y : EuclideanSpace ℝ (Fin n),
      ‖fderiv ℝ f y (EuclideanSpace.single j (1 : ℝ))‖ ≤ N := by
    intro y
    calc ‖fderiv ℝ f y (EuclideanSpace.single j (1 : ℝ))‖
        ≤ ‖fderiv ℝ f y‖ * ‖EuclideanSpace.single j (1 : ℝ)‖ := ContinuousLinearMap.le_opNorm _ _
      _ = ‖fderiv ℝ f y‖ := by rw [PiLp.norm_single]; simp
      _ ≤ N := hN y
  have hN0 : (0 : ℝ) ≤ N := le_trans (norm_nonneg _) (hNd 0)
  -- `γₙ` is a probability measure, so the Mehler average inherits the same bound with
  -- no estimate of its own.
  have hGbd : ∀ (s : ℝ) (x : EuclideanSpace ℝ (Fin n)),
      ‖∫ z, fderiv ℝ f (Real.exp (-s) • x + Real.sqrt (1 - Real.exp (-2 * s)) • z)
        (EuclideanSpace.single j (1 : ℝ)) ∂(GaussMeasure n)‖ ≤ N := by
    intro s x
    have h : ‖∫ z, fderiv ℝ f (Real.exp (-s) • x + Real.sqrt (1 - Real.exp (-2 * s)) • z)
          (EuclideanSpace.single j (1 : ℝ)) ∂(GaussMeasure n)‖
        ≤ N * Measure.real (GaussMeasure n) Set.univ :=
      norm_integral_le_of_norm_le_const (Filter.Eventually.of_forall fun z => hNd _)
    simpa using h
  -- Joint continuity of the Mehler average in `(s, x)`, by dominated convergence with
  -- the constant dominating function `N`.  The affine map is continuous in `(s, x, z)`
  -- jointly and `fderiv ℝ f` is continuous, so nothing here is specific to `s > 0`.
  have hjoint : Continuous (fun p : ℝ × EuclideanSpace ℝ (Fin n) =>
      ∫ z, fderiv ℝ f (Real.exp (-p.1) • p.2 + Real.sqrt (1 - Real.exp (-2 * p.1)) • z)
        (EuclideanSpace.single j (1 : ℝ)) ∂(GaussMeasure n)) := by
    refine continuous_of_dominated (bound := fun _ => N) (fun p => ?_)
      (fun p => Filter.Eventually.of_forall fun z => hNd _) (integrable_const N)
      (Filter.Eventually.of_forall fun z => ?_)
    · exact Continuous.aestronglyMeasurable ((hfd.comp (by fun_prop)).clm_apply continuous_const)
    · exact (hfd.comp (by fun_prop)).clm_apply continuous_const
  have hG_s : ∀ x : EuclideanSpace ℝ (Fin n), Continuous (fun s : ℝ =>
      ∫ z, fderiv ℝ f (Real.exp (-s) • x + Real.sqrt (1 - Real.exp (-2 * s)) • z)
        (EuclideanSpace.single j (1 : ℝ)) ∂(GaussMeasure n)) := fun x =>
    hjoint.comp (by fun_prop : Continuous fun s : ℝ => (s, x))
  have hG_x : ∀ s : ℝ, Continuous (fun x : EuclideanSpace ℝ (Fin n) =>
      ∫ z, fderiv ℝ f (Real.exp (-s) • x + Real.sqrt (1 - Real.exp (-2 * s)) • z)
        (EuclideanSpace.single j (1 : ℝ)) ∂(GaussMeasure n)) := fun s =>
    hjoint.comp (by fun_prop : Continuous fun x : EuclideanSpace ℝ (Fin n) => (s, x))
  -- Step 1 is `SubordinationWeightIntegral`: the scalar weight is integrable on `(0,∞)`.
  have hdomint : IntegrableOn (fun s : ℝ =>
      (Real.sqrt 2)⁻¹ * N * ((Real.sqrt s)⁻¹ * Real.exp (-s))) (Set.Ioi (0 : ℝ)) :=
    SubordinationWeightIntegral.1.const_mul _
  -- measurability in `s`, for each fixed `x`
  have hmeasx : ∀ x : EuclideanSpace ℝ (Fin n),
      Measurable (fun s : ℝ => (Real.sqrt s)⁻¹ * (Real.exp (-s) *
        ((Real.sqrt 2)⁻¹ * ∫ z, fderiv ℝ f (Real.exp (-s) • x
            + Real.sqrt (1 - Real.exp (-2 * s)) • z)
          (EuclideanSpace.single j (1 : ℝ)) ∂(GaussMeasure n)))) := fun x =>
    (Real.continuous_sqrt.measurable.inv).mul
      (((Real.continuous_exp.comp continuous_neg).measurable).mul
        (measurable_const.mul (hG_s x).measurable))
  -- the pointwise majorant, uniform in `x`
  have hptbd : ∀ (x : EuclideanSpace ℝ (Fin n)) (s : ℝ), 0 < s →
      ‖(Real.sqrt s)⁻¹ * (Real.exp (-s) *
        ((Real.sqrt 2)⁻¹ * ∫ z, fderiv ℝ f (Real.exp (-s) • x
            + Real.sqrt (1 - Real.exp (-2 * s)) • z)
          (EuclideanSpace.single j (1 : ℝ)) ∂(GaussMeasure n)))‖
        ≤ (Real.sqrt 2)⁻¹ * N * ((Real.sqrt s)⁻¹ * Real.exp (-s)) := by
    intro x s hs
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_mul, abs_inv, abs_inv,
      abs_of_nonneg (Real.sqrt_nonneg s), abs_of_nonneg (Real.sqrt_nonneg 2),
      abs_of_pos (Real.exp_pos _)]
    have h1 : |∫ z, fderiv ℝ f (Real.exp (-s) • x
          + Real.sqrt (1 - Real.exp (-2 * s)) • z)
        (EuclideanSpace.single j (1 : ℝ)) ∂(GaussMeasure n)| ≤ N := by
      simpa [Real.norm_eq_abs] using hGbd s x
    have h2 : (0 : ℝ) ≤ (Real.sqrt s)⁻¹ := by positivity
    have h3 : (0 : ℝ) ≤ (Real.sqrt 2)⁻¹ := by positivity
    have h4 : (0 : ℝ) < Real.exp (-s) := Real.exp_pos _
    nlinarith [mul_le_mul_of_nonneg_left h1 (mul_nonneg (mul_nonneg h2 h4.le) h3)]
  refine ⟨fun x => ?_, ?_⟩
  · -- clause (1)
    refine Integrable.mono' hdomint ((hmeasx x).aestronglyMeasurable.restrict) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    exact hptbd x s hs
  · -- clause (2): dominated continuity, with the same `x`-independent majorant
    refine Continuous.const_mul ?_ _
    refine continuous_of_dominated
      (bound := fun s : ℝ => (Real.sqrt 2)⁻¹ * N * ((Real.sqrt s)⁻¹ * Real.exp (-s)))
      (fun x => (hmeasx x).aestronglyMeasurable.restrict) (fun x => ?_) hdomint ?_
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
      exact hptbd x s hs
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
      exact (((hG_x s).const_mul ((Real.sqrt 2)⁻¹)).const_mul (Real.exp (-s))).const_mul
        ((Real.sqrt s)⁻¹)
