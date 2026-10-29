module

public import GaussianRiesz.LebesgueDilation
public import GaussianRiesz.MehlerGradientSubordination
public import GaussianRiesz.SemigroupGradientCommute
public import GaussianRiesz.RieszTransform
public import GaussianRiesz.GaussDWitness
public import GaussianRiesz.SubordinationWeightIntegral
public import GaussianRiesz.GaussLebesgueBallComparison
public import GaussianRiesz.RieszPseudoInverseTestedIdentity

@[expose] public section
open MeasureTheory
theorem RieszSemigroupPointwise {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hfc : HasCompactSupport f)
    (hmem : MemLp f 2 (GaussMeasure n)) (j : Fin n) :
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
              (EuclideanSpace.single j (1 : ℝ)) ∂(GaussMeasure n))))
      ∧ (fun x : EuclideanSpace ℝ (Fin n) =>
            (Real.sqrt Real.pi)⁻¹ * ∫ s in Set.Ioi (0 : ℝ), (Real.sqrt s)⁻¹ * (Real.exp (-s) *
              ((Real.sqrt 2)⁻¹ * ∫ z, fderiv ℝ f (Real.exp (-s) • x
                  + Real.sqrt (1 - Real.exp (-2 * s)) • z)
                (EuclideanSpace.single j (1 : ℝ)) ∂(GaussMeasure n))))
          =ᵐ[GaussMeasure n]
          fun x : EuclideanSpace ℝ (Fin n) =>
            (RieszTransform (hmem.toLp f) :
              EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) x j := by
  classical
  have hprob : IsProbabilityMeasure (GaussMeasure n) := GaussIsProb n
  set u : Lp ℝ 2 (GaussMeasure n) := hmem.toLp f with hu
  -- `A s i x` is the Mehler average of `∂ᵢf` at time `s`, and `Phi i` its subordination
  -- integral; `Phi j` is the function the statement is about.
  set A : ℝ → Fin n → EuclideanSpace ℝ (Fin n) → ℝ := fun s i x =>
    ∫ z, fderiv ℝ f (Real.exp (-s) • x + Real.sqrt (1 - Real.exp (-2 * s)) • z)
      (EuclideanSpace.single i (1 : ℝ)) ∂(GaussMeasure n) with hA
  set Phi : Fin n → EuclideanSpace ℝ (Fin n) → ℝ := fun i x =>
    (Real.sqrt Real.pi)⁻¹ * ∫ s in Set.Ioi (0 : ℝ),
      (Real.sqrt s)⁻¹ * (Real.exp (-s) * ((Real.sqrt 2)⁻¹ * A s i x)) with hPhi
  -- Step 0: the sup-norm bound on the gradient, as in `MehlerGradientSubordination`.
  have hfd : Continuous (fderiv ℝ f) := hf.continuous_fderiv (by simp)
  have hfdcs : HasCompactSupport (fderiv ℝ f) := hfc.fderiv ℝ
  obtain ⟨N, hN⟩ : ∃ N : ℝ, ∀ y, ‖fderiv ℝ f y‖ ≤ N := by
    obtain ⟨N, hNb⟩ := (hfdcs.isCompact_range hfd).isBounded.subset_closedBall 0
    exact ⟨N, fun y => by simpa using hNb (Set.mem_range_self y)⟩
  have hNd : ∀ (i : Fin n) (y : EuclideanSpace ℝ (Fin n)),
      ‖fderiv ℝ f y (EuclideanSpace.single i (1 : ℝ))‖ ≤ N := by
    intro i y
    calc ‖fderiv ℝ f y (EuclideanSpace.single i (1 : ℝ))‖
        ≤ ‖fderiv ℝ f y‖ * ‖EuclideanSpace.single i (1 : ℝ)‖ := ContinuousLinearMap.le_opNorm _ _
      _ = ‖fderiv ℝ f y‖ := by rw [PiLp.norm_single]; simp
      _ ≤ N := hN y
  have hN0 : (0 : ℝ) ≤ N := le_trans (norm_nonneg _) (hNd j 0)
  have hAbd : ∀ (s : ℝ) (i : Fin n) (x : EuclideanSpace ℝ (Fin n)), ‖A s i x‖ ≤ N := by
    intro s i x
    have h : ‖A s i x‖ ≤ N * Measure.real (GaussMeasure n) Set.univ := by
      rw [hA]
      exact norm_integral_le_of_norm_le_const (Filter.Eventually.of_forall fun z => hNd i _)
    simpa using h
  -- joint continuity of `A` in `(s, x)`, re-derived here: `MehlerGradientSubordination`
  -- establishes it inside its proof but does not carry it at statement level.
  have hAjoint : ∀ i : Fin n, Continuous (fun p : ℝ × EuclideanSpace ℝ (Fin n) =>
      A p.1 i p.2) := by
    intro i
    rw [hA]
    refine continuous_of_dominated (bound := fun _ => N) (fun p => ?_)
      (fun p => Filter.Eventually.of_forall fun z => hNd i _) (integrable_const N)
      (Filter.Eventually.of_forall fun z => ?_)
    · exact Continuous.aestronglyMeasurable ((hfd.comp (by fun_prop)).clm_apply continuous_const)
    · exact (hfd.comp (by fun_prop)).clm_apply continuous_const
  -- the scalar weight, by import
  have hwt : IntegrableOn (fun s : ℝ => (Real.sqrt s)⁻¹ * Real.exp (-s))
      (Set.Ioi (0 : ℝ)) := SubordinationWeightIntegral.1
  have hwtval : ∫ s in Set.Ioi (0 : ℝ), (Real.sqrt s)⁻¹ * Real.exp (-s) = Real.sqrt Real.pi :=
    SubordinationWeightIntegral.2
  -- clauses (1) and (2), and the pointwise bound on `Phi`
  have hcl : ∀ i : Fin n,
      (∀ x : EuclideanSpace ℝ (Fin n),
          IntegrableOn (fun s : ℝ => (Real.sqrt s)⁻¹ * (Real.exp (-s) *
            ((Real.sqrt 2)⁻¹ * A s i x))) (Set.Ioi (0 : ℝ)))
        ∧ Continuous (Phi i) := fun i => MehlerGradientSubordination f hf hfc i
  have hPhibd : ∀ (i : Fin n) (x : EuclideanSpace ℝ (Fin n)),
      ‖Phi i x‖ ≤ (Real.sqrt 2)⁻¹ * N := by
    intro i x
    have hmaj : IntegrableOn (fun s : ℝ => (Real.sqrt 2)⁻¹ * N *
        ((Real.sqrt s)⁻¹ * Real.exp (-s))) (Set.Ioi (0 : ℝ)) := hwt.const_mul _
    have h1 : ‖∫ s in Set.Ioi (0 : ℝ), (Real.sqrt s)⁻¹ * (Real.exp (-s) *
          ((Real.sqrt 2)⁻¹ * A s i x))‖
        ≤ ∫ s in Set.Ioi (0 : ℝ), (Real.sqrt 2)⁻¹ * N *
            ((Real.sqrt s)⁻¹ * Real.exp (-s)) := by
      refine le_trans (norm_integral_le_integral_norm _) ?_
      refine setIntegral_mono_on ((hcl i).1 x).norm hmaj measurableSet_Ioi fun s hs => ?_
      have hs0 : (0 : ℝ) < s := hs
      have h2 : ‖A s i x‖ ≤ N := hAbd s i x
      have h3 : (0 : ℝ) ≤ (Real.sqrt s)⁻¹ := by positivity
      have h4 : (0 : ℝ) < Real.exp (-s) := Real.exp_pos _
      have h5 : (0 : ℝ) ≤ (Real.sqrt 2)⁻¹ := by positivity
      rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_mul, abs_inv, abs_inv,
        abs_of_nonneg (Real.sqrt_nonneg s), abs_of_nonneg (Real.sqrt_nonneg 2),
        abs_of_pos h4]
      rw [Real.norm_eq_abs] at h2
      nlinarith [mul_le_mul_of_nonneg_left h2 (mul_nonneg (mul_nonneg h3 h4.le) h5)]
    rw [hPhi]
    simp only
    rw [norm_mul, Real.norm_eq_abs, abs_inv, abs_of_nonneg (Real.sqrt_nonneg _)]
    have hpi : (0 : ℝ) < Real.sqrt Real.pi := Real.sqrt_pos.mpr Real.pi_pos
    have h6 : ∫ s in Set.Ioi (0 : ℝ), (Real.sqrt 2)⁻¹ * N *
        ((Real.sqrt s)⁻¹ * Real.exp (-s)) = (Real.sqrt 2)⁻¹ * N * Real.sqrt Real.pi := by
      rw [integral_const_mul, hwtval]
    rw [h6] at h1
    rw [inv_mul_le_iff₀ hpi]
    calc ‖∫ s in Set.Ioi (0 : ℝ), (Real.sqrt s)⁻¹ * (Real.exp (-s) *
            ((Real.sqrt 2)⁻¹ * A s i x))‖
        ≤ (Real.sqrt 2)⁻¹ * N * Real.sqrt Real.pi := h1
      _ = Real.sqrt Real.pi * ((Real.sqrt 2)⁻¹ * N) := by ring
  -- the vector field and its `L²(γₙ)` class
  set PhiV : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) := fun x =>
    WithLp.toLp 2 (fun i => Phi i x) with hPhiV
  have hPhiVc : Continuous PhiV := by
    rw [hPhiV]
    exact (EuclideanSpace.equiv (Fin n) ℝ).symm.continuous.comp
      (continuous_pi fun i => (hcl i).2)
  have hPhiVbd : ∀ x, ‖PhiV x‖ ≤ Real.sqrt n * ((Real.sqrt 2)⁻¹ * N) := by
    intro x
    have hD0 : (0 : ℝ) ≤ (Real.sqrt 2)⁻¹ * N := by positivity
    rw [hPhiV, EuclideanSpace.norm_eq]
    have hsum : ∑ i : Fin n, ‖(WithLp.toLp 2 (fun i => Phi i x) :
        EuclideanSpace ℝ (Fin n)) i‖ ^ 2
        ≤ ∑ _i : Fin n, ((Real.sqrt 2)⁻¹ * N) ^ 2 := by
      refine Finset.sum_le_sum fun i _ => ?_
      have := hPhibd i x
      have h' : ‖(WithLp.toLp 2 (fun i => Phi i x) : EuclideanSpace ℝ (Fin n)) i‖
          = ‖Phi i x‖ := rfl
      rw [h']
      exact pow_le_pow_left₀ (norm_nonneg _) this 2
    refine le_trans (Real.sqrt_le_sqrt hsum) ?_
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      Real.sqrt_mul (by positivity), Real.sqrt_sq hD0]
  have hPhiVmem : MemLp PhiV 2 (GaussMeasure n) :=
    MemLp.of_bound hPhiVc.aestronglyMeasurable _
      (Filter.Eventually.of_forall hPhiVbd)
  set Psi : Lp (EuclideanSpace ℝ (Fin n)) 2 (GaussMeasure n) := hPhiVmem.toLp PhiV with hPsi
  have hPsicoe : (Psi : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
      =ᵐ[GaussMeasure n] PhiV := by rw [hPsi]; exact hPhiVmem.coeFn_toLp
  -- `γₙ` and Lebesgue measure have the same null sets, so a.e. statements transfer
  have hnull : ∀ S : Set (EuclideanSpace ℝ (Fin n)),
      GaussMeasure n S = 0 ↔ volume S = 0 := GaussLebesgueBallComparison.2.2.2
  have hconv : ∀ p : EuclideanSpace ℝ (Fin n) → Prop,
      (∀ᵐ x ∂(GaussMeasure n), p x) →
      ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))), p x := by
    intro p hp
    rw [MeasureTheory.ae_iff] at hp ⊢
    exact (hnull _).mp hp
  -- STEPS 6, 7, 10: the tested identity for the pseudoinverse
  have hmain := RieszPseudoInverseTestedIdentity f hf hfc hmem u hu A hA Phi hPhi N
    hAbd hAjoint hwt hconv
  have hWG : HasGaussWeakGrad (FracPow (-(1 : ℝ) / 2) u : EuclideanSpace ℝ (Fin n) → ℝ)
      (fun x => Real.sqrt 2 •
        (Psi : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) x) := by
    intro i ψ hψ hψc
    rw [hmain i ψ hψ hψc]
    congr 1
    refine integral_congr_ae ?_
    refine hconv _ ?_
    filter_upwards [hPsicoe] with x hx
    rw [hx]
    simp [hPhiV]
  have hGD : GaussD (FracPow (-(1 : ℝ) / 2) u) = Psi :=
    (GaussDWitness (FracPow (-(1 : ℝ) / 2) u) Psi hWG).2
  refine ⟨(MehlerGradientSubordination f hf hfc j).1,
    (MehlerGradientSubordination f hf hfc j).2, ?_⟩
  have hRT : (RieszTransform u : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
      =ᵐ[GaussMeasure n] PhiV := by
    rw [show RieszTransform u = Psi from by rw [RieszTransform]; exact hGD]
    exact hPsicoe
  filter_upwards [hRT] with x hx
  rw [hx]
