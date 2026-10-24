import GaussianRiesz.ComplexRieszTransform
import GaussianRiesz.RieszL2Identity
open MeasureTheory
theorem ComplexRieszL2Identity {n : ℕ} (v : Lp ℂ 2 (GaussMeasure n)) :
    ‖ComplexRieszTransform v‖ ^ 2
        = ‖RieszTransform (Complex.reCLM.compLp v)‖ ^ 2
          + ‖RieszTransform (Complex.imCLM.compLp v)‖ ^ 2
      ∧ ‖ComplexRieszTransform v‖ ≤ ‖v‖
      ∧ (∀ᵐ x ∂(GaussMeasure n),
          ‖(ComplexRieszTransform v :
              EuclideanSpace ℝ (Fin n) → EuclideanSpace ℂ (Fin n)) x‖ ^ 2
            = ‖(RieszTransform (Complex.reCLM.compLp v) :
                  EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) x‖ ^ 2
              + ‖(RieszTransform (Complex.imCLM.compLp v) :
                  EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) x‖ ^ 2) := by
  classical
  -- the `L²` norm squared is the integral of the squared pointwise norm, and that
  -- integrand is integrable; stated once for every value space used below
  have hsq : ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      (w : Lp E 2 (GaussMeasure n)),
      ‖w‖ ^ 2 = ∫ x, ‖(w : EuclideanSpace ℝ (Fin n) → E) x‖ ^ 2 ∂(GaussMeasure n) := by
    intro E _ _ w
    rw [← real_inner_self_eq_norm_sq, L2.inner_def (𝕜 := ℝ)]
    simp [real_inner_self_eq_norm_sq]
  have hsqint : ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      (w : Lp E 2 (GaussMeasure n)),
      Integrable (fun x => ‖(w : EuclideanSpace ℝ (Fin n) → E) x‖ ^ 2) (GaussMeasure n) := by
    intro E _ _ w
    simpa [real_inner_self_eq_norm_sq] using L2.integrable_inner (𝕜 := ℝ) w w
  -- STEP 1: the scalar identity
  have hscal : ∀ a b : ℝ, ‖(a : ℂ) + Complex.I * (b : ℂ)‖ ^ 2 = a ^ 2 + b ^ 2 := by
    intro a b
    rw [← Complex.normSq_eq_norm_sq]
    simp [Complex.normSq_apply]
    ring
  -- the coordinatewise inclusion of `ComplexRieszTransform`, kept opaque
  obtain ⟨A, hA⟩ : ∃ A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℂ (Fin n),
      A = (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n => ℂ)).symm.toContinuousLinearMap.comp
        (ContinuousLinearMap.pi fun i => Complex.ofRealCLM.comp (EuclideanSpace.proj i)) :=
    ⟨_, rfl⟩
  have hAcoord : ∀ (u : EuclideanSpace ℝ (Fin n)) (j : Fin n), (A u) j = ((u j : ℝ) : ℂ) := by
    intro u j
    rw [hA]
    simp
  have hpt : ∀ u1 u2 : EuclideanSpace ℝ (Fin n),
      ‖A u1 + Complex.I • A u2‖ ^ 2 = ‖u1‖ ^ 2 + ‖u2‖ ^ 2 := by
    intro u1 u2
    rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [show (A u1 + Complex.I • A u2) j
        = ((u1 j : ℝ) : ℂ) + Complex.I * ((u2 j : ℝ) : ℂ) from by
      rw [show (A u1 + Complex.I • A u2) j = (A u1) j + Complex.I * (A u2) j from rfl,
        hAcoord, hAcoord], hscal]
    simp [Real.norm_eq_abs, sq_abs]
  -- STEP 2: clause (3)
  have h3 : ∀ᵐ x ∂(GaussMeasure n),
      ‖(ComplexRieszTransform v :
          EuclideanSpace ℝ (Fin n) → EuclideanSpace ℂ (Fin n)) x‖ ^ 2
        = ‖(RieszTransform (Complex.reCLM.compLp v) :
              EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) x‖ ^ 2
          + ‖(RieszTransform (Complex.imCLM.compLp v) :
              EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) x‖ ^ 2 := by
    have hdef : ComplexRieszTransform v
        = A.compLp (RieszTransform (Complex.reCLM.compLp v))
          + Complex.I • A.compLp (RieszTransform (Complex.imCLM.compLp v)) := by
      rw [hA, ComplexRieszTransform]
    filter_upwards [Lp.coeFn_add (A.compLp (RieszTransform (Complex.reCLM.compLp v)))
        (Complex.I • A.compLp (RieszTransform (Complex.imCLM.compLp v))),
      Lp.coeFn_smul Complex.I (A.compLp (RieszTransform (Complex.imCLM.compLp v))),
      ContinuousLinearMap.coeFn_compLp' A (RieszTransform (Complex.reCLM.compLp v)),
      ContinuousLinearMap.coeFn_compLp' A (RieszTransform (Complex.imCLM.compLp v))]
      with x e1 e2 e3 e4
    rw [hdef, e1, Pi.add_apply, e2, Pi.smul_apply, e3, e4, hpt]
  -- STEP 3: clause (1)
  have h1 : ‖ComplexRieszTransform v‖ ^ 2
      = ‖RieszTransform (Complex.reCLM.compLp v)‖ ^ 2
        + ‖RieszTransform (Complex.imCLM.compLp v)‖ ^ 2 := by
    rw [hsq _ (ComplexRieszTransform v), hsq _ (RieszTransform (Complex.reCLM.compLp v)),
      hsq _ (RieszTransform (Complex.imCLM.compLp v)),
      ← integral_add (hsqint _ (RieszTransform (Complex.reCLM.compLp v)))
        (hsqint _ (RieszTransform (Complex.imCLM.compLp v)))]
    exact integral_congr_ae h3
  -- STEP 4: the real and imaginary parts of `v`
  have hstar : ‖v‖ ^ 2
      = ‖Complex.reCLM.compLp v‖ ^ 2 + ‖Complex.imCLM.compLp v‖ ^ 2 := by
    have hvpt : ∀ᵐ x ∂(GaussMeasure n),
        ‖(v : EuclideanSpace ℝ (Fin n) → ℂ) x‖ ^ 2
          = ‖(Complex.reCLM.compLp v : EuclideanSpace ℝ (Fin n) → ℝ) x‖ ^ 2
            + ‖(Complex.imCLM.compLp v : EuclideanSpace ℝ (Fin n) → ℝ) x‖ ^ 2 := by
      filter_upwards [ContinuousLinearMap.coeFn_compLp' Complex.reCLM v,
        ContinuousLinearMap.coeFn_compLp' Complex.imCLM v] with x e1 e2
      rw [e1, e2]
      simp only [Complex.reCLM_apply, Complex.imCLM_apply, Real.norm_eq_abs, sq_abs]
      rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
      ring
    rw [hsq _ v, hsq _ (Complex.reCLM.compLp v), hsq _ (Complex.imCLM.compLp v),
      ← integral_add (hsqint _ (Complex.reCLM.compLp v)) (hsqint _ (Complex.imCLM.compLp v))]
    exact integral_congr_ae hvpt
  -- STEP 5: clause (2)
  refine ⟨h1, ?_, h3⟩
  have hr1 := (RieszL2Identity (Complex.reCLM.compLp v)).2
  have hr2 := (RieszL2Identity (Complex.imCLM.compLp v)).2
  have hsq2 : ‖ComplexRieszTransform v‖ ^ 2 ≤ ‖v‖ ^ 2 := by
    rw [h1, hstar]
    have n1 := norm_nonneg (RieszTransform (Complex.reCLM.compLp v))
    have n2 := norm_nonneg (RieszTransform (Complex.imCLM.compLp v))
    nlinarith [hr1, hr2, n1, n2]
  calc ‖ComplexRieszTransform v‖
      = Real.sqrt (‖ComplexRieszTransform v‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
    _ ≤ Real.sqrt (‖v‖ ^ 2) := Real.sqrt_le_sqrt hsq2
    _ = ‖v‖ := Real.sqrt_sq (norm_nonneg _)
