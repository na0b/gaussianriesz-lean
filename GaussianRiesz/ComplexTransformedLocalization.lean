module

public import GaussianRiesz.ComplexRieszTransform
public import GaussianRiesz.TransformedLocalization

@[expose] public section
open MeasureTheory
theorem ComplexTransformedLocalization {n : ℕ} (v w : Lp ℂ 2 (GaussMeasure n))
    (g₁ g₂ u₁ u₂ : Lp ℝ 2 (GaussMeasure n))
    (hu₁ : u₁ ∈ FracPowDomain ((1 : ℝ) / 2)) (hu₂ : u₂ ∈ FracPowDomain ((1 : ℝ) / 2))
    (h₁ : Complex.reCLM.compLp v = g₁ + FracPow ((1 : ℝ) / 2) u₁)
    (h₂ : Complex.imCLM.compLp v = g₂ + FracPow ((1 : ℝ) / 2) u₂)
    (hw₁ : Complex.reCLM.compLp w = g₁) (hw₂ : Complex.imCLM.compLp w = g₂)
    (t : ℝ) (Ω : Set (EuclideanSpace ℝ (Fin n)))
    (hloc₁ : ∀ᵐ x ∂(GaussMeasure n), x ∉ Ω →
      (GaussD u₁ : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) x = 0)
    (hloc₂ : ∀ᵐ x ∂(GaussMeasure n), x ∉ Ω →
      (GaussD u₂ : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) x = 0) :
    (∀ᵐ x ∂(GaussMeasure n), x ∉ Ω →
        (ComplexRieszTransform v :
            EuclideanSpace ℝ (Fin n) → EuclideanSpace ℂ (Fin n)) x
          = (ComplexRieszTransform w :
              EuclideanSpace ℝ (Fin n) → EuclideanSpace ℂ (Fin n)) x)
      ∧ GaussMeasure n {x | t < ‖(ComplexRieszTransform v :
            EuclideanSpace ℝ (Fin n) → EuclideanSpace ℂ (Fin n)) x‖}
          ≤ GaussMeasure n Ω
            + GaussMeasure n {x | t < ‖(ComplexRieszTransform w :
                EuclideanSpace ℝ (Fin n) → EuclideanSpace ℂ (Fin n)) x‖} := by
  classical
  -- the coordinatewise inclusion of `ComplexRieszTransform`, kept opaque
  obtain ⟨A, hA⟩ : ∃ A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℂ (Fin n),
      A = (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n => ℂ)).symm.toContinuousLinearMap.comp
        (ContinuousLinearMap.pi fun i => Complex.ofRealCLM.comp (EuclideanSpace.proj i)) :=
    ⟨_, rfl⟩
  have hdefv : ComplexRieszTransform v
      = A.compLp (RieszTransform (Complex.reCLM.compLp v))
        + Complex.I • A.compLp (RieszTransform (Complex.imCLM.compLp v)) := by
    rw [hA, ComplexRieszTransform]
  have hdefw : ComplexRieszTransform w
      = A.compLp (RieszTransform g₁) + Complex.I • A.compLp (RieszTransform g₂) := by
    rw [hA, ComplexRieszTransform, hw₁, hw₂]
  -- STEP 1: the two real localizations
  obtain ⟨hl1, -⟩ := TransformedLocalization (Complex.reCLM.compLp v) g₁ u₁ hu₁ h₁ t Ω hloc₁
  obtain ⟨hl2, -⟩ := TransformedLocalization (Complex.imCLM.compLp v) g₂ u₂ hu₂ h₂ t Ω hloc₂
  -- STEPS 2 and 3: a single null set, and clause (1)
  have hc1 : ∀ᵐ x ∂(GaussMeasure n), x ∉ Ω →
      (ComplexRieszTransform v :
          EuclideanSpace ℝ (Fin n) → EuclideanSpace ℂ (Fin n)) x
        = (ComplexRieszTransform w :
            EuclideanSpace ℝ (Fin n) → EuclideanSpace ℂ (Fin n)) x := by
    filter_upwards [hloc₁, hloc₂, hl1, hl2,
      Lp.coeFn_add (A.compLp (RieszTransform (Complex.reCLM.compLp v)))
        (Complex.I • A.compLp (RieszTransform (Complex.imCLM.compLp v))),
      Lp.coeFn_smul Complex.I (A.compLp (RieszTransform (Complex.imCLM.compLp v))),
      ContinuousLinearMap.coeFn_compLp' A (RieszTransform (Complex.reCLM.compLp v)),
      ContinuousLinearMap.coeFn_compLp' A (RieszTransform (Complex.imCLM.compLp v)),
      Lp.coeFn_add (A.compLp (RieszTransform g₁))
        (Complex.I • A.compLp (RieszTransform g₂)),
      Lp.coeFn_smul Complex.I (A.compLp (RieszTransform g₂)),
      ContinuousLinearMap.coeFn_compLp' A (RieszTransform g₁),
      ContinuousLinearMap.coeFn_compLp' A (RieszTransform g₂)]
      with x d1 d2 e1 e2 a1 a2 a3 a4 b1 b2 b3 b4
    intro hxΩ
    rw [hdefv, a1, Pi.add_apply, a2, Pi.smul_apply, a3, a4,
      hdefw, b1, Pi.add_apply, b2, Pi.smul_apply, b3, b4,
      e1, e2, d1 hxΩ, d2 hxΩ, add_zero, add_zero]
  refine ⟨hc1, ?_⟩
  -- STEP 4: clause (2)
  have hsub : {x : EuclideanSpace ℝ (Fin n) | t < ‖(ComplexRieszTransform v :
        EuclideanSpace ℝ (Fin n) → EuclideanSpace ℂ (Fin n)) x‖}
      ⊆ (Ω ∪ {x : EuclideanSpace ℝ (Fin n) | t < ‖(ComplexRieszTransform w :
            EuclideanSpace ℝ (Fin n) → EuclideanSpace ℂ (Fin n)) x‖})
        ∪ {x : EuclideanSpace ℝ (Fin n) | ¬ (x ∉ Ω →
            (ComplexRieszTransform v :
                EuclideanSpace ℝ (Fin n) → EuclideanSpace ℂ (Fin n)) x
              = (ComplexRieszTransform w :
                  EuclideanSpace ℝ (Fin n) → EuclideanSpace ℂ (Fin n)) x)} := by
    intro x hx
    by_cases hxΩ : x ∈ Ω
    · exact Or.inl (Or.inl hxΩ)
    by_cases hgood : (ComplexRieszTransform v :
        EuclideanSpace ℝ (Fin n) → EuclideanSpace ℂ (Fin n)) x
        = (ComplexRieszTransform w :
            EuclideanSpace ℝ (Fin n) → EuclideanSpace ℂ (Fin n)) x
    · refine Or.inl (Or.inr ?_)
      rw [Set.mem_ofPred_eq, ← hgood]
      exact hx
    · exact Or.inr fun h => hgood (h hxΩ)
  calc GaussMeasure n {x : EuclideanSpace ℝ (Fin n) | t < ‖(ComplexRieszTransform v :
          EuclideanSpace ℝ (Fin n) → EuclideanSpace ℂ (Fin n)) x‖}
      ≤ GaussMeasure n ((Ω ∪ {x : EuclideanSpace ℝ (Fin n) |
              t < ‖(ComplexRieszTransform w :
                EuclideanSpace ℝ (Fin n) → EuclideanSpace ℂ (Fin n)) x‖})
            ∪ {x : EuclideanSpace ℝ (Fin n) | ¬ (x ∉ Ω →
                (ComplexRieszTransform v :
                    EuclideanSpace ℝ (Fin n) → EuclideanSpace ℂ (Fin n)) x
                  = (ComplexRieszTransform w :
                      EuclideanSpace ℝ (Fin n) → EuclideanSpace ℂ (Fin n)) x)}) :=
        measure_mono hsub
    _ ≤ GaussMeasure n (Ω ∪ {x : EuclideanSpace ℝ (Fin n) |
            t < ‖(ComplexRieszTransform w :
              EuclideanSpace ℝ (Fin n) → EuclideanSpace ℂ (Fin n)) x‖})
          + GaussMeasure n {x : EuclideanSpace ℝ (Fin n) | ¬ (x ∉ Ω →
              (ComplexRieszTransform v :
                  EuclideanSpace ℝ (Fin n) → EuclideanSpace ℂ (Fin n)) x
                = (ComplexRieszTransform w :
                    EuclideanSpace ℝ (Fin n) → EuclideanSpace ℂ (Fin n)) x)} :=
        measure_union_le _ _
    _ ≤ GaussMeasure n Ω
          + GaussMeasure n {x : EuclideanSpace ℝ (Fin n) |
              t < ‖(ComplexRieszTransform w :
                EuclideanSpace ℝ (Fin n) → EuclideanSpace ℂ (Fin n)) x‖} := by
        rw [ae_iff.1 hc1, add_zero]
        exact measure_union_le _ _
