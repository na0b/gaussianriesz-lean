module

public import GaussianRiesz.RieszSqrtIdentity
public import GaussianRiesz.FracPowLinear
public import GaussianRiesz.PseudoInverseSqrt
public import GaussianRiesz.SqrtDomainSobolev
public import GaussianRiesz.GaussDLinear

@[expose] public section
open MeasureTheory
theorem TransformedLocalization {n : ℕ} (f g u : Lp ℝ 2 (GaussMeasure n))
    (hu : u ∈ FracPowDomain ((1 : ℝ) / 2))
    (hdec : f = g + FracPow ((1 : ℝ) / 2) u) (t : ℝ)
    (Ω : Set (EuclideanSpace ℝ (Fin n)))
    (hloc : ∀ᵐ x ∂(GaussMeasure n), x ∉ Ω
      → (GaussD u : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) x = 0) :
    (RieszTransform f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
        =ᵐ[GaussMeasure n] (fun x =>
          (RieszTransform g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) x
            + (GaussD u : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) x)
      ∧ GaussMeasure n
            {x | t < ‖(RieszTransform f : EuclideanSpace ℝ (Fin n)
              → EuclideanSpace ℝ (Fin n)) x‖}
          ≤ GaussMeasure n Ω
            + GaussMeasure n {x | t < ‖(RieszTransform g : EuclideanSpace ℝ (Fin n)
              → EuclideanSpace ℝ (Fin n)) x‖} := by
  -- Step 1: `R_γ` is additive on `L²(γₙ)`, so it may be applied to `f = g + Bu`
  have hd1 : (-(1 : ℝ) / 2 : ℝ) ≤ 0 := by norm_num
  have hmem : ∀ z : Lp ℝ 2 (GaussMeasure n), z ∈ FracPowDomain (-(1 : ℝ) / 2) :=
    (FracPowLinear (-(1 : ℝ) / 2)).1 hd1
  have hsplit : FracPow (-(1 : ℝ) / 2) f
      = FracPow (-(1 : ℝ) / 2) g
        + FracPow (-(1 : ℝ) / 2) (FracPow ((1 : ℝ) / 2) u) := by
    rw [hdec]
    exact ((FracPowLinear (-(1 : ℝ) / 2)).2.1 g (FracPow ((1 : ℝ) / 2) u)
      (hmem g) (hmem _)).2
  have hs1 : FracPow (-(1 : ℝ) / 2) g ∈ SobolevW12 n :=
    (SqrtDomainSobolev _ (PseudoInverseSqrt g).1).1
  have hs2 : FracPow (-(1 : ℝ) / 2) (FracPow ((1 : ℝ) / 2) u) ∈ SobolevW12 n :=
    (SqrtDomainSobolev _ (PseudoInverseSqrt (FracPow ((1 : ℝ) / 2) u)).1).1
  have hRadd : RieszTransform f = RieszTransform g + GaussD u := by
    show GaussD (FracPow (-(1 : ℝ) / 2) f)
        = GaussD (FracPow (-(1 : ℝ) / 2) g) + GaussD u
    rw [hsplit, (GaussDLinear.1 _ _ hs1 hs2).2]
    exact congrArg _ (RieszSqrtIdentity u hu)
  -- Step 2: the pointwise identity
  have hae : (RieszTransform f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
      =ᵐ[GaussMeasure n] (fun x =>
        (RieszTransform g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) x
          + (GaussD u : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) x) := by
    rw [hRadd]
    filter_upwards [Lp.coeFn_add (RieszTransform g) (GaussD u)] with x hx
    simpa using hx
  refine ⟨hae, ?_⟩
  -- Step 3: the level set is contained, up to a null set, in `Ω` together with
  -- the level set of `R_γ g`
  have h1 : GaussMeasure n {x | t < ‖(RieszTransform f : EuclideanSpace ℝ (Fin n)
          → EuclideanSpace ℝ (Fin n)) x‖}
      ≤ GaussMeasure n (Ω ∪ {x | t < ‖(RieszTransform g : EuclideanSpace ℝ (Fin n)
          → EuclideanSpace ℝ (Fin n)) x‖}) := by
    refine measure_mono_ae ?_
    filter_upwards [hae, hloc] with x hx hxl
    intro hxS
    by_cases hxΩ : x ∈ Ω
    · exact Or.inl hxΩ
    · refine Or.inr ?_
      have hxS' : t < ‖(RieszTransform f : EuclideanSpace ℝ (Fin n)
          → EuclideanSpace ℝ (Fin n)) x‖ := hxS
      show t < ‖(RieszTransform g : EuclideanSpace ℝ (Fin n)
          → EuclideanSpace ℝ (Fin n)) x‖
      rwa [hx, hxl hxΩ, add_zero] at hxS'
  exact h1.trans (measure_union_le _ _)
