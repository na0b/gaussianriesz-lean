module

public import GaussianRiesz.MultiplierL2Representation
public import GaussianRiesz.SemigroupRegularity
public import GaussianRiesz.MehlerFormula
public import GaussianRiesz.L2InnerGaussIntegral
public import GaussianRiesz.PosPartConstSubMemLp

@[expose] public section
open MeasureTheory
-- binder retained for statement fidelity to the paper; intentionally unused in the proof
set_option linter.unusedVariables false
theorem MultiplierPointwiseBound {n : ℕ} (F : Lp ℝ 2 (GaussMeasure n))
    (hF : 0 ≤ᵐ[GaussMeasure n] (F : EuclideanSpace ℝ (Fin n) → ℝ)) (a : ℝ) (ha : 0 < a)
    (u : Lp ℝ 2 (GaussMeasure n)) (hu : u ∈ ObstacleCone n)
    (hmin : ∀ w ∈ ObstacleCone n, ObstacleFunctional F a u ≤ ObstacleFunctional F a w)
    (η : Lp ℝ 2 (GaussMeasure n))
    (hη : ∀ φ : Lp ℝ 2 (GaussMeasure n), Energy φ ≠ ⊤ →
      ObstacleMultiplier F a u φ
        = ∫ x, (η : EuclideanSpace ℝ (Fin n) → ℝ) x
            * (φ : EuclideanSpace ℝ (Fin n) → ℝ) x ∂(GaussMeasure n)) :
    ∀ᵐ x ∂(GaussMeasure n), 0 ≤ (η : EuclideanSpace ℝ (Fin n) → ℝ) x
      ∧ (η : EuclideanSpace ℝ (Fin n) → ℝ) x
          ≤ max (a - (F : EuclideanSpace ℝ (Fin n) → ℝ) x) 0 := by
  classical
  have hprob : IsProbabilityMeasure (GaussMeasure n) := GaussIsProb n
  -- the kernel `k = (a - F)⁺` lies in `L²(γₙ)`, by domination by `a - F`
  have hk := PosPartConstSubMemLp F a
  set kL : Lp ℝ 2 (GaussMeasure n) := hk.toLp _ with hkLdef
  have hkc : (kL : EuclideanSpace ℝ (Fin n) → ℝ)
      =ᵐ[GaussMeasure n] fun x => max (a - (F : EuclideanSpace ℝ (Fin n) → ℝ) x) 0 :=
    hk.coeFn_toLp
  -- `L² ⊆ L¹` on a probability measure
  have hηint : Integrable (η : EuclideanSpace ℝ (Fin n) → ℝ) (GaussMeasure n) :=
    (Lp.memLp η).integrable (by norm_num)
  have hkint : Integrable (fun x => max (a - (F : EuclideanSpace ℝ (Fin n) → ℝ) x) 0)
      (GaussMeasure n) := hk.integrable (by norm_num)
  -- STEPS 1-3: the two set-integral inequalities, for every measurable `A`
  have hsets : ∀ A : Set (EuclideanSpace ℝ (Fin n)), MeasurableSet A →
      0 ≤ ∫ x in A, (η : EuclideanSpace ℝ (Fin n) → ℝ) x ∂(GaussMeasure n)
        ∧ (∫ x in A, (η : EuclideanSpace ℝ (Fin n) → ℝ) x ∂(GaussMeasure n))
            ≤ ∫ x in A, max (a - (F : EuclideanSpace ℝ (Fin n) → ℝ) x) 0 ∂(GaussMeasure n) := by
    intro A hA
    -- the indicator of `A`, as an `L²` element
    set oneA : Lp ℝ 2 (GaussMeasure n) :=
      indicatorConstLp 2 hA (measure_ne_top (GaussMeasure n) A) (1 : ℝ) with honeAdef
    have honeAc : (oneA : EuclideanSpace ℝ (Fin n) → ℝ)
        =ᵐ[GaussMeasure n] A.indicator (fun _ => (1 : ℝ)) := indicatorConstLp_coeFn
    have honeAnn : 0 ≤ᵐ[GaussMeasure n] (oneA : EuclideanSpace ℝ (Fin n) → ℝ) := by
      filter_upwards [honeAc] with x hx
      rw [hx]
      exact Set.indicator_nonneg (fun _ _ => zero_le_one) x
    obtain ⟨hreg1, hreg2⟩ := SemigroupRegularity oneA
    -- STEP 1 + STEP 2: for each `s > 0` the smoothed indicator is a legal test function
    have hper : ∀ s : ℝ, 0 < s →
        0 ≤ (inner ℝ η (OUSemigroup s oneA) : ℝ)
          ∧ (inner ℝ η (OUSemigroup s oneA) : ℝ)
              ≤ (inner ℝ kL (OUSemigroup s oneA) : ℝ) := by
      intro s hs
      have hE : Energy (OUSemigroup s oneA) ≠ ⊤ := hreg1 s hs
      have hnn : 0 ≤ᵐ[GaussMeasure n]
          (OUSemigroup s oneA : EuclideanSpace ℝ (Fin n) → ℝ) :=
        (MehlerFormula s hs oneA).2.2 honeAnn
      have hcone : OUSemigroup s oneA ∈ ObstacleCone n := ⟨hE, hnn⟩
      have hrep := hη (OUSemigroup s oneA) hE
      have hpos := MultiplierPositive F a u hu hmin (OUSemigroup s oneA) hcone
      have hLS := LewyStampacchia F hF a u hu hmin (OUSemigroup s oneA) hcone
      rw [hrep] at hpos hLS
      have e1 : ∫ x, (η : EuclideanSpace ℝ (Fin n) → ℝ) x
            * (OUSemigroup s oneA : EuclideanSpace ℝ (Fin n) → ℝ) x ∂(GaussMeasure n)
          = (inner ℝ η (OUSemigroup s oneA) : ℝ) := (L2InnerGaussIntegral _ _).symm
      have e2 : ∫ x, max (a - (F : EuclideanSpace ℝ (Fin n) → ℝ) x) 0
            * (OUSemigroup s oneA : EuclideanSpace ℝ (Fin n) → ℝ) x ∂(GaussMeasure n)
          = (inner ℝ kL (OUSemigroup s oneA) : ℝ) := by
        rw [L2InnerGaussIntegral kL]
        refine integral_congr_ae ?_
        filter_upwards [hkc] with x hx
        rw [hx]
      rw [e1] at hpos
      rw [e1, e2] at hLS
      exact ⟨hpos, hLS⟩
    -- STEP 3: let `s ↓ 0`, using strong continuity and continuity of the inner product
    have hlim1 : Filter.Tendsto (fun s : ℝ => (inner ℝ η (OUSemigroup s oneA) : ℝ))
        (nhdsWithin 0 (Set.Ioi 0)) (nhds (inner ℝ η oneA : ℝ)) :=
      Filter.Tendsto.inner tendsto_const_nhds hreg2
    have hlim2 : Filter.Tendsto (fun s : ℝ => (inner ℝ kL (OUSemigroup s oneA) : ℝ))
        (nhdsWithin 0 (Set.Ioi 0)) (nhds (inner ℝ kL oneA : ℝ)) :=
      Filter.Tendsto.inner tendsto_const_nhds hreg2
    have hev1 : ∀ᶠ s in nhdsWithin (0 : ℝ) (Set.Ioi 0),
        (0 : ℝ) ≤ (inner ℝ η (OUSemigroup s oneA) : ℝ) :=
      eventually_nhdsWithin_of_forall fun s hs => (hper s hs).1
    have hev2 : ∀ᶠ s in nhdsWithin (0 : ℝ) (Set.Ioi 0),
        (inner ℝ η (OUSemigroup s oneA) : ℝ) ≤ (inner ℝ kL (OUSemigroup s oneA) : ℝ) :=
      eventually_nhdsWithin_of_forall fun s hs => (hper s hs).2
    have hA1 : (0 : ℝ) ≤ (inner ℝ η oneA : ℝ) := ge_of_tendsto hlim1 hev1
    have hA2 : (inner ℝ η oneA : ℝ) ≤ (inner ℝ kL oneA : ℝ) :=
      le_of_tendsto_of_tendsto hlim1 hlim2 hev2
    -- identify the limiting inner products with set integrals over `A`
    have hsetη : (inner ℝ η oneA : ℝ)
        = ∫ x in A, (η : EuclideanSpace ℝ (Fin n) → ℝ) x ∂(GaussMeasure n) := by
      rw [L2InnerGaussIntegral, ← integral_indicator hA]
      refine integral_congr_ae ?_
      filter_upwards [honeAc] with x hx
      rw [hx]
      by_cases hxA : x ∈ A <;> simp [hxA]
    have hsetk : (inner ℝ kL oneA : ℝ)
        = ∫ x in A, max (a - (F : EuclideanSpace ℝ (Fin n) → ℝ) x) 0 ∂(GaussMeasure n) := by
      rw [L2InnerGaussIntegral, ← integral_indicator hA]
      refine integral_congr_ae ?_
      filter_upwards [honeAc, hkc] with x hx hkx
      rw [hx, hkx]
      by_cases hxA : x ∈ A <;> simp [hxA]
    rw [hsetη] at hA1 hA2
    rw [hsetk] at hA2
    exact ⟨hA1, hA2⟩
  -- STEP 4: arbitrary measurable sets give the pointwise bounds
  have hnn : 0 ≤ᵐ[GaussMeasure n] (η : EuclideanSpace ℝ (Fin n) → ℝ) :=
    ae_nonneg_of_forall_setIntegral_nonneg hηint fun A hA _ => (hsets A hA).1
  have hle : (η : EuclideanSpace ℝ (Fin n) → ℝ)
      ≤ᵐ[GaussMeasure n] fun x => max (a - (F : EuclideanSpace ℝ (Fin n) → ℝ) x) 0 :=
    ae_le_of_forall_setIntegral_le hηint hkint fun A hA _ => (hsets A hA).2
  filter_upwards [hnn, hle] with x h1 h2
  exact ⟨h1, h2⟩
