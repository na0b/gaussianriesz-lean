module

public import GaussianRiesz.ObstacleMinimizerExists
public import GaussianRiesz.ObstacleMinimizerUnique
public import GaussianRiesz.MultiplierL2Representation
public import GaussianRiesz.MultiplierPointwiseBound
public import GaussianRiesz.DomainUpgrade
public import GaussianRiesz.MassConservation
public import GaussianRiesz.Complementarity
public import GaussianRiesz.ExceptionalSetBound
public import GaussianRiesz.GradientLocality
public import GaussianRiesz.SqrtDomainSobolev
public import GaussianRiesz.HermiteL2ZeroAEOne

@[expose] public section
open MeasureTheory
theorem ObstacleDecomposition {n : ℕ} (F : Lp ℝ 2 (GaussMeasure n))
    (hF : 0 ≤ᵐ[GaussMeasure n] (F : EuclideanSpace ℝ (Fin n) → ℝ)) (m a : ℝ)
    (hm : m = ∫ x, (F : EuclideanSpace ℝ (Fin n) → ℝ) x ∂(GaussMeasure n)) (ha : m < a) :
    ∃ u ∈ FracPowDomain ((1 : ℝ) / 2), ∃ g : Lp ℝ 2 (GaussMeasure n),
      (0 ≤ᵐ[GaussMeasure n] (u : EuclideanSpace ℝ (Fin n) → ℝ))
      ∧ F = g + FracPow ((1 : ℝ) / 2) u
      ∧ (∀ᵐ x ∂(GaussMeasure n),
          min ((F : EuclideanSpace ℝ (Fin n) → ℝ) x) a ≤ (g : EuclideanSpace ℝ (Fin n) → ℝ) x
            ∧ (g : EuclideanSpace ℝ (Fin n) → ℝ) x ≤ a)
      ∧ (∫ x, (g : EuclideanSpace ℝ (Fin n) → ℝ) x ∂(GaussMeasure n)) = m
      ∧ (∀ᵐ x ∂(GaussMeasure n), 0 < (u : EuclideanSpace ℝ (Fin n) → ℝ) x
          → (g : EuclideanSpace ℝ (Fin n) → ℝ) x = a)
      ∧ ENNReal.ofReal a * GaussMeasure n {x | 0 < (u : EuclideanSpace ℝ (Fin n) → ℝ) x}
          ≤ ENNReal.ofReal m
      ∧ (∀ᵐ x ∂(GaussMeasure n), (u : EuclideanSpace ℝ (Fin n) → ℝ) x ≤ 0
          → (GaussD u : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) x = 0)
      ∧ u ∈ ObstacleCone n
      ∧ (∀ v ∈ ObstacleCone n, ObstacleFunctional F a u ≤ ObstacleFunctional F a v)
      ∧ (∀ u' ∈ ObstacleCone n,
          (∀ v ∈ ObstacleCone n, ObstacleFunctional F a u' ≤ ObstacleFunctional F a v)
            → u' = u) := by
  classical
  -- `m ≥ 0`, hence `a > 0`
  have hm0 : 0 ≤ m := by
    rw [hm]
    exact integral_nonneg_of_ae hF
  have ha0 : 0 < a := lt_of_le_of_lt hm0 ha
  -- Step 1: the minimizer
  obtain ⟨u, hu, hmin⟩ := ObstacleMinimizerExists F hF m a hm ha
  -- Step 2: the multiplier as an `L²` function
  obtain ⟨η, hη⟩ := MultiplierL2Representation F hF a ha0 u hu hmin
  -- Step 3: pointwise bounds
  have hbd := MultiplierPointwiseBound F hF a ha0 u hu hmin η hη
  -- Step 4: the decomposition identity
  obtain ⟨hdom, hsqrt⟩ := DomainUpgrade F a u hu η hη
  -- Step 5: mass
  have hmass := MassConservation F m a hm u η hη
  -- Step 6: the contact set
  obtain ⟨-, hcompl⟩ := Complementarity F hF a ha0 u hu hmin η hη
  -- Step 7: the measure of the contact set
  have hmeas := ExceptionalSetBound F hF m a ha0 u η hmass hbd hcompl
  -- Step 8: locality of the gradient
  obtain ⟨hsob, -⟩ := SqrtDomainSobolev u hdom
  have hloc := GradientLocality u hsob hu.2
  -- the good part `g = a·1 - η`
  set g : Lp ℝ 2 (GaussMeasure n) := a • HermiteL2 (0 : Fin n → ℕ) - η with hgdef
  have hgpt : (g : EuclideanSpace ℝ (Fin n) → ℝ)
      =ᵐ[GaussMeasure n] fun x => a - (η : EuclideanSpace ℝ (Fin n) → ℝ) x := by
    filter_upwards [Lp.coeFn_sub (a • HermiteL2 (0 : Fin n → ℕ)) η,
      Lp.coeFn_smul a (HermiteL2 (0 : Fin n → ℕ)), HermiteL2ZeroAEOne] with x hx hy hz
    rw [hgdef, hx]
    simp only [Pi.sub_apply]
    rw [hy]
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [hz]
    ring
  refine ⟨u, hdom, g, hu.2, ?_, ?_, ?_, ?_, hmeas, hloc, hu, hmin, ?_⟩
  · -- `F = g + Bu`
    rw [hsqrt, hgdef]
    abel
  · -- pointwise bounds on `g`
    filter_upwards [hbd, hgpt] with x hx hgx
    obtain ⟨hx1, hx2⟩ := hx
    rw [hgx]
    refine ⟨?_, by linarith⟩
    rcases le_or_gt (a - (F : EuclideanSpace ℝ (Fin n) → ℝ) x) 0 with h | h
    · rw [max_eq_right h] at hx2
      have hmr : min ((F : EuclideanSpace ℝ (Fin n) → ℝ) x) a ≤ a := min_le_right _ _
      linarith
    · rw [max_eq_left h.le] at hx2
      have hml : min ((F : EuclideanSpace ℝ (Fin n) → ℝ) x) a
          ≤ (F : EuclideanSpace ℝ (Fin n) → ℝ) x := min_le_left _ _
      linarith
  · -- mass of `g`
    rw [← hmass]
    exact integral_congr_ae hgpt
  · -- `g = a` on the contact set
    filter_upwards [hcompl, hgpt] with x hx hgx hux
    rw [hgx, hx hux, sub_zero]
  · -- uniqueness of the minimizer
    intro u' hu' hmin'
    exact ObstacleMinimizerUnique F m a hm ha u' u hu' hu hmin' hmin
