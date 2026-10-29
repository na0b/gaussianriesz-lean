module

public import GaussianRiesz.Spec

/-!
# Proofs of the Challenge statements

Each theorem below has exactly the statement of its counterpart in `Challenge.lean` (over the
definitions of `GaussianRiesz.Spec`, which are textually identical to those of `Challenge.lean`) and
is proved by the corresponding result of the development; the original definitions unfold to the
same terms. Comparator checks that the statements agree and that only `propext`,
`Classical.choice` and `Quot.sound` are used.
-/

@[expose] public section

section obstacle_decomposition
open MeasureTheory

theorem GaussianRiesz.obstacle_decomposition {n : ℕ} (F : Lp ℝ 2 (GaussianRiesz.GaussMeasure n))
    (hF : 0 ≤ᵐ[GaussianRiesz.GaussMeasure n] (F : EuclideanSpace ℝ (Fin n) → ℝ)) (m a : ℝ)
    (hm : m = ∫ x, (F : EuclideanSpace ℝ (Fin n) → ℝ) x ∂(GaussianRiesz.GaussMeasure n)) (ha : m < a) :
    ∃ u ∈ GaussianRiesz.FracPowDomain ((1 : ℝ) / 2), ∃ g : Lp ℝ 2 (GaussianRiesz.GaussMeasure n),
      (0 ≤ᵐ[GaussianRiesz.GaussMeasure n] (u : EuclideanSpace ℝ (Fin n) → ℝ))
      ∧ F = g + GaussianRiesz.FracPow ((1 : ℝ) / 2) u
      ∧ (∀ᵐ x ∂(GaussianRiesz.GaussMeasure n),
          min ((F : EuclideanSpace ℝ (Fin n) → ℝ) x) a ≤ (g : EuclideanSpace ℝ (Fin n) → ℝ) x
            ∧ (g : EuclideanSpace ℝ (Fin n) → ℝ) x ≤ a)
      ∧ (∫ x, (g : EuclideanSpace ℝ (Fin n) → ℝ) x ∂(GaussianRiesz.GaussMeasure n)) = m
      ∧ (∀ᵐ x ∂(GaussianRiesz.GaussMeasure n), 0 < (u : EuclideanSpace ℝ (Fin n) → ℝ) x
          → (g : EuclideanSpace ℝ (Fin n) → ℝ) x = a)
      ∧ ENNReal.ofReal a * GaussianRiesz.GaussMeasure n {x | 0 < (u : EuclideanSpace ℝ (Fin n) → ℝ) x}
          ≤ ENNReal.ofReal m
      ∧ (∀ᵐ x ∂(GaussianRiesz.GaussMeasure n), (u : EuclideanSpace ℝ (Fin n) → ℝ) x ≤ 0
          → (GaussianRiesz.GaussD u : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) x = 0)
      ∧ u ∈ GaussianRiesz.ObstacleCone n
      ∧ (∀ v ∈ GaussianRiesz.ObstacleCone n, GaussianRiesz.ObstacleFunctional F a u ≤ GaussianRiesz.ObstacleFunctional F a v)
      ∧ (∀ u' ∈ GaussianRiesz.ObstacleCone n,
          (∀ v ∈ GaussianRiesz.ObstacleCone n, GaussianRiesz.ObstacleFunctional F a u' ≤ GaussianRiesz.ObstacleFunctional F a v)
            → u' = u) := by
  exact _root_.ObstacleDecomposition F hF m a hm ha

end obstacle_decomposition

section obstacle_decomposition_unique
open MeasureTheory

theorem GaussianRiesz.obstacle_decomposition_unique {n : ℕ} (F : Lp ℝ 2 (GaussianRiesz.GaussMeasure n))
    (hF : 0 ≤ᵐ[GaussianRiesz.GaussMeasure n] (F : EuclideanSpace ℝ (Fin n) → ℝ)) (m a : ℝ)
    (hm : m = ∫ x, (F : EuclideanSpace ℝ (Fin n) → ℝ) x ∂(GaussianRiesz.GaussMeasure n)) (ha : m < a)
    (u₁ u₂ : Lp ℝ 2 (GaussianRiesz.GaussMeasure n))
    (h₁dom : u₁ ∈ GaussianRiesz.FracPowDomain ((1 : ℝ) / 2))
    (h₂dom : u₂ ∈ GaussianRiesz.FracPowDomain ((1 : ℝ) / 2))
    (g₁ g₂ : Lp ℝ 2 (GaussianRiesz.GaussMeasure n))
    (h₁nn : 0 ≤ᵐ[GaussianRiesz.GaussMeasure n] (u₁ : EuclideanSpace ℝ (Fin n) → ℝ))
    (h₂nn : 0 ≤ᵐ[GaussianRiesz.GaussMeasure n] (u₂ : EuclideanSpace ℝ (Fin n) → ℝ))
    (h₁eq : F = g₁ + GaussianRiesz.FracPow ((1 : ℝ) / 2) u₁)
    (h₂eq : F = g₂ + GaussianRiesz.FracPow ((1 : ℝ) / 2) u₂)
    (h₁le : ∀ᵐ x ∂(GaussianRiesz.GaussMeasure n), (g₁ : EuclideanSpace ℝ (Fin n) → ℝ) x ≤ a)
    (h₂le : ∀ᵐ x ∂(GaussianRiesz.GaussMeasure n), (g₂ : EuclideanSpace ℝ (Fin n) → ℝ) x ≤ a)
    (h₁ct : ∀ᵐ x ∂(GaussianRiesz.GaussMeasure n), 0 < (u₁ : EuclideanSpace ℝ (Fin n) → ℝ) x
        → (g₁ : EuclideanSpace ℝ (Fin n) → ℝ) x = a)
    (h₂ct : ∀ᵐ x ∂(GaussianRiesz.GaussMeasure n), 0 < (u₂ : EuclideanSpace ℝ (Fin n) → ℝ) x
        → (g₂ : EuclideanSpace ℝ (Fin n) → ℝ) x = a) :
    u₁ = u₂ ∧ g₁ = g₂ := by
  exact _root_.ObstacleDecompositionUnique F hF m a hm ha u₁ u₂ h₁dom h₂dom g₁ g₂ h₁nn h₂nn h₁eq h₂eq h₁le h₂le h₁ct h₂ct

end obstacle_decomposition_unique

section sqrt_domain_sobolev
open MeasureTheory

theorem GaussianRiesz.sqrt_domain_sobolev {n : ℕ} (v : Lp ℝ 2 (GaussianRiesz.GaussMeasure n))
    (hv : v ∈ GaussianRiesz.FracPowDomain ((1 : ℝ) / 2)) :
    v ∈ GaussianRiesz.SobolevW12 n ∧ ‖GaussianRiesz.FracPow ((1 : ℝ) / 2) v‖ = ‖GaussianRiesz.GaussD v‖ := by
  exact _root_.SqrtDomainSobolev v hv

end sqrt_domain_sobolev

section endpoint_theorem
open MeasureTheory

theorem GaussianRiesz.endpoint_theorem {n : ℕ} :
    ∃! T : Lp ℝ 1 (GaussianRiesz.GaussMeasure n) →ₗ[ℝ]
        (EuclideanSpace ℝ (Fin n) →ₘ[GaussianRiesz.GaussMeasure n] EuclideanSpace ℝ (Fin n)),
      (∀ v : Lp ℝ 2 (GaussianRiesz.GaussMeasure n),
          T (GaussianRiesz.ToL1 v) = (GaussianRiesz.RieszTransform v : EuclideanSpace ℝ (Fin n)
            →ₘ[GaussianRiesz.GaussMeasure n] EuclideanSpace ℝ (Fin n)))
        ∧ ∀ (f : Lp ℝ 1 (GaussianRiesz.GaussMeasure n)) (t : ℝ), 0 < t →
            ENNReal.ofReal t * GaussianRiesz.GaussMeasure n {x | t < ‖T f x‖}
              ≤ ENNReal.ofReal (2 * ‖f‖) := by
  exact _root_.EndpointTheorem 

end endpoint_theorem

section pv_identification
open MeasureTheory
open scoped ENNReal

theorem GaussianRiesz.pv_identification {n : ℕ}
    (T : Lp ℝ 1 (GaussianRiesz.GaussMeasure n) →ₗ[ℝ]
      (EuclideanSpace ℝ (Fin n) →ₘ[GaussianRiesz.GaussMeasure n] EuclideanSpace ℝ (Fin n)))
    (hext : ∀ v : Lp ℝ 2 (GaussianRiesz.GaussMeasure n),
      T (GaussianRiesz.ToL1 v) = (GaussianRiesz.RieszTransform v : EuclideanSpace ℝ (Fin n)
        →ₘ[GaussianRiesz.GaussMeasure n] EuclideanSpace ℝ (Fin n)))
    (hT : ∀ (f : Lp ℝ 1 (GaussianRiesz.GaussMeasure n)) (t : ℝ), 0 < t →
      ENNReal.ofReal t * GaussianRiesz.GaussMeasure n {x | t < ‖T f x‖} ≤ ENNReal.ofReal (2 * ‖f‖))
    (f : Lp ℝ 1 (GaussianRiesz.GaussMeasure n)) :
    (∀ᵐ x ∂(GaussianRiesz.GaussMeasure n), ∀ j : Fin n,
        Filter.Tendsto
          (fun ε : ℝ => ∫ y in {y : EuclideanSpace ℝ (Fin n) | ε < ‖x - y‖},
            GaussianRiesz.GaussRieszKernel j x y * (f : EuclideanSpace ℝ (Fin n) → ℝ) y)
          (nhdsWithin 0 (Set.Ioi 0)) (nhds (T f x j)))
      ∧ (∀ F : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n),
          (∀ᵐ x ∂(GaussianRiesz.GaussMeasure n), ∀ j : Fin n,
              Filter.Tendsto
                (fun ε : ℝ => ∫ y in {y : EuclideanSpace ℝ (Fin n) | ε < ‖x - y‖},
                  GaussianRiesz.GaussRieszKernel j x y * (f : EuclideanSpace ℝ (Fin n) → ℝ) y)
                (nhdsWithin 0 (Set.Ioi 0)) (nhds (F x j))) →
          ∀ t : ℝ, 0 < t →
            ENNReal.ofReal t * GaussianRiesz.GaussMeasure n {x | t < ‖F x‖}
              ≤ ENNReal.ofReal (2 * ‖f‖)) := by
  exact _root_.PVIdentification T hext hT f

end pv_identification

section coordinate_endpoint_bound
open MeasureTheory

theorem GaussianRiesz.coordinate_endpoint_bound {n : ℕ}
    (T : Lp ℝ 1 (GaussianRiesz.GaussMeasure n) →ₗ[ℝ]
      (EuclideanSpace ℝ (Fin n) →ₘ[GaussianRiesz.GaussMeasure n] EuclideanSpace ℝ (Fin n)))
    (hext : ∀ v : Lp ℝ 2 (GaussianRiesz.GaussMeasure n),
      T (GaussianRiesz.ToL1 v) = (GaussianRiesz.RieszTransform v : EuclideanSpace ℝ (Fin n)
        →ₘ[GaussianRiesz.GaussMeasure n] EuclideanSpace ℝ (Fin n)))
    (hT : ∀ (f : Lp ℝ 1 (GaussianRiesz.GaussMeasure n)) (t : ℝ), 0 < t →
      ENNReal.ofReal t * GaussianRiesz.GaussMeasure n {x | t < ‖T f x‖} ≤ ENNReal.ofReal (2 * ‖f‖))
    (f : Lp ℝ 1 (GaussianRiesz.GaussMeasure n)) (j : Fin n) (t : ℝ) (ht : 0 < t) :
    ENNReal.ofReal t * GaussianRiesz.GaussMeasure n {x | t < |T f x j|}
      ≤ ENNReal.ofReal (2 * ‖f‖) := by
  exact _root_.CoordinateEndpointBound T hext hT f j t ht

end coordinate_endpoint_bound

section spectral_normalization_bound
open MeasureTheory

theorem GaussianRiesz.spectral_normalization_bound {n : ℕ}
    (T : Lp ℝ 1 (GaussianRiesz.GaussMeasure n) →ₗ[ℝ]
      (EuclideanSpace ℝ (Fin n) →ₘ[GaussianRiesz.GaussMeasure n] EuclideanSpace ℝ (Fin n)))
    (hext : ∀ v : Lp ℝ 2 (GaussianRiesz.GaussMeasure n),
      T (GaussianRiesz.ToL1 v) = (GaussianRiesz.RieszTransform v : EuclideanSpace ℝ (Fin n)
        →ₘ[GaussianRiesz.GaussMeasure n] EuclideanSpace ℝ (Fin n)))
    (hT : ∀ (f : Lp ℝ 1 (GaussianRiesz.GaussMeasure n)) (t : ℝ), 0 < t →
      ENNReal.ofReal t * GaussianRiesz.GaussMeasure n {x | t < ‖T f x‖} ≤ ENNReal.ofReal (2 * ‖f‖))
    (f : Lp ℝ 1 (GaussianRiesz.GaussMeasure n)) (t : ℝ) (ht : 0 < t) :
    ENNReal.ofReal t * GaussianRiesz.GaussMeasure n
        {x | t < ‖((-Real.sqrt 2) • T) f x‖}
      ≤ ENNReal.ofReal (2 * Real.sqrt 2 * ‖f‖) := by
  exact _root_.SpectralNormalizationBound T hext hT f t ht

end spectral_normalization_bound

section unnormalized_measure_invariance
open MeasureTheory

theorem GaussianRiesz.unnormalized_measure_invariance {n : ℕ}
    (T : Lp ℝ 1 (GaussianRiesz.GaussMeasure n) →ₗ[ℝ]
      (EuclideanSpace ℝ (Fin n) →ₘ[GaussianRiesz.GaussMeasure n] EuclideanSpace ℝ (Fin n)))
    (hext : ∀ v : Lp ℝ 2 (GaussianRiesz.GaussMeasure n),
      T (GaussianRiesz.ToL1 v) = (GaussianRiesz.RieszTransform v : EuclideanSpace ℝ (Fin n)
        →ₘ[GaussianRiesz.GaussMeasure n] EuclideanSpace ℝ (Fin n)))
    (hT : ∀ (f : Lp ℝ 1 (GaussianRiesz.GaussMeasure n)) (t : ℝ), 0 < t →
      ENNReal.ofReal t * GaussianRiesz.GaussMeasure n {x | t < ‖T f x‖} ≤ ENNReal.ofReal (2 * ‖f‖))
    (c : ℝ) (hc : 0 < c) (f : Lp ℝ 1 (GaussianRiesz.GaussMeasure n)) (t : ℝ) (ht : 0 < t) :
    (∀ j : Fin n,
        ENNReal.ofReal t * (ENNReal.ofReal c • GaussianRiesz.GaussMeasure n) {x | t < |T f x j|}
          ≤ ENNReal.ofReal (2 * ∫ x, |(f : EuclideanSpace ℝ (Fin n) → ℝ) x|
              ∂(ENNReal.ofReal c • GaussianRiesz.GaussMeasure n)))
      ∧ ENNReal.ofReal t * (ENNReal.ofReal c • GaussianRiesz.GaussMeasure n)
            {x | t < ‖((-Real.sqrt 2) • T) f x‖}
          ≤ ENNReal.ofReal (2 * Real.sqrt 2 * ∫ x,
              |(f : EuclideanSpace ℝ (Fin n) → ℝ) x|
                ∂(ENNReal.ofReal c • GaussianRiesz.GaussMeasure n)) := by
  exact _root_.UnnormalizedMeasureInvariance T hext hT c hc f t ht

end unnormalized_measure_invariance

section complex_endpoint_theorem
open MeasureTheory

theorem GaussianRiesz.complex_endpoint_theorem {n : ℕ} :
    ∃! T : Lp ℂ 1 (GaussianRiesz.GaussMeasure n) →ₗ[ℂ]
        (EuclideanSpace ℝ (Fin n) →ₘ[GaussianRiesz.GaussMeasure n] EuclideanSpace ℂ (Fin n)),
      (∀ v : Lp ℂ 2 (GaussianRiesz.GaussMeasure n),
          T (GaussianRiesz.ComplexToL1 v) = (GaussianRiesz.ComplexRieszTransform v : EuclideanSpace ℝ (Fin n)
            →ₘ[GaussianRiesz.GaussMeasure n] EuclideanSpace ℂ (Fin n)))
        ∧ ∀ (f : Lp ℂ 1 (GaussianRiesz.GaussMeasure n)) (t : ℝ), 0 < t →
            ENNReal.ofReal t * GaussianRiesz.GaussMeasure n {x | t < ‖T f x‖}
              ≤ ENNReal.ofReal ((8 / Real.pi) * ‖f‖) := by
  exact _root_.ComplexEndpointTheorem 

end complex_endpoint_theorem
