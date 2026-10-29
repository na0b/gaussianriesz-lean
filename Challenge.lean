module

public import Mathlib.MeasureTheory.Measure.WithDensity
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
public import Mathlib.MeasureTheory.Function.StronglyMeasurable.Lp
public import Mathlib.Analysis.InnerProductSpace.l2Space
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import Mathlib.RingTheory.Polynomial.Hermite.Gaussian
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Topology.Algebra.Support
public import Mathlib.Analysis.Normed.Lp.lpSpace
public import Mathlib.Analysis.Convex.Integral
public import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
public import Mathlib.Analysis.Complex.TaylorSeries
public import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
public import Mathlib.Analysis.Calculus.ContDiff.Convolution
public import Mathlib.Analysis.Calculus.BumpFunction.Convolution
public import Mathlib.MeasureTheory.Function.ContinuousMapDense
public import Mathlib.Analysis.Normed.Module.WeakDual
public import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform

/-!
# A dimension-free weak-type (1,1) bound for the Gaussian Riesz transforms

Statement of record for a Lean 4 formalization of

> Cristian E. Gutiérrez and Juan J. Manfredi, *A direct obstacle proof of a dimension-free
> weak-type (1,1) bound for the Gaussian Riesz transforms*, arXiv:2610.26478 (2026).

Setting (paper, §2): `dγₙ = π^{-n/2} e^{-|x|²} dx` on `ℝⁿ`, the Ornstein–Uhlenbeck operator
`L = -½Δ + x·∇` (diagonal in the Hermite basis, `L h_α = |α| h_α`), the normalized gradient
`D = 2^{-1/2}∇`, `B = L^{1/2}`, and the vector Riesz transform `R_γ = D L^{-1/2} Π₀`, where `Π₀`
removes the mean. With this normalization `‖R_γ v‖ = ‖Π₀ v‖` on `L²(γₙ)`.

Main results stated below (all for every dimension `n`, with constants independent of `n`):

* `GaussianRiesz.endpoint_theorem` (Theorem 5.1): `R_γ` has exactly one linear extension `T` from
  `L²(γₙ)` to `L¹(γₙ)`, with values in a.e.-classes of `ℝⁿ`-valued functions, satisfying
  `t · γₙ{|Tf| > t} ≤ 2 ‖f‖₁` for all `t > 0`.
* `GaussianRiesz.obstacle_decomposition`, `…_unique`, `GaussianRiesz.sqrt_domain_sobolev`
  (Theorem 3.1): the Gaussian obstacle (Calderón–Zygmund-type) decomposition `F = g + Bu` and its
  uniqueness, and `Dom(B) ⊆ W^{1,2}(γₙ)` with `‖Bv‖ = ‖Dv‖`.
* `GaussianRiesz.pv_identification` (Proposition 5.3): the extension is given a.e. by the
  principal-value integrals against the Gaussian Riesz kernels, and the weak-type bound holds for
  any a.e. limit of those truncations.
* `GaussianRiesz.coordinate_endpoint_bound`, `…spectral_normalization_bound`,
  `…unnormalized_measure_invariance` (Corollary 5.4): the coordinatewise bound, the bound for the
  historical normalization `-√2 T`, and invariance under rescaling the measure.
* `GaussianRiesz.complex_endpoint_theorem` (Corollary 5.5): the complex-valued version, constant
  `8/π`.

Only Mathlib is imported. The definitions below are copied verbatim from the development, and
Comparator checks that they agree with it. Four supporting facts are stated with `sorry` because
definitions depend on them (`γₙ` is a probability measure; Hermite functions are in `L²(γₙ)`, are
orthonormal, and are complete); they are proved in the development and checked by Comparator as
part of this submission.
-/

@[expose] public section

section GaussMeasure
open MeasureTheory

/-- The Gaussian probability measure `dγₙ = π^{-n/2} e^{-|x|²} dx` on `ℝⁿ` (paper, §2). The associated
Ornstein–Uhlenbeck operator is `L = -½Δ + x·∇`. -/
noncomputable def GaussianRiesz.GaussMeasure (n : ℕ) : Measure (EuclideanSpace ℝ (Fin n)) :=
  volume.withDensity
    (fun x => ENNReal.ofReal (Real.pi ^ (-(n : ℝ) / 2) * Real.exp (-‖x‖ ^ 2)))

end GaussMeasure

section GaussIsProb
open MeasureTheory

/-- `γₙ` is a probability measure (a standard Gaussian integral). Stated here because `GaussianRiesz.ToL1` uses it;
proved in the development. -/
instance GaussianRiesz.GaussIsProb (n : ℕ) : IsProbabilityMeasure (GaussianRiesz.GaussMeasure n) := by
  sorry

end GaussIsProb

section Hermite1

/-- The normalized one-dimensional Hermite function `h_k(x) = He_k(√2 x)/√(k!)`, where `He_k` is
Mathlib's (probabilists') Hermite polynomial `Polynomial.hermite k`. These are orthonormal in
`L²(π^{-1/2} e^{-x²} dx)`. -/
noncomputable def GaussianRiesz.Hermite1 (k : ℕ) (x : ℝ) : ℝ :=
  Polynomial.aeval (Real.sqrt 2 * x) (Polynomial.hermite k) / Real.sqrt (Nat.factorial k)

end Hermite1

section MultiIndexSum

/-- The length `|α| = α₁ + ⋯ + αₙ` of a multi-index `α : Fin n → ℕ`. -/
def GaussianRiesz.MultiIndexSum {n : ℕ} (α : Fin n → ℕ) : ℕ :=
  ∑ j, α j

end MultiIndexSum

section HermiteFun

/-- The tensor-product Hermite function `h_α(x) = ∏ⱼ h_{αⱼ}(xⱼ)` on `ℝⁿ`. -/
noncomputable def GaussianRiesz.HermiteFun {n : ℕ} (α : Fin n → ℕ) (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  ∏ j, GaussianRiesz.Hermite1 (α j) (x j)

end HermiteFun

section HermiteFunMemLp
open MeasureTheory

/-- Each `h_α` is square-integrable for `γₙ` (needed to define `GaussianRiesz.HermiteL2`; proved in the development). -/
theorem GaussianRiesz.HermiteFunMemLp {n : ℕ} (α : Fin n → ℕ) :
    MemLp (GaussianRiesz.HermiteFun α) 2 (GaussianRiesz.GaussMeasure n) := by
  sorry

end HermiteFunMemLp

section HermiteL2
open MeasureTheory

/-- `h_α` as an element of the real Hilbert space `L²(γₙ)`. -/
noncomputable def GaussianRiesz.HermiteL2 {n : ℕ} (α : Fin n → ℕ) : Lp ℝ 2 (GaussianRiesz.GaussMeasure n) :=
  MemLp.toLp (GaussianRiesz.HermiteFun α) (GaussianRiesz.HermiteFunMemLp α)

end HermiteL2

section HermiteL2Orthonormal
open MeasureTheory

/-- The Hermite functions are orthonormal in `L²(γₙ)` (proved in the development). -/
theorem GaussianRiesz.HermiteL2Orthonormal (n : ℕ) : Orthonormal ℝ (GaussianRiesz.HermiteL2 (n := n)) := by
  sorry

end HermiteL2Orthonormal

section HermiteL2Complete
open MeasureTheory

/-- The Hermite functions span a dense subspace of `L²(γₙ)` (proved in the development). -/
theorem GaussianRiesz.HermiteL2Complete (n : ℕ) :
    ⊤ ≤ (Submodule.span ℝ (Set.range (GaussianRiesz.HermiteL2 (n := n)))).topologicalClosure := by
  sorry

end HermiteL2Complete

section HermiteBasis
open MeasureTheory

/-- The Hermite Hilbert basis `(h_α)` of `L²(γₙ)`, indexed by multi-indices. It diagonalizes the
Ornstein–Uhlenbeck operator: `L h_α = |α| h_α` (paper, `eq:Hermite`). -/
noncomputable def GaussianRiesz.HermiteBasis (n : ℕ) :
    HilbertBasis (Fin n → ℕ) ℝ (Lp ℝ 2 (GaussianRiesz.GaussMeasure n)) :=
  HilbertBasis.mk (GaussianRiesz.HermiteL2Orthonormal n) (GaussianRiesz.HermiteL2Complete n)

end HermiteBasis

section FracPowCoeff

/-- Hermite coefficients `c_α` multiplied by `|α|^s`, with the `α = 0` coefficient set to `0` (this is
the projection `Π₀` removing the mean). -/
noncomputable def GaussianRiesz.FracPowCoeff {n : ℕ} (s : ℝ) (c : (Fin n → ℕ) → ℝ) : (Fin n → ℕ) → ℝ :=
  fun α => if α = 0 then 0 else (GaussianRiesz.MultiIndexSum α : ℝ) ^ s * c α

end FracPowCoeff

section FracPowDomain
open MeasureTheory

/-- The domain of the spectral power `L^s`: those `v` with `Σ_{α≠0} |α|^{2s} ⟨v,h_α⟩² < ∞`. For `s = 1/2`
this is `Dom(B)`, `B = L^{1/2}`. -/
def GaussianRiesz.FracPowDomain {n : ℕ} (s : ℝ) : Set (Lp ℝ 2 (GaussianRiesz.GaussMeasure n)) :=
  {v | Memℓp (GaussianRiesz.FracPowCoeff s (fun α => (GaussianRiesz.HermiteBasis n).repr v α)) 2}

end FracPowDomain

section FracPow
open MeasureTheory

open scoped Classical in
/-- The spectral power `L^s Π₀ v = Σ_{α≠0} |α|^s ⟨v,h_α⟩ h_α` (paper, §2), defined as `0` off its
domain. `GaussianRiesz.FracPow (1/2)` is the paper's `B = L^{1/2}`, and `GaussianRiesz.FracPow (-1/2)` is `L^{-1/2}Π₀`. -/
noncomputable def GaussianRiesz.FracPow {n : ℕ} (s : ℝ) (v : Lp ℝ 2 (GaussianRiesz.GaussMeasure n)) :
    Lp ℝ 2 (GaussianRiesz.GaussMeasure n) :=
  if h : Memℓp (GaussianRiesz.FracPowCoeff s (fun α => (GaussianRiesz.HermiteBasis n).repr v α)) 2
    then (GaussianRiesz.HermiteBasis n).repr.symm ⟨_, h⟩ else 0

end FracPow

section HasGaussWeakGrad
open MeasureTheory

/-- `G` is a weak gradient of `v` in the distributional sense: `∫ v ∂ⱼφ = -∫ Gⱼ φ` (Lebesgue
integrals) for every smooth compactly supported test function `φ` and every coordinate `j`. -/
def GaussianRiesz.HasGaussWeakGrad {n : ℕ} (v : EuclideanSpace ℝ (Fin n) → ℝ)
    (G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) : Prop :=
  ∀ (j : Fin n) (φ : EuclideanSpace ℝ (Fin n) → ℝ),
    ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      ∫ x, v x * fderiv ℝ φ x (EuclideanSpace.single j 1) = -∫ x, G x j * φ x

end HasGaussWeakGrad

section SobolevW12
open MeasureTheory

/-- The Gaussian Sobolev space `W^{1,2}(γₙ)`: those `v ∈ L²(γₙ)` with a weak gradient of the form
`√2·G`, `G ∈ L²(γₙ; ℝⁿ)`. The factor reflects the paper's normalized gradient `D = 2^{-1/2}∇`. -/
def GaussianRiesz.SobolevW12 (n : ℕ) : Set (Lp ℝ 2 (GaussianRiesz.GaussMeasure n)) :=
  {v | ∃ G : Lp (EuclideanSpace ℝ (Fin n)) 2 (GaussianRiesz.GaussMeasure n),
    GaussianRiesz.HasGaussWeakGrad (v : EuclideanSpace ℝ (Fin n) → ℝ)
      (fun x => Real.sqrt 2 •
        (G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) x)}

end SobolevW12

section GaussD
open MeasureTheory

open scoped Classical in
/-- The normalized gradient `D v = 2^{-1/2} ∇v ∈ L²(γₙ; ℝⁿ)` of `v ∈ W^{1,2}(γₙ)` (weak gradients
are unique, so the choice is canonical); `0` outside `W^{1,2}`. -/
noncomputable def GaussianRiesz.GaussD {n : ℕ} (v : Lp ℝ 2 (GaussianRiesz.GaussMeasure n)) :
    Lp (EuclideanSpace ℝ (Fin n)) 2 (GaussianRiesz.GaussMeasure n) :=
  if h : v ∈ GaussianRiesz.SobolevW12 n then h.choose else 0

end GaussD

section ToL1
open MeasureTheory

/-- The inclusion `L²(γₙ) → L¹(γₙ)` (a contraction, since `γₙ` is a probability measure). -/
noncomputable def GaussianRiesz.ToL1 {n : ℕ} (v : Lp ℝ 2 (GaussianRiesz.GaussMeasure n)) : Lp ℝ 1 (GaussianRiesz.GaussMeasure n) :=
  MemLp.toLp (v : EuclideanSpace ℝ (Fin n) → ℝ) ((Lp.memLp v).mono_exponent (by norm_num))

end ToL1

section ComplexToL1
open MeasureTheory

/-- The inclusion `L²(γₙ; ℂ) → L¹(γₙ; ℂ)`. -/
noncomputable def GaussianRiesz.ComplexToL1 {n : ℕ} (v : Lp ℂ 2 (GaussianRiesz.GaussMeasure n)) :
    Lp ℂ 1 (GaussianRiesz.GaussMeasure n) :=
  MemLp.toLp (v : EuclideanSpace ℝ (Fin n) → ℂ) ((Lp.memLp v).mono_exponent (by norm_num))

end ComplexToL1

section RieszTransform
open MeasureTheory

/-- The vector Gaussian Riesz transform `R_γ = D L^{-1/2} Π₀` on real `L²(γₙ)` with the paper's
energy normalization, so that `‖R_γ v‖ = ‖Π₀ v‖`. -/
noncomputable def GaussianRiesz.RieszTransform {n : ℕ} (f : Lp ℝ 2 (GaussianRiesz.GaussMeasure n)) :
    Lp (EuclideanSpace ℝ (Fin n)) 2 (GaussianRiesz.GaussMeasure n) :=
  GaussianRiesz.GaussD (GaussianRiesz.FracPow (-(1 : ℝ) / 2) f)

end RieszTransform

section ComplexRieszTransform
open MeasureTheory

/-- The complex Riesz transform: `R_γ` applied to the real and imaginary parts separately,
`R_γ(Re v) + i R_γ(Im v)`, with values in `L²(γₙ; ℂⁿ)`. -/
noncomputable def GaussianRiesz.ComplexRieszTransform {n : ℕ} (v : Lp ℂ 2 (GaussianRiesz.GaussMeasure n)) :
    Lp (EuclideanSpace ℂ (Fin n)) 2 (GaussianRiesz.GaussMeasure n) :=
  ((PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n => ℂ)).symm.toContinuousLinearMap.comp
      (ContinuousLinearMap.pi fun i => Complex.ofRealCLM.comp (EuclideanSpace.proj i))).compLp
        (GaussianRiesz.RieszTransform (Complex.reCLM.compLp v))
  + Complex.I •
      (((PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n => ℂ)).symm.toContinuousLinearMap.comp
        (ContinuousLinearMap.pi fun i => Complex.ofRealCLM.comp (EuclideanSpace.proj i))).compLp
          (GaussianRiesz.RieszTransform (Complex.imCLM.compLp v)))

end ComplexRieszTransform

section Energy
open MeasureTheory

/-- The energy `𝓔(v) = Σ_{α≠0} |α|^{1/2} ⟨v,h_α⟩² ∈ [0, ∞]`, the quadratic form `⟨Bv, v⟩` of `B = L^{1/2}`
(finite exactly on the form domain `Dom(L^{1/4})`). -/
noncomputable def GaussianRiesz.Energy {n : ℕ} (v : Lp ℝ 2 (GaussianRiesz.GaussMeasure n)) : ENNReal :=
  ∑' α : {α : Fin n → ℕ // α ≠ 0},
    ENNReal.ofReal ((GaussianRiesz.MultiIndexSum (α : Fin n → ℕ) : ℝ) ^ ((1 : ℝ) / 2)
      * ((GaussianRiesz.HermiteBasis n).repr v (α : Fin n → ℕ)) ^ 2)

end Energy

section ObstacleFunctional
open MeasureTheory

/-- The obstacle functional `J(v) = ½𝓔(v) + ∫ (a - F) v dγₙ` (paper, `eq:functional`). -/
noncomputable def GaussianRiesz.ObstacleFunctional {n : ℕ} (F : Lp ℝ 2 (GaussianRiesz.GaussMeasure n)) (a : ℝ)
    (v : Lp ℝ 2 (GaussianRiesz.GaussMeasure n)) : ℝ :=
  (GaussianRiesz.Energy v).toReal / 2
    + ∫ x, (a - (F : EuclideanSpace ℝ (Fin n) → ℝ) x) * (v : EuclideanSpace ℝ (Fin n) → ℝ) x
        ∂(GaussianRiesz.GaussMeasure n)

end ObstacleFunctional

section ObstacleCone
open MeasureTheory

/-- The admissible cone `𝒦 = {v : 𝓔(v) < ∞, v ≥ 0 a.e.}` of the obstacle problem (paper, `eq:cone`). -/
def GaussianRiesz.ObstacleCone (n : ℕ) : Set (Lp ℝ 2 (GaussianRiesz.GaussMeasure n)) :=
  {v | GaussianRiesz.Energy v ≠ ⊤ ∧ 0 ≤ᵐ[GaussianRiesz.GaussMeasure n] (v : EuclideanSpace ℝ (Fin n) → ℝ)}

end ObstacleCone

section GaussRieszKernel
open MeasureTheory

/-- The `j`-th Gaussian Riesz kernel (paper, §5):
`K_j(x,y) = √2 π^{-(n+1)/2} ∫₀¹ (y_j - r x_j) / ((1-r²)^{n/2+1} √(-log r)) · e^{-|rx-y|²/(1-r²)} dr`. -/
noncomputable def GaussianRiesz.GaussRieszKernel {n : ℕ} (j : Fin n)
    (x y : EuclideanSpace ℝ (Fin n)) : ℝ :=
  Real.sqrt 2 * Real.pi ^ (-((n : ℝ) + 1) / 2) *
    ∫ r in Set.Ioo (0 : ℝ) 1,
      (y j - r * x j) / ((1 - r ^ 2) ^ ((n : ℝ) / 2 + 1) * Real.sqrt (-Real.log r))
        * Real.exp (-‖r • x - y‖ ^ 2 / (1 - r ^ 2))

end GaussRieszKernel

section obstacle_decomposition
open MeasureTheory

/-- **Theorem 3.1 (Gaussian obstacle decomposition), existence and minimization.** For nonnegative
`F ∈ L²(γₙ)` with mean `m` and any height `a > m` there are `u ∈ Dom(B)` and `g ∈ L²(γₙ)` with
`u ≥ 0`, `F = g + Bu`, `min(F, a) ≤ g ≤ a` a.e., `∫ g = m`, `g = a` a.e. on `Ω = {u > 0}`,
`a γₙ(Ω) ≤ m`, `Du = 0` a.e. on `{u ≤ 0}`; moreover `u` lies in the cone `𝒦` and is the unique
minimizer of the obstacle functional `J` over `𝒦`. -/
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
  sorry

end obstacle_decomposition

section obstacle_decomposition_unique
open MeasureTheory

/-- **Theorem 3.1, uniqueness.** Two decompositions `F = gᵢ + Buᵢ` with `uᵢ ∈ Dom(B)`, `uᵢ ≥ 0`,
`gᵢ ≤ a`, and `gᵢ = a` a.e. on `{uᵢ > 0}` coincide: `u₁ = u₂` and `g₁ = g₂`. -/
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
  sorry

end obstacle_decomposition_unique

section sqrt_domain_sobolev
open MeasureTheory

/-- **Theorem 3.1, the identification `Dom(B) ⊆ W^{1,2}(γₙ)`.** Every `v ∈ Dom(B)` has a weak gradient
in `L²(γₙ)`, and `‖Bv‖ = ‖Dv‖`. -/
theorem GaussianRiesz.sqrt_domain_sobolev {n : ℕ} (v : Lp ℝ 2 (GaussianRiesz.GaussMeasure n))
    (hv : v ∈ GaussianRiesz.FracPowDomain ((1 : ℝ) / 2)) :
    v ∈ GaussianRiesz.SobolevW12 n ∧ ‖GaussianRiesz.FracPow ((1 : ℝ) / 2) v‖ = ‖GaussianRiesz.GaussD v‖ := by
  sorry

end sqrt_domain_sobolev

section endpoint_theorem
open MeasureTheory

/-- **Theorem 5.1 (dimension-free weak type (1,1)).** There is exactly one linear map
`T : L¹(γₙ) → L⁰(γₙ; ℝⁿ)` extending the Riesz transform `R_γ` from `L²(γₙ)` and satisfying
`t · γₙ{x : |Tf(x)| > t} ≤ 2‖f‖_{L¹(γₙ)}` for every `t > 0`; the constant `2` does not depend on `n`. -/
theorem GaussianRiesz.endpoint_theorem {n : ℕ} :
    ∃! T : Lp ℝ 1 (GaussianRiesz.GaussMeasure n) →ₗ[ℝ]
        (EuclideanSpace ℝ (Fin n) →ₘ[GaussianRiesz.GaussMeasure n] EuclideanSpace ℝ (Fin n)),
      (∀ v : Lp ℝ 2 (GaussianRiesz.GaussMeasure n),
          T (GaussianRiesz.ToL1 v) = (GaussianRiesz.RieszTransform v : EuclideanSpace ℝ (Fin n)
            →ₘ[GaussianRiesz.GaussMeasure n] EuclideanSpace ℝ (Fin n)))
        ∧ ∀ (f : Lp ℝ 1 (GaussianRiesz.GaussMeasure n)) (t : ℝ), 0 < t →
            ENNReal.ofReal t * GaussianRiesz.GaussMeasure n {x | t < ‖T f x‖}
              ≤ ENNReal.ofReal (2 * ‖f‖) := by
  sorry

end endpoint_theorem

section pv_identification
open MeasureTheory
open scoped ENNReal

/-- **Proposition 5.3 (principal-value realization).** If `T` is the extension of Theorem 5.1, then
for every `f ∈ L¹(γₙ)` and a.e. `x`, each coordinate `(Tf)_j(x)` is the limit as `ε → 0⁺` of the
truncated integrals `∫_{|x-y|>ε} K_j(x,y) f(y) dy` (Lebesgue measure); and any a.e. limit `F` of
these truncations satisfies the same weak-type bound with constant `2`. -/
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
  sorry

end pv_identification

section coordinate_endpoint_bound
open MeasureTheory

/-- **Corollary 5.4 (coordinates).** Each coordinate `(Tf)_j` of the extension satisfies
`t · γₙ{|(Tf)_j| > t} ≤ 2‖f‖₁`. -/
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
  sorry

end coordinate_endpoint_bound

section spectral_normalization_bound
open MeasureTheory

/-- **Corollary 5.4 (historical normalization).** The operator `𝓡 = -∇L^{-1/2}Π₀ = -√2 R_γ` of the
historical spectral convention (paper, `eq:FGS-spectral`), extended to `L¹` as `-√2 T`, satisfies
the weak-type bound with constant `2√2`. -/
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
  sorry

end spectral_normalization_bound

section unnormalized_measure_invariance
open MeasureTheory

/-- **Corollary 5.4 (unnormalized measure).** The bounds of Theorem 5.1 and Corollary 5.4 hold with
the same constants when `γₙ` is replaced by `c·γₙ` for any `c > 0` (both the measure of the level
set and the `L¹` norm are taken with respect to `c·γₙ`). The paper's unnormalized measure
`e^{-|x|²} dx` is the case `c = π^{n/2}`. -/
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
  sorry

end unnormalized_measure_invariance

section complex_endpoint_theorem
open MeasureTheory

/-- **Corollary 5.5 (complex-valued functions).** The complex Riesz transform has exactly one linear
extension to `L¹(γₙ; ℂ)` satisfying the weak-type bound with constant `8/π`, for every `n`. -/
theorem GaussianRiesz.complex_endpoint_theorem {n : ℕ} :
    ∃! T : Lp ℂ 1 (GaussianRiesz.GaussMeasure n) →ₗ[ℂ]
        (EuclideanSpace ℝ (Fin n) →ₘ[GaussianRiesz.GaussMeasure n] EuclideanSpace ℂ (Fin n)),
      (∀ v : Lp ℂ 2 (GaussianRiesz.GaussMeasure n),
          T (GaussianRiesz.ComplexToL1 v) = (GaussianRiesz.ComplexRieszTransform v : EuclideanSpace ℝ (Fin n)
            →ₘ[GaussianRiesz.GaussMeasure n] EuclideanSpace ℂ (Fin n)))
        ∧ ∀ (f : Lp ℂ 1 (GaussianRiesz.GaussMeasure n)) (t : ℝ), 0 < t →
            ENNReal.ofReal t * GaussianRiesz.GaussMeasure n {x | t < ‖T f x‖}
              ≤ ENNReal.ofReal ((8 / Real.pi) * ‖f‖) := by
  sorry

end complex_endpoint_theorem
