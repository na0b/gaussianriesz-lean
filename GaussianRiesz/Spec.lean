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
public import GaussianRiesz

/-!
# The definitions of `Challenge.lean`, inside the development

Generated from the same source as `Challenge.lean` and kept textually identical to its definitions
section (same Mathlib imports, same declarations in the same order), so that both elaborate to the
same terms, including the names of auxiliary proofs, as Comparator requires. The four supporting
facts are proved here from the development's own results about the original definitions, which
unfold to the same terms.
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
  exact _root_.GaussIsProb n

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
  exact _root_.HermiteFunMemLp α

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
  exact _root_.HermiteL2Orthonormal n

end HermiteL2Orthonormal

section HermiteL2Complete
open MeasureTheory

/-- The Hermite functions span a dense subspace of `L²(γₙ)` (proved in the development). -/
theorem GaussianRiesz.HermiteL2Complete (n : ℕ) :
    ⊤ ≤ (Submodule.span ℝ (Set.range (GaussianRiesz.HermiteL2 (n := n)))).topologicalClosure := by
  exact _root_.HermiteL2Complete n

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
