module

public import GaussianRiesz.ObstacleMultiplier
public import GaussianRiesz.ObstacleCone
public import GaussianRiesz.EnergyBilIsOperator
public import GaussianRiesz.HermiteL2
public import GaussianRiesz.Hermite1Zero
public import GaussianRiesz.HermiteL2Orthonormal
public import GaussianRiesz.L2InnerGaussIntegral
public import GaussianRiesz.HermiteL2ZeroAEOne
public import GaussianRiesz.HermiteBasisVectorFacts

@[expose] public section
open MeasureTheory
-- binder retained for statement fidelity to the paper; intentionally unused in the proof
set_option linter.unusedVariables false
theorem DomainUpgrade {n : ℕ} (F : Lp ℝ 2 (GaussMeasure n)) (a : ℝ)
    (u : Lp ℝ 2 (GaussMeasure n)) (hu : u ∈ ObstacleCone n)
    (η : Lp ℝ 2 (GaussMeasure n))
    (hη : ∀ φ : Lp ℝ 2 (GaussMeasure n), Energy φ ≠ ⊤ →
      ObstacleMultiplier F a u φ
        = ∫ x, (η : EuclideanSpace ℝ (Fin n) → ℝ) x
            * (φ : EuclideanSpace ℝ (Fin n) → ℝ) x ∂(GaussMeasure n)) :
    u ∈ FracPowDomain ((1 : ℝ) / 2)
      ∧ FracPow ((1 : ℝ) / 2) u = F - (a • HermiteL2 (0 : Fin n → ℕ) - η) := by
  -- `hL = F - g` with `g = a·1 - η`, the paper's `h = F - a + η`
  set hL : Lp ℝ 2 (GaussMeasure n) := F - (a • HermiteL2 (0 : Fin n → ℕ) - η) with hLdef
  -- `h₀ = 1` almost everywhere, so `a • h₀` is the constant `a`
  have hLc : (hL : EuclideanSpace ℝ (Fin n) → ℝ) =ᵐ[GaussMeasure n]
      fun x => ((F : EuclideanSpace ℝ (Fin n) → ℝ) x - a)
        + (η : EuclideanSpace ℝ (Fin n) → ℝ) x := by
    rw [hLdef]
    filter_upwards [Lp.coeFn_sub F (a • HermiteL2 (0 : Fin n → ℕ) - η),
      Lp.coeFn_sub (a • HermiteL2 (0 : Fin n → ℕ)) η,
      Lp.coeFn_smul a (HermiteL2 (0 : Fin n → ℕ)), HermiteL2ZeroAEOne] with x e1 e2 e3 e4
    rw [e1, Pi.sub_apply, e2, Pi.sub_apply, e3, Pi.smul_apply, smul_eq_mul, e4, mul_one]
    ring
  -- STEP (a): the representation hypothesis, as the form equation `E(u,φ) = ⟪hL, φ⟫`
  have hFa : MemLp (fun x => (F : EuclideanSpace ℝ (Fin n) → ℝ) x - a) 2 (GaussMeasure n) :=
    (Lp.memLp F).sub (memLp_const a)
  have hform : ∀ φ : Lp ℝ 2 (GaussMeasure n), Energy φ ≠ ⊤ →
      EnergyBil u φ = (inner ℝ hL φ : ℝ) := by
    intro φ hφ
    have e := hη φ hφ
    rw [ObstacleMultiplier] at e
    have hint1 : Integrable (fun x => ((F : EuclideanSpace ℝ (Fin n) → ℝ) x - a)
        * (φ : EuclideanSpace ℝ (Fin n) → ℝ) x) (GaussMeasure n) :=
      hFa.integrable_mul (Lp.memLp φ)
    have hint2 : Integrable (fun x => (η : EuclideanSpace ℝ (Fin n) → ℝ) x
        * (φ : EuclideanSpace ℝ (Fin n) → ℝ) x) (GaussMeasure n) :=
      (Lp.memLp η).integrable_mul (Lp.memLp φ)
    have esum : (inner ℝ hL φ : ℝ)
        = (∫ x, ((F : EuclideanSpace ℝ (Fin n) → ℝ) x - a)
              * (φ : EuclideanSpace ℝ (Fin n) → ℝ) x ∂(GaussMeasure n))
          + ∫ x, (η : EuclideanSpace ℝ (Fin n) → ℝ) x
              * (φ : EuclideanSpace ℝ (Fin n) → ℝ) x ∂(GaussMeasure n) := by
      rw [L2InnerGaussIntegral, ← integral_add hint1 hint2]
      refine integral_congr_ae ?_
      filter_upwards [hLc] with x hx
      rw [hx]
      ring
    rw [esum]
    linarith [e]
  obtain ⟨hbasis, hreprh, hhE⟩ := HermiteBasisVectorFacts n
  -- STEP (b2): the form tested on `h_β` reads off the `L^{1/2}` coefficient of `u`
  have hEb : ∀ β : Fin n → ℕ, EnergyBil u (HermiteL2 β)
      = FracPowCoeff ((1 : ℝ) / 2) (fun α => (HermiteBasis n).repr u α) β := by
    intro β
    simp only [EnergyBil, FracPowCoeff]
    by_cases hβ : β = 0
    · have hzz : ∀ x : {α : Fin n → ℕ // α ≠ 0},
          (MultiIndexSum (x : Fin n → ℕ) : ℝ) ^ ((1 : ℝ) / 2)
              * ((HermiteBasis n).repr u (x : Fin n → ℕ))
              * ((HermiteBasis n).repr (HermiteL2 β) (x : Fin n → ℕ)) = 0 := by
        intro x
        rw [hreprh β (x : Fin n → ℕ), if_neg (by rw [hβ]; exact x.2)]
        ring
      rw [tsum_congr hzz, tsum_zero, if_pos hβ]
    · rw [if_neg hβ, tsum_eq_single (⟨β, hβ⟩ : {α : Fin n → ℕ // α ≠ 0}) ?_]
      · rw [hreprh β β, if_pos rfl]
        ring
      · intro x hx
        rw [hreprh β (x : Fin n → ℕ), if_neg fun hcon => hx (Subtype.ext hcon)]
        ring
  -- the coefficient identity `⟪hL, h_β⟫ = FracPowCoeff (1/2) (repr u) β`, for every `β`
  have hcoef : ∀ β : Fin n → ℕ, (HermiteBasis n).repr hL β
      = FracPowCoeff ((1 : ℝ) / 2) (fun α => (HermiteBasis n).repr u α) β := by
    intro β
    have e := hform (HermiteL2 β) (hhE β)
    rw [hEb β] at e
    rw [e, HilbertBasis.repr_apply_apply, hbasis β]
    exact real_inner_comm _ _
  have hcoefFun : (fun β : Fin n → ℕ => (HermiteBasis n).repr hL β)
      = FracPowCoeff ((1 : ℝ) / 2) (fun α => (HermiteBasis n).repr u α) := funext hcoef
  -- STEP (c): Parseval is structural -- `repr hL` already lies in `ℓ²`
  have hmem : Memℓp (FracPowCoeff ((1 : ℝ) / 2)
      (fun α => (HermiteBasis n).repr u α)) 2 := by
    rw [← hcoefFun]
    exact lp.memℓp ((HermiteBasis n).repr hL)
  refine ⟨hmem, ?_⟩
  -- STEP (d): the operator identity is then forced
  have hFPval : FracPow ((1 : ℝ) / 2) u = (HermiteBasis n).repr.symm ⟨_, hmem⟩ := by
    simp only [FracPow]
    rw [dif_pos hmem]
  have hlpeq : (⟨FracPowCoeff ((1 : ℝ) / 2) (fun α => (HermiteBasis n).repr u α), hmem⟩
      : lp (fun _ : Fin n → ℕ => ℝ) 2) = (HermiteBasis n).repr hL :=
    lp.ext hcoefFun.symm
  rw [hFPval, hlpeq, LinearIsometryEquiv.symm_apply_apply]
