import GaussianRiesz.MultiplierAPrioriL2Bound
import GaussianRiesz.ObstacleMultiplierLinearOnFormDomain
import GaussianRiesz.HermiteL2Orthonormal
import GaussianRiesz.HermiteL2Complete
import Mathlib.Topology.Algebra.InfiniteSum.Real
import GaussianRiesz.L2InnerGaussIntegral
import GaussianRiesz.HermiteL2ZeroAEOne
import GaussianRiesz.HermiteBasisVectorFacts
open MeasureTheory
theorem MultiplierL2Representation {n : ℕ} (F : Lp ℝ 2 (GaussMeasure n))
    (hF : 0 ≤ᵐ[GaussMeasure n] (F : EuclideanSpace ℝ (Fin n) → ℝ)) (a : ℝ) (ha : 0 < a)
    (u : Lp ℝ 2 (GaussMeasure n)) (hu : u ∈ ObstacleCone n)
    (hmin : ∀ w ∈ ObstacleCone n, ObstacleFunctional F a u ≤ ObstacleFunctional F a w) :
    ∃ η : Lp ℝ 2 (GaussMeasure n), ∀ φ : Lp ℝ 2 (GaussMeasure n), Energy φ ≠ ⊤ →
      ObstacleMultiplier F a u φ
        = ∫ x, (η : EuclideanSpace ℝ (Fin n) → ℝ) x
            * (φ : EuclideanSpace ℝ (Fin n) → ℝ) x ∂(GaussMeasure n) := by
  classical
  have hprob : IsProbabilityMeasure (GaussMeasure n) := GaussIsProb n
  obtain ⟨hmixsum, -, -, hclosed⟩ := EnergyFormBilinear (n := n)
  have huE : Energy u ≠ ⊤ := hu.1
  have c1 : ∀ x : ℝ, ‖x‖ ^ ((2 : ENNReal).toReal) = x ^ (2 : ℕ) := by
    intro x
    rw [show ((2 : ENNReal)).toReal = ((2 : ℕ) : ℝ) from by norm_num, Real.rpow_natCast,
      Real.norm_eq_abs, ← abs_pow, abs_of_nonneg (by positivity)]
  -- the multiplier as the energy form minus a fixed inner product, hence additive and
  obtain ⟨hT, hTadd, hTsmul⟩ := ObstacleMultiplierLinearOnFormDomain F a u huE
  set g : Lp ℝ 2 (GaussMeasure n) := F - a • HermiteL2 (0 : Fin n → ℕ)
  -- STEP 1: the a-priori `L²` bound on the form domain
  have hstep1 := MultiplierAPrioriL2Bound F hF a ha u hu hmin
  obtain ⟨hbasis, hreprh, hhE⟩ := HermiteBasisVectorFacts n
  -- STEP 2: the coefficients of the representing function, written down explicitly
  obtain ⟨c, hcdef⟩ : ∃ c : (Fin n → ℕ) → ℝ, ∀ β : Fin n → ℕ, c β
      = (if β = 0 then 0 else (MultiIndexSum β : ℝ) ^ ((1 : ℝ) / 2)
            * (HermiteBasis n).repr u β)
        - (HermiteBasis n).repr g β := ⟨_, fun β => rfl⟩
  have hcval : ∀ β : Fin n → ℕ, c β = ObstacleMultiplier F a u (HermiteL2 β) := by
    intro β
    rw [hcdef, hT (HermiteL2 β)]
    congr 1
    · rw [EnergyBil]
      by_cases hβ : β = 0
      · have hzz : ∀ x : {α : Fin n → ℕ // α ≠ 0},
            (MultiIndexSum (x : Fin n → ℕ) : ℝ) ^ ((1 : ℝ) / 2)
                * ((HermiteBasis n).repr u (x : Fin n → ℕ))
                * ((HermiteBasis n).repr (HermiteL2 β) (x : Fin n → ℕ)) = 0 := by
          intro x
          rw [hreprh β (x : Fin n → ℕ), if_neg (by rw [hβ]; exact x.2)]
          ring
        rw [if_pos hβ, tsum_congr hzz, tsum_zero]
      · rw [if_neg hβ, tsum_eq_single (⟨β, hβ⟩ : {α : Fin n → ℕ // α ≠ 0}) ?_]
        · rw [hreprh β β, if_pos rfl]
          ring
        · intro x hx
          rw [hreprh β (x : Fin n → ℕ), if_neg fun h => hx (Subtype.ext h)]
          ring
    · rw [real_inner_comm, ← hbasis β, HilbertBasis.repr_apply_apply]
  -- finite Hermite sums have finite energy, and the multiplier reads off their coefficients
  have hfinE : ∀ S : Finset (Fin n → ℕ), Energy (∑ β ∈ S, c β • HermiteL2 β) ≠ ⊤ := by
    intro S
    induction S using Finset.cons_induction with
    | empty =>
        rw [Finset.sum_empty]
        have h := (hclosed u u (0 : ℝ) huE huE).2
        rwa [zero_smul] at h
    | cons β S hβ ih =>
        rw [Finset.sum_cons]
        exact (hclosed _ _ (0 : ℝ)
          ((hclosed (HermiteL2 β) (HermiteL2 β) (c β) (hhE β) (hhE β)).2) ih).1
  have hTfin : ∀ S : Finset (Fin n → ℕ),
      ObstacleMultiplier F a u (∑ β ∈ S, c β • HermiteL2 β) = ∑ β ∈ S, (c β) ^ 2 := by
    intro S
    induction S using Finset.cons_induction with
    | empty =>
        rw [Finset.sum_empty, Finset.sum_empty]
        have h := hTsmul (0 : ℝ) u huE
        rw [zero_smul] at h
        rw [h]
        ring
    | cons β S hβ ih =>
        rw [Finset.sum_cons, Finset.sum_cons,
          hTadd _ _ ((hclosed (HermiteL2 β) (HermiteL2 β) (c β) (hhE β) (hhE β)).2) (hfinE S),
          hTsmul (c β) (HermiteL2 β) (hhE β), ← hcval β, ih]
        ring
  have hnormfin : ∀ S : Finset (Fin n → ℕ),
      ‖∑ β ∈ S, c β • HermiteL2 β‖ ^ 2 = ∑ β ∈ S, (c β) ^ 2 := by
    intro S
    rw [← real_inner_self_eq_norm_sq, (HermiteL2Orthonormal n).inner_sum c c S]
    exact Finset.sum_congr rfl fun β _ => by simp [sq]
  -- the uniform bound on every finite partial sum of squared coefficients
  have hbound : ∀ S : Finset (Fin n → ℕ), ∑ β ∈ S, (c β) ^ 2 ≤ a ^ 2 := by
    intro S
    have hX0 : (0 : ℝ) ≤ ∑ β ∈ S, (c β) ^ 2 := Finset.sum_nonneg fun β _ => sq_nonneg _
    have hnorm : ‖∑ β ∈ S, c β • HermiteL2 β‖ = Real.sqrt (∑ β ∈ S, (c β) ^ 2) := by
      rw [← hnormfin S, Real.sqrt_sq (norm_nonneg _)]
    have hsq : Real.sqrt (∑ β ∈ S, (c β) ^ 2) ^ 2 = ∑ β ∈ S, (c β) ^ 2 := Real.sq_sqrt hX0
    have hs0 : (0 : ℝ) ≤ Real.sqrt (∑ β ∈ S, (c β) ^ 2) := Real.sqrt_nonneg _
    have h1 : ∑ β ∈ S, (c β) ^ 2 ≤ a * Real.sqrt (∑ β ∈ S, (c β) ^ 2) := by
      have h := hstep1 _ (hfinE S)
      rw [hTfin S, hnorm] at h
      exact le_trans (le_abs_self _) h
    rcases eq_or_lt_of_le hs0 with h0 | hpos
    · nlinarith [hsq, ha]
    · have hsa : Real.sqrt (∑ β ∈ S, (c β) ^ 2) ≤ a := by nlinarith
      nlinarith
  have hcsum : Summable (fun β : Fin n → ℕ => (c β) ^ 2) :=
    summable_of_sum_le (fun β => sq_nonneg _) hbound
  have hcmem : Memℓp c 2 := memℓp_gen (hcsum.congr fun β => (c1 (c β)).symm)
  set η : Lp ℝ 2 (GaussMeasure n) := (HermiteBasis n).repr.symm ⟨c, hcmem⟩ with hηdef
  have hreprη : ∀ β : Fin n → ℕ, (HermiteBasis n).repr η β = c β := by
    intro β
    rw [hηdef, LinearIsometryEquiv.apply_symm_apply]
  -- STEP 3: the representation identity, as a splitting of absolutely convergent series
  refine ⟨η, fun φ hφ => ?_⟩
  have hA0 : HasSum (fun x : {α : Fin n → ℕ // α ≠ 0} =>
      (MultiIndexSum (x : Fin n → ℕ) : ℝ) ^ ((1 : ℝ) / 2)
        * ((HermiteBasis n).repr u (x : Fin n → ℕ))
        * ((HermiteBasis n).repr φ (x : Fin n → ℕ))) (EnergyBil u φ) := by
    rw [EnergyBil]
    exact (hmixsum u φ huE hφ).hasSum
  have hsupp : Function.support (fun β : Fin n → ℕ =>
      (if β = 0 then 0 else (MultiIndexSum β : ℝ) ^ ((1 : ℝ) / 2)
          * ((HermiteBasis n).repr u β)) * ((HermiteBasis n).repr φ β))
      ⊆ {α : Fin n → ℕ | α ≠ 0} := by
    intro β hβ
    simp only [Function.mem_support] at hβ
    by_contra hcon
    rw [Set.mem_ofPred_eq, not_not] at hcon
    rw [hcon] at hβ
    simp at hβ
  have hA1 : HasSum (fun β : Fin n → ℕ =>
      (if β = 0 then 0 else (MultiIndexSum β : ℝ) ^ ((1 : ℝ) / 2)
          * ((HermiteBasis n).repr u β)) * ((HermiteBasis n).repr φ β)) (EnergyBil u φ) := by
    refine (hasSum_subtype_iff_of_support_subset hsupp).mp ?_
    refine hA0.congr_fun fun x => ?_
    simp only [Function.comp_apply, if_neg x.2]
  have hB : HasSum (fun β : Fin n → ℕ =>
      ((HermiteBasis n).repr g β) * ((HermiteBasis n).repr φ β)) (inner ℝ g φ : ℝ) := by
    have h := lp.hasSum_inner (𝕜 := ℝ) ((HermiteBasis n).repr g) ((HermiteBasis n).repr φ)
    rw [(HermiteBasis n).repr.inner_map_map g φ] at h
    exact h.congr_fun fun β => by simp [RCLike.inner_apply, mul_comm]
  have hC : HasSum (fun β : Fin n → ℕ => c β * ((HermiteBasis n).repr φ β))
      (EnergyBil u φ - (inner ℝ g φ : ℝ)) := by
    refine (hA1.sub hB).congr_fun fun β => ?_
    rw [hcdef]
    ring
  have hD : HasSum (fun β : Fin n → ℕ => c β * ((HermiteBasis n).repr φ β))
      (inner ℝ η φ : ℝ) := by
    have h := lp.hasSum_inner (𝕜 := ℝ) ((HermiteBasis n).repr η) ((HermiteBasis n).repr φ)
    rw [(HermiteBasis n).repr.inner_map_map η φ] at h
    refine h.congr_fun fun β => ?_
    simp [RCLike.inner_apply, hreprη β, mul_comm]
  rw [hT φ, ← L2InnerGaussIntegral η φ]
  exact hC.unique hD
