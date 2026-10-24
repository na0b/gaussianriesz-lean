import GaussianRiesz.GaussD
import GaussianRiesz.OneLeMultiIndexSum
import GaussianRiesz.HermiteGradGram
import GaussianRiesz.GaussDLinear
import GaussianRiesz.FracPow
import GaussianRiesz.HermiteFunDeriv
import GaussianRiesz.GaussWeakGradClosed
import GaussianRiesz.HermiteL2Orthonormal
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.InnerProductSpace.l2Space
import GaussianRiesz.GaussWeakGradAECongr
import GaussianRiesz.GaussDWitness
open MeasureTheory
theorem SqrtDomainSobolev {n : ℕ} (v : Lp ℝ 2 (GaussMeasure n))
    (hv : v ∈ FracPowDomain ((1 : ℝ) / 2)) :
    v ∈ SobolevW12 n ∧ ‖FracPow ((1 : ℝ) / 2) v‖ = ‖GaussD v‖ := by
  -- the Hermite gradients: their coordinates and their Gram matrix
  obtain ⟨hstep1, hstep2⟩ := HermiteGradGram n
  -- `Dh_α` as an element of `L²(γₙ;ℝⁿ)`
  set GV : (Fin n → ℕ) → Lp (EuclideanSpace ℝ (Fin n)) 2 (GaussMeasure n) :=
    fun α => GaussD (HermiteL2 α) with hGVdef
  have hGVapp : ∀ α : Fin n → ℕ, GV α = GaussD (HermiteL2 α) := fun _ => rfl
  have hGV0 : GV (0 : Fin n → ℕ) = 0 := by
    rw [hGVapp, MeasureTheory.Lp.eq_zero_iff_ae_eq_zero]
    filter_upwards [(hstep1 (0 : Fin n → ℕ)).2] with x hx
    rw [hx]
    simp
    rfl
  -- the unit-normalized gradients, indexed by the nonzero multi-indices
  set EV : {α : Fin n → ℕ // α ≠ 0} → Lp (EuclideanSpace ℝ (Fin n)) 2 (GaussMeasure n) :=
    fun i => (Real.sqrt (MultiIndexSum i.1))⁻¹ • GV i.1 with hEVdef
  have hEVapp : ∀ i : {α : Fin n → ℕ // α ≠ 0},
      EV i = (Real.sqrt (MultiIndexSum i.1))⁻¹ • GV i.1 := fun _ => rfl
  have hEVon : Orthonormal ℝ EV := by
    have hsq : ∀ i : {α : Fin n → ℕ // α ≠ 0},
        Real.sqrt (MultiIndexSum i.1) * Real.sqrt (MultiIndexSum i.1)
          = (MultiIndexSum i.1 : ℝ) :=
      fun i => Real.mul_self_sqrt (Nat.cast_nonneg _)
    have hpos : ∀ i : {α : Fin n → ℕ // α ≠ 0}, (0:ℝ) < Real.sqrt (MultiIndexSum i.1) :=
      fun i => Real.sqrt_pos.mpr (lt_of_lt_of_le zero_lt_one (OneLeMultiIndexSum i.1 i.2))
    rw [orthonormal_iff_ite]
    intro i j
    rw [hEVapp, hEVapp, real_inner_smul_left, real_inner_smul_right, hGVapp, hGVapp, hstep2]
    by_cases hij : i = j
    · subst hij
      rw [if_pos rfl, if_pos rfl]
      have hs := hsq i
      have hs0 : Real.sqrt (MultiIndexSum i.1) ≠ 0 := (hpos i).ne'
      set s := Real.sqrt (MultiIndexSum i.1) with hsdef
      rw [← hs]
      field_simp
    · have h1 : i.1 ≠ j.1 := fun h => hij (Subtype.ext h)
      rw [if_neg h1, if_neg hij, mul_zero, mul_zero]
  -- **Step 3(a).** `D` of a finite Hermite sum, by `Finset` induction on `GaussDLinear`
  have hstep3A : ∀ (c : (Fin n → ℕ) → ℝ) (S : Finset (Fin n → ℕ)),
      (∑ α ∈ S, c α • HermiteL2 α) ∈ SobolevW12 n
        ∧ GaussD (∑ α ∈ S, c α • HermiteL2 α) = ∑ α ∈ S, c α • GV α := by
    intro c S
    induction S using Finset.induction_on with
    | empty =>
        simp only [Finset.sum_empty]
        have h0 := (GaussDLinear (n := n)).2.2 0
        rw [zero_smul] at h0
        exact h0
    | insert a S ha ih =>
        rw [Finset.sum_insert ha, Finset.sum_insert ha]
        have h1 : (c a • HermiteL2 a) ∈ SobolevW12 n ∧
            GaussD (c a • HermiteL2 a) = c a • GV a := by
          have h2 := (GaussDLinear (n := n)).2.1 (c a) (HermiteL2 a) (hstep1 a).1
          refine ⟨h2.1, ?_⟩
          rw [h2.2, hGVapp]
        have h3 := (GaussDLinear (n := n)).1 _ _ h1.1 ih.1
        exact ⟨h3.1, by rw [h3.2, h1.2, ih.2]⟩
  -- an exhausting monotone sequence of finite sets of multi-indices
  have hTpi : Filter.Tendsto
      (fun N : ℕ => Fintype.piFinset (fun _ : Fin n => Finset.range (N + 1)))
      Filter.atTop Filter.atTop := by
    rw [Filter.tendsto_atTop_atTop]
    intro S
    refine ⟨S.sup (fun α => Finset.univ.sup α), fun M hM α hα => ?_⟩
    rw [Fintype.mem_piFinset]
    intro j
    rw [Finset.mem_range]
    have h1 : α j ≤ Finset.univ.sup α := Finset.le_sup (Finset.mem_univ j)
    have h2 : Finset.univ.sup α ≤ S.sup (fun β => Finset.univ.sup β) := Finset.le_sup hα
    omega

  -- (0) the coefficient family and the value of `L^{1/2} v`
  have hvK : Memℓp
      (FracPowCoeff ((1 : ℝ) / 2) (fun α => (HermiteBasis n).repr v α)) 2 := hv
  have hFPnorm : ‖FracPow ((1 : ℝ) / 2) v‖
      = ‖(⟨_, hvK⟩ : lp (fun _ : Fin n → ℕ => ℝ) 2)‖ := by
    simp only [FracPow]
    rw [dif_pos hvK]
    exact LinearIsometryEquiv.norm_map _ _
  set K : (Fin n → ℕ) → ℝ :=
    FracPowCoeff ((1 : ℝ) / 2) (fun α => (HermiteBasis n).repr v α) with hKdef
  have hK0 : K (0 : Fin n → ℕ) = 0 := by
    rw [hKdef]
    simp [FracPowCoeff]
  have hKval : ∀ α : Fin n → ℕ, α ≠ 0 →
      K α = Real.sqrt (MultiIndexSum α) * (HermiteBasis n).repr v α := by
    intro α hα
    rw [hKdef]
    simp only [FracPowCoeff, if_neg hα]
    rw [Real.sqrt_eq_rpow]
  -- (1) restrict the coefficient family to the nonzero multi-indices
  have hsumK : Summable (fun α : Fin n → ℕ => ‖K α‖ ^ (2 : ENNReal).toReal) :=
    hvK.summable (by norm_num)
  have hF : Memℓp (fun i : {α : Fin n → ℕ // α ≠ 0} => K i.1) 2 :=
    memℓp_gen (hsumK.subtype {α : Fin n → ℕ | α ≠ 0})
  have hsupp : Function.support (fun α : Fin n → ℕ => ‖K α‖ ^ (2 : ENNReal).toReal)
      ⊆ {α : Fin n → ℕ | α ≠ 0} := by
    intro α hα h0
    rw [Function.mem_support] at hα
    rw [h0, hK0] at hα
    simp at hα
  have hnormF : ‖(⟨_, hF⟩ : lp (fun _ : {α : Fin n → ℕ // α ≠ 0} => ℝ) 2)‖
      = ‖(⟨_, hvK⟩ : lp (fun _ : Fin n → ℕ => ℝ) 2)‖ := by
    rw [lp.norm_eq_tsum_rpow (by norm_num), lp.norm_eq_tsum_rpow (by norm_num)]
    congr 1
    exact tsum_subtype_eq_of_support_subset hsupp
  -- (2) the limit gradient, as the image of the coefficient family under the
  -- orthogonal-family isometry attached to the orthonormal rescaled gradients
  set Γ : Lp (EuclideanSpace ℝ (Fin n)) 2 (GaussMeasure n) :=
    (hEVon).orthogonalFamily.linearIsometry ⟨_, hF⟩ with hΓdef
  have hΓnorm : ‖Γ‖ = ‖(⟨_, hvK⟩ : lp (fun _ : Fin n → ℕ => ℝ) 2)‖ := by
    rw [hΓdef, LinearIsometry.norm_map, hnormF]
  have hΓsum0 : HasSum (fun i : {α : Fin n → ℕ // α ≠ 0} => K i.1 • EV i) Γ := by
    have h := (hEVon).orthogonalFamily.hasSum_linearIsometry
      (⟨_, hF⟩ : lp (fun _ : {α : Fin n → ℕ // α ≠ 0} => ℝ) 2)
    simpa only [LinearIsometry.toSpanSingleton_apply] using h
  have hterm : ∀ i : {α : Fin n → ℕ // α ≠ 0},
      K i.1 • EV i = ((HermiteBasis n).repr v i.1) • GV i.1 := by
    intro i
    have hpos : (0:ℝ) < Real.sqrt (MultiIndexSum i.1) :=
      Real.sqrt_pos.mpr (lt_of_lt_of_le zero_lt_one (OneLeMultiIndexSum i.1 i.2))
    rw [hEVapp, smul_smul, hKval i.1 i.2]
    congr 1
    field_simp
  have hΓsum : HasSum
      (fun α : Fin n → ℕ => ((HermiteBasis n).repr v α) • GV α) Γ := by
    refine (hasSum_subtype_iff_of_support_subset (s := {α : Fin n → ℕ | α ≠ 0}) ?_).1 ?_
    · intro α hα h0
      rw [Function.mem_support] at hα
      rw [h0, hGV0, smul_zero] at hα
      exact hα rfl
    · have h2 : HasSum (fun i : {α : Fin n → ℕ // α ≠ 0} =>
          ((HermiteBasis n).repr v i.1) • GV i.1) Γ := by
        simpa only [hterm] using hΓsum0
      exact h2
  -- (3) the Hermite expansion of `v` itself
  have hrepr : ⇑(HermiteBasis n) = HermiteL2 (n := n) := by
    rw [HermiteBasis]
    exact HilbertBasis.coe_mk _ _
  have hvsum : HasSum
      (fun α : Fin n → ℕ => ((HermiteBasis n).repr v α) • HermiteL2 α) v := by
    simpa only [hrepr] using (HermiteBasis n).hasSum_repr v
  -- (4) the two sequences of partial sums
  set T : ℕ → Finset (Fin n → ℕ) :=
    fun N => Fintype.piFinset (fun _ : Fin n => Finset.range (N + 1)) with hTdef
  have hT : Filter.Tendsto T Filter.atTop Filter.atTop := hTpi
  have hvN : Filter.Tendsto
      (fun N => ∑ α ∈ T N, ((HermiteBasis n).repr v α) • HermiteL2 α)
      Filter.atTop (nhds v) := hvsum.comp hT
  have hGN : Filter.Tendsto
      (fun N => ∑ α ∈ T N, ((HermiteBasis n).repr v α) • GV α)
      Filter.atTop (nhds Γ) := hΓsum.comp hT
  -- (5) each partial sum has the corresponding weak gradient
  have hgradN : ∀ N : ℕ, HasGaussWeakGrad
      (((∑ α ∈ T N, ((HermiteBasis n).repr v α) • HermiteL2 α :
          Lp ℝ 2 (GaussMeasure n)) : EuclideanSpace ℝ (Fin n) → ℝ))
      (((Real.sqrt 2 • ∑ α ∈ T N, ((HermiteBasis n).repr v α) • GV α :
          Lp (EuclideanSpace ℝ (Fin n)) 2 (GaussMeasure n)) :
          EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))) := by
    intro N
    obtain ⟨hmemN, hDN⟩ := hstep3A (fun α => (HermiteBasis n).repr v α) (T N)
    have hspec := hmemN.choose_spec
    have hchoose : GaussD (∑ α ∈ T N, ((HermiteBasis n).repr v α) • HermiteL2 α)
        = hmemN.choose := by
      simp only [GaussD]
      rw [dif_pos hmemN]
    refine GaussWeakGradAECongr _ _ _ _ (Filter.EventuallyEq.refl _ _) ?_ hspec
    have h1 : hmemN.choose = ∑ α ∈ T N, ((HermiteBasis n).repr v α) • GV α := by
      rw [← hchoose, hDN]
    rw [h1]
    exact (Lp.coeFn_smul (Real.sqrt 2) _).symm
  -- (6) close up: the weak gradient passes to the limit
  have hgradlim : HasGaussWeakGrad ((v : EuclideanSpace ℝ (Fin n) → ℝ))
      (((Real.sqrt 2 • Γ : Lp (EuclideanSpace ℝ (Fin n)) 2 (GaussMeasure n)) :
        EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))) :=
    GaussWeakGradClosed v (Real.sqrt 2 • Γ) _ _ hgradN hvN (hGN.const_smul (Real.sqrt 2))
  have hgradΓ : HasGaussWeakGrad ((v : EuclideanSpace ℝ (Fin n) → ℝ))
      (fun x => Real.sqrt 2 • (Γ : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) x) := by
    refine GaussWeakGradAECongr _ _ _ _ (Filter.EventuallyEq.refl _ _) ?_ hgradlim
    exact Lp.coeFn_smul (Real.sqrt 2) Γ
  obtain ⟨hmem, hDv⟩ := GaussDWitness v Γ hgradΓ
  refine ⟨hmem, ?_⟩
  rw [hFPnorm, hDv, hΓnorm]
