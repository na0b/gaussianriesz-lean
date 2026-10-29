module

public import GaussianRiesz.GaussD
public import GaussianRiesz.GaussDWitness
public import GaussianRiesz.GaussWeakGradAECongr
public import GaussianRiesz.HermiteFunDeriv
public import GaussianRiesz.HermiteL2Orthonormal
public import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
public import Mathlib.Analysis.InnerProductSpace.l2Space

@[expose] public section
open MeasureTheory
theorem HermiteGradGram (n : ℕ) :
    (∀ α : Fin n → ℕ, HermiteL2 α ∈ SobolevW12 n ∧
        ((GaussD (HermiteL2 α) : Lp (EuclideanSpace ℝ (Fin n)) 2 (GaussMeasure n)) :
            EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
          =ᵐ[GaussMeasure n] fun x => WithLp.toLp 2 (fun j =>
            Real.sqrt (α j) * HermiteFun (Function.update α j (α j - 1)) x))
      ∧ (∀ α β : Fin n → ℕ,
          (inner ℝ (GaussD (HermiteL2 α)) (GaussD (HermiteL2 β)) : ℝ)
            = if α = β then (MultiIndexSum α : ℝ) else 0) := by
  -- `D h_α` as an explicit function: the `j`th coordinate is `√(α_j) h_{α-e_j}`
  set DF : (Fin n → ℕ) → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) := fun α x =>
    WithLp.toLp 2 (fun j => Real.sqrt (α j) * HermiteFun (Function.update α j (α j - 1)) x)
    with hDFdef
  have hDFapp : ∀ (α : Fin n → ℕ) (x : EuclideanSpace ℝ (Fin n)) (j : Fin n),
      (DF α x) j = Real.sqrt (α j) * HermiteFun (Function.update α j (α j - 1)) x :=
    fun _ _ _ => rfl
  -- the classical directional derivative is `√2` times the `j`th coordinate of `DF`
  have hfdDF : ∀ (α : Fin n → ℕ) (x : EuclideanSpace ℝ (Fin n)) (j : Fin n),
      fderiv ℝ (HermiteFun α) x (EuclideanSpace.single j 1) = Real.sqrt 2 * (DF α x) j := by
    intro α x j
    rw [(HermiteFunDeriv α j x).2, hDFapp]
    ring
  have hDFcont : ∀ α : Fin n → ℕ, Continuous (DF α) := by
    intro α
    refine (EuclideanSpace.equiv (Fin n) ℝ).symm.continuous.comp (continuous_pi ?_)
    intro j
    exact continuous_const.mul (HermiteFunContDiff _).continuous
  have hDFmem : ∀ α : Fin n → ℕ, MemLp (DF α) 2 (GaussMeasure n) := by
    intro α
    have hg : MemLp (fun x => ∑ j : Fin n,
        |Real.sqrt (α j) * HermiteFun (Function.update α j (α j - 1)) x| ) 2
        (GaussMeasure n) := by
      refine memLp_finsetSum Finset.univ (fun j _ => ?_)
      exact ((HermiteFunMemLp (Function.update α j (α j - 1))).const_mul
        (Real.sqrt (α j))).abs
    refine MemLp.of_le hg (hDFcont α).aestronglyMeasurable ?_
    filter_upwards with x
    have hb : ‖DF α x‖ ≤ ∑ j, |(DF α x) j| := by
      rw [EuclideanSpace.norm_eq]
      have h1 : ∑ j, ‖(DF α x) j‖ ^ 2 ≤ (∑ j, |(DF α x) j|) ^ 2 := by
        simpa [Real.norm_eq_abs] using
          Finset.sum_sq_le_sq_sum_of_nonneg (s := Finset.univ)
            (f := fun j => |(DF α x) j|) (fun j _ => abs_nonneg _)
      calc Real.sqrt (∑ j, ‖(DF α x) j‖ ^ 2)
          ≤ Real.sqrt ((∑ j, |(DF α x) j|) ^ 2) := Real.sqrt_le_sqrt h1
        _ = ∑ j, |(DF α x) j| := Real.sqrt_sq (Finset.sum_nonneg fun j _ => abs_nonneg _)
    refine hb.trans ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (Finset.sum_nonneg fun j _ => abs_nonneg _)]

  -- Step 1, integration-by-parts half: `√2 · DF α` is a weak Euclidean gradient of `h_α`
  have hibp : ∀ α : Fin n → ℕ,
      HasGaussWeakGrad (HermiteFun α) (fun x => Real.sqrt 2 • DF α x) := by
    intro α j φ hφ hφc
    have hcd : ContDiff ℝ (⊤ : ℕ∞) (HermiteFun α) := HermiteFunContDiff α
    have hdiffH : ∀ x, DifferentiableAt ℝ (HermiteFun α) x :=
      fun x => (hcd.differentiable (by norm_num)) x
    have hdiffφ : ∀ x, DifferentiableAt ℝ φ x :=
      fun x => (hφ.differentiable (by norm_num)) x
    have hcH : Continuous (HermiteFun α) := hcd.continuous
    have hcdH : Continuous (fun x => fderiv ℝ (HermiteFun α) x (EuclideanSpace.single j (1:ℝ))) :=
      (hcd.continuous_fderiv (by simp)).clm_apply continuous_const
    have hcdφ : Continuous (fun x => fderiv ℝ φ x (EuclideanSpace.single j (1:ℝ))) :=
      (hφ.continuous_fderiv (by simp)).clm_apply continuous_const
    have hcsφ : HasCompactSupport (fun x => fderiv ℝ φ x (EuclideanSpace.single j (1:ℝ))) :=
      hφc.fderiv_apply ℝ _
    have i1 : Integrable
        (fun x => fderiv ℝ (HermiteFun α) x (EuclideanSpace.single j (1:ℝ)) * φ x) volume :=
      (hcdH.mul hφ.continuous).integrable_of_hasCompactSupport (hφc.mul_left)
    have i2 : Integrable
        (fun x => HermiteFun α x * fderiv ℝ φ x (EuclideanSpace.single j (1:ℝ))) volume :=
      (hcH.mul hcdφ).integrable_of_hasCompactSupport (hcsφ.mul_left)
    have i3 : Integrable (fun x => HermiteFun α x * φ x) volume :=
      (hcH.mul hφ.continuous).integrable_of_hasCompactSupport (hφc.mul_left)
    have hfield : (fun x => ((Real.sqrt 2 • DF α x : EuclideanSpace ℝ (Fin n)) j) * φ x)
        = fun x => fderiv ℝ (HermiteFun α) x (EuclideanSpace.single j 1) * φ x := by
      funext x
      rw [hfdDF]
      rfl
    show ∫ x, HermiteFun α x * fderiv ℝ φ x (EuclideanSpace.single j 1)
        = -∫ x, (Real.sqrt 2 • DF α x : EuclideanSpace ℝ (Fin n)) j * φ x
    rw [hfield]
    exact integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable i1 i2 i3
      (fun x _ => hdiffH x) (fun x _ => hdiffφ x)
  -- **Step 1.** Each Hermite function lies in `W^{1,2}(γₙ)`, and its `D` is `DF`
  have hstep1 : ∀ α : Fin n → ℕ,
      HermiteL2 α ∈ SobolevW12 n ∧ GaussD (HermiteL2 α) = (hDFmem α).toLp := by
    intro α
    have hHae : ((HermiteL2 α : Lp ℝ 2 (GaussMeasure n)) : EuclideanSpace ℝ (Fin n) → ℝ)
        =ᵐ[GaussMeasure n] HermiteFun α := MemLp.coeFn_toLp _
    -- the weak-gradient statement for a general `Lp` witness `W` with `↑W =ᵐ DF α`
    have hfromAe : ∀ W : Lp (EuclideanSpace ℝ (Fin n)) 2 (GaussMeasure n),
        (W : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) =ᵐ[GaussMeasure n] DF α →
        HasGaussWeakGrad ((HermiteL2 α : Lp ℝ 2 (GaussMeasure n)) : EuclideanSpace ℝ (Fin n) → ℝ)
          (fun x => Real.sqrt 2 • (W : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) x) := by
      intro W hW
      refine GaussWeakGradAECongr _ _ _ _ hHae.symm ?_ (hibp α)
      filter_upwards [hW] with x hx
      rw [hx]
    have hGae : (((hDFmem α).toLp : Lp (EuclideanSpace ℝ (Fin n)) 2 (GaussMeasure n)) :
        EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) =ᵐ[GaussMeasure n] DF α :=
      MemLp.coeFn_toLp _
    exact GaussDWitness (HermiteL2 α) ((hDFmem α).toLp) (hfromAe _ hGae)
  -- **Step 2.** The Gram matrix of the Hermite gradients is `diag(|α|)`
  have hstep2 : ∀ α β : Fin n → ℕ,
      (inner ℝ ((hDFmem α).toLp) ((hDFmem β).toLp) : ℝ)
        = if α = β then (MultiIndexSum α : ℝ) else 0 := by
    intro α β
    have hkron : ∀ a b : Fin n → ℕ,
        (inner ℝ (HermiteL2 a) (HermiteL2 b) : ℝ) = if a = b then 1 else 0 :=
      orthonormal_iff_ite.mp (HermiteL2Orthonormal n)
    -- the γₙ-integral of a product of two Hermite functions
    have hint : ∀ a b : Fin n → ℕ,
        ∫ x, HermiteFun a x * HermiteFun b x ∂(GaussMeasure n) = if a = b then 1 else 0 := by
      intro a b
      rw [← hkron a b, L2.inner_def]
      refine integral_congr_ae ?_
      filter_upwards [MemLp.coeFn_toLp (HermiteFunMemLp a),
        MemLp.coeFn_toLp (HermiteFunMemLp b)] with x hx hy
      rw [show ((HermiteL2 a : Lp ℝ 2 (GaussMeasure n)) :
          EuclideanSpace ℝ (Fin n) → ℝ) x = HermiteFun a x from hx,
        show ((HermiteL2 b : Lp ℝ 2 (GaussMeasure n)) :
          EuclideanSpace ℝ (Fin n) → ℝ) x = HermiteFun b x from hy]
      simp only [RCLike.inner_apply, conj_trivial]
      ring
    -- expand the L²(γₙ;ℝⁿ) inner product coordinatewise
    have hI : (inner ℝ ((hDFmem α).toLp) ((hDFmem β).toLp) : ℝ)
        = ∑ j : Fin n, ∫ x, (DF α x) j * (DF β x) j ∂(GaussMeasure n) := by
      rw [L2.inner_def]
      have hae : ∀ᵐ x ∂(GaussMeasure n),
          (inner ℝ
              ((((hDFmem α).toLp : Lp (EuclideanSpace ℝ (Fin n)) 2 (GaussMeasure n)) :
                EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) x)
              ((((hDFmem β).toLp : Lp (EuclideanSpace ℝ (Fin n)) 2 (GaussMeasure n)) :
                EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) x) : ℝ)
            = ∑ j : Fin n, (DF α x) j * (DF β x) j := by
        filter_upwards [MemLp.coeFn_toLp (hDFmem α),
          MemLp.coeFn_toLp (hDFmem β)] with x hx hy
        rw [hx, hy, PiLp.inner_apply]
        exact Finset.sum_congr rfl fun j _ => by
          simp only [RCLike.inner_apply, conj_trivial]
          ring
      rw [integral_congr_ae hae]
      refine integral_finsetSum _ (fun j _ => ?_)
      exact ((HermiteFunMemLp (Function.update α j (α j - 1))).const_mul
          (Real.sqrt (α j))).integrable_mul
        ((HermiteFunMemLp (Function.update β j (β j - 1))).const_mul (Real.sqrt (β j)))
    rw [hI]
    -- evaluate each coordinate integral
    have hterm : ∀ j : Fin n, ∫ x, (DF α x) j * (DF β x) j ∂(GaussMeasure n)
        = if α = β then (α j : ℝ) else 0 := by
      intro j
      have hexp : ∀ x : EuclideanSpace ℝ (Fin n), (DF α x) j * (DF β x) j
          = (Real.sqrt (α j) * Real.sqrt (β j)) *
            (HermiteFun (Function.update α j (α j - 1)) x
              * HermiteFun (Function.update β j (β j - 1)) x) := by
        intro x
        rw [hDFapp, hDFapp]
        ring
      rw [integral_congr_ae (Filter.Eventually.of_forall hexp), integral_const_mul,
        hint]
      by_cases hab : α = β
      · subst hab
        rw [if_pos rfl, if_pos rfl, mul_one, Real.mul_self_sqrt (Nat.cast_nonneg _)]
      · rw [if_neg hab]
        by_cases hj : α j = 0
        · rw [hj]
          simp
        by_cases hj2 : β j = 0
        · rw [hj2]
          simp
        have hne : Function.update α j (α j - 1) ≠ Function.update β j (β j - 1) := by
          intro heq
          refine hab (funext fun i => ?_)
          by_cases hij : i = j
          · subst hij
            have h1 : α i - 1 = β i - 1 := by
              simpa [Function.update_self] using congrFun heq i
            omega
          · have := congrFun heq i
            rwa [Function.update_of_ne hij, Function.update_of_ne hij] at this
        rw [if_neg hne, mul_zero]
    rw [Finset.sum_congr rfl fun j _ => hterm j]
    by_cases hab : α = β
    · simp only [if_pos hab]
      rw [MultiIndexSum]
      push_cast
      ring
    · simp only [if_neg hab, Finset.sum_const_zero]
  -- the two conjuncts, stated on `GaussD (HermiteL2 α)` itself
  have hA : ∀ α : Fin n → ℕ, HermiteL2 α ∈ SobolevW12 n ∧
      ((GaussD (HermiteL2 α) : Lp (EuclideanSpace ℝ (Fin n)) 2 (GaussMeasure n)) :
          EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
        =ᵐ[GaussMeasure n] fun x => WithLp.toLp 2 (fun j =>
          Real.sqrt (α j) * HermiteFun (Function.update α j (α j - 1)) x) := by
    intro α
    refine ⟨(hstep1 α).1, ?_⟩
    rw [(hstep1 α).2]
    exact MemLp.coeFn_toLp (hDFmem α)
  have hB : ∀ α β : Fin n → ℕ,
      (inner ℝ (GaussD (HermiteL2 α)) (GaussD (HermiteL2 β)) : ℝ)
        = if α = β then (MultiIndexSum α : ℝ) else 0 := by
    intro α β
    rw [(hstep1 α).2, (hstep1 β).2]
    exact hstep2 α β
  exact ⟨hA, hB⟩
