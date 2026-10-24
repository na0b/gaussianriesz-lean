import GaussianRiesz.MehlerFixedTimeTesting
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import GaussianRiesz.CompIntegrationByParts
import GaussianRiesz.SemigroupGradientCommute
import GaussianRiesz.SubordinationPseudoInverse
import GaussianRiesz.GaussL2LocallyIntegrable
import GaussianRiesz.HermiteL2ZeroAEOne
open MeasureTheory
theorem RieszPseudoInverseTestedIdentity {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hfc : HasCompactSupport f)
    (hmem : MemLp f 2 (GaussMeasure n))
    (u : Lp ℝ 2 (GaussMeasure n)) (hu : u = hmem.toLp f)
    (A : ℝ → Fin n → EuclideanSpace ℝ (Fin n) → ℝ)
    (hA : A = fun s i x =>
      ∫ z, fderiv ℝ f (Real.exp (-s) • x + Real.sqrt (1 - Real.exp (-2 * s)) • z)
        (EuclideanSpace.single i (1 : ℝ)) ∂(GaussMeasure n))
    (Phi : Fin n → EuclideanSpace ℝ (Fin n) → ℝ)
    (hPhi : Phi = fun i x =>
      (Real.sqrt Real.pi)⁻¹ * ∫ s in Set.Ioi (0 : ℝ),
        (Real.sqrt s)⁻¹ * (Real.exp (-s) * ((Real.sqrt 2)⁻¹ * A s i x)))
    (N : ℝ)
    (hAbd : ∀ (s : ℝ) (i : Fin n) (x : EuclideanSpace ℝ (Fin n)), ‖A s i x‖ ≤ N)
    (hAjoint : ∀ i : Fin n, Continuous (fun p : ℝ × EuclideanSpace ℝ (Fin n) =>
      A p.1 i p.2))
    (hwt : IntegrableOn (fun s : ℝ => (Real.sqrt s)⁻¹ * Real.exp (-s))
      (Set.Ioi (0 : ℝ)))
    (hconv : ∀ p : EuclideanSpace ℝ (Fin n) → Prop,
      (∀ᵐ x ∂(GaussMeasure n), p x) →
      ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))), p x) :
    ∀ (i : Fin n) (ψ : EuclideanSpace ℝ (Fin n) → ℝ),
      ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      ∫ x, (FracPow (-(1 : ℝ) / 2) u : EuclideanSpace ℝ (Fin n) → ℝ) x
            * fderiv ℝ ψ x (EuclideanSpace.single i (1 : ℝ))
        = -∫ x, (Real.sqrt 2 * Phi i x) * ψ x := by
  intro i ψ hψ hψc
  -- Step 6a: the test factor `∂ᵢψ` is continuous, compactly supported and bounded
  have hdψc : Continuous (fun x : EuclideanSpace ℝ (Fin n) =>
      fderiv ℝ ψ x (EuclideanSpace.single i (1 : ℝ))) :=
    (hψ.continuous_fderiv (by simp)).clm_apply continuous_const
  have hdψcs : HasCompactSupport (fun x : EuclideanSpace ℝ (Fin n) =>
      fderiv ℝ ψ x (EuclideanSpace.single i (1 : ℝ))) := by
    have h := HasCompactSupport.comp_left (g := fun L : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ =>
      L (EuclideanSpace.single i (1 : ℝ))) (hψc.fderiv ℝ) (by simp)
    exact h
  obtain ⟨D, hD⟩ : ∃ D : ℝ, ∀ x, ‖fderiv ℝ ψ x (EuclideanSpace.single i (1 : ℝ))‖ ≤ D := by
    obtain ⟨D, hDb⟩ := (hdψcs.isCompact_range hdψc).isBounded.subset_closedBall 0
    exact ⟨D, fun y => by simpa using hDb (Set.mem_range_self y)⟩
  have hD0 : (0 : ℝ) ≤ D := le_trans (norm_nonneg _) (hD 0)
  -- Step 6b: every `L²` class pairs integrably against `∂ᵢψ`
  have hint : ∀ v : Lp ℝ 2 (GaussMeasure n),
      Integrable (fun x => (v : EuclideanSpace ℝ (Fin n) → ℝ) x
        * fderiv ℝ ψ x (EuclideanSpace.single i (1 : ℝ))) volume := by
    intro v
    have hloc : LocallyIntegrable (v : EuclideanSpace ℝ (Fin n) → ℝ) volume :=
      (GaussL2LocallyIntegrable (v : EuclideanSpace ℝ (Fin n) → ℝ) (Lp.memLp v)).1
    simpa [smul_eq_mul] using
      hloc.integrable_smul_right_of_hasCompactSupport hdψc hdψcs
  -- Step 6c: the operator bound, from the local `L²`-to-`L¹` estimate
  obtain ⟨C, hC0, hCb⟩ := (GaussL2LocallyIntegrable (n := n) (fun _ => (0 : ℝ))
    (MemLp.zero)).2.2 (tsupport (fun x : EuclideanSpace ℝ (Fin n) =>
      fderiv ℝ ψ x (EuclideanSpace.single i (1 : ℝ)))) hdψcs
  have hbound : ∀ v : Lp ℝ 2 (GaussMeasure n),
      ‖∫ x, (v : EuclideanSpace ℝ (Fin n) → ℝ) x
        * fderiv ℝ ψ x (EuclideanSpace.single i (1 : ℝ))‖ ≤ D * C * ‖v‖ := by
    intro v
    obtain ⟨hvK, hvb⟩ := hCb (v : EuclideanSpace ℝ (Fin n) → ℝ) (Lp.memLp v)
    have hK : MeasurableSet (tsupport (fun x : EuclideanSpace ℝ (Fin n) =>
        fderiv ℝ ψ x (EuclideanSpace.single i (1 : ℝ)))) := hdψcs.measurableSet
    calc ‖∫ x, (v : EuclideanSpace ℝ (Fin n) → ℝ) x
            * fderiv ℝ ψ x (EuclideanSpace.single i (1 : ℝ))‖
        ≤ ∫ x, ‖(v : EuclideanSpace ℝ (Fin n) → ℝ) x
            * fderiv ℝ ψ x (EuclideanSpace.single i (1 : ℝ))‖ :=
          norm_integral_le_integral_norm _
      _ = ∫ x in tsupport (fun x : EuclideanSpace ℝ (Fin n) =>
            fderiv ℝ ψ x (EuclideanSpace.single i (1 : ℝ))),
          ‖(v : EuclideanSpace ℝ (Fin n) → ℝ) x
            * fderiv ℝ ψ x (EuclideanSpace.single i (1 : ℝ))‖ :=
          (setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => by
            rw [image_eq_zero_of_notMem_tsupport hx, mul_zero, norm_zero]).symm
      _ ≤ ∫ x in tsupport (fun x : EuclideanSpace ℝ (Fin n) =>
            fderiv ℝ ψ x (EuclideanSpace.single i (1 : ℝ))),
          D * ‖(v : EuclideanSpace ℝ (Fin n) → ℝ) x‖ := by
          refine setIntegral_mono_on (hint v).norm.restrict
            ((hvK.norm.const_mul D)) hK fun x _ => ?_
          rw [norm_mul]
          exact mul_le_mul_of_nonneg_left (hD x) (norm_nonneg _) |>.trans_eq (by ring)
      _ = D * ∫ x in tsupport (fun x : EuclideanSpace ℝ (Fin n) =>
            fderiv ℝ ψ x (EuclideanSpace.single i (1 : ℝ))),
          |(v : EuclideanSpace ℝ (Fin n) → ℝ) x| := by
          rw [integral_const_mul]
          simp [Real.norm_eq_abs]
      _ ≤ D * (C * ‖v‖) := by
          refine mul_le_mul_of_nonneg_left ?_ hD0
          rw [Lp.norm_def]
          exact hvb
      _ = D * C * ‖v‖ := by ring
  -- Step 6d: the bundled functional.  Additivity and homogeneity each need the
  -- `γₙ`-a.e. additivity of the `Lp` coercion transported to a `volume`-a.e. statement.
  have hLadd : ∀ v₁ v₂ : Lp ℝ 2 (GaussMeasure n),
      (∫ x, ((v₁ + v₂ : Lp ℝ 2 (GaussMeasure n)) : EuclideanSpace ℝ (Fin n) → ℝ) x
          * fderiv ℝ ψ x (EuclideanSpace.single i (1 : ℝ)))
        = (∫ x, (v₁ : EuclideanSpace ℝ (Fin n) → ℝ) x
            * fderiv ℝ ψ x (EuclideanSpace.single i (1 : ℝ)))
          + ∫ x, (v₂ : EuclideanSpace ℝ (Fin n) → ℝ) x
            * fderiv ℝ ψ x (EuclideanSpace.single i (1 : ℝ)) := by
    intro v₁ v₂
    have hae : (fun x => ((v₁ + v₂ : Lp ℝ 2 (GaussMeasure n)) :
          EuclideanSpace ℝ (Fin n) → ℝ) x
          * fderiv ℝ ψ x (EuclideanSpace.single i (1 : ℝ)))
        =ᵐ[volume] fun x => (v₁ : EuclideanSpace ℝ (Fin n) → ℝ) x
            * fderiv ℝ ψ x (EuclideanSpace.single i (1 : ℝ))
          + (v₂ : EuclideanSpace ℝ (Fin n) → ℝ) x
            * fderiv ℝ ψ x (EuclideanSpace.single i (1 : ℝ)) := by
      refine hconv _ ?_
      filter_upwards [Lp.coeFn_add v₁ v₂] with x hx
      rw [hx, Pi.add_apply]; ring
    rw [integral_congr_ae hae, integral_add (hint v₁) (hint v₂)]
  have hLsmul : ∀ (c : ℝ) (v : Lp ℝ 2 (GaussMeasure n)),
      (∫ x, ((c • v : Lp ℝ 2 (GaussMeasure n)) : EuclideanSpace ℝ (Fin n) → ℝ) x
          * fderiv ℝ ψ x (EuclideanSpace.single i (1 : ℝ)))
        = c * ∫ x, (v : EuclideanSpace ℝ (Fin n) → ℝ) x
            * fderiv ℝ ψ x (EuclideanSpace.single i (1 : ℝ)) := by
    intro c v
    have hae : (fun x => ((c • v : Lp ℝ 2 (GaussMeasure n)) :
          EuclideanSpace ℝ (Fin n) → ℝ) x
          * fderiv ℝ ψ x (EuclideanSpace.single i (1 : ℝ)))
        =ᵐ[volume] fun x => c * ((v : EuclideanSpace ℝ (Fin n) → ℝ) x
            * fderiv ℝ ψ x (EuclideanSpace.single i (1 : ℝ))) := by
      refine hconv _ ?_
      filter_upwards [Lp.coeFn_smul c v] with x hx
      rw [hx, Pi.smul_apply, smul_eq_mul]; ring
    rw [integral_congr_ae hae, integral_const_mul]
  let L : Lp ℝ 2 (GaussMeasure n) →ₗ[ℝ] ℝ :=
    { toFun := fun v => ∫ x, (v : EuclideanSpace ℝ (Fin n) → ℝ) x
        * fderiv ℝ ψ x (EuclideanSpace.single i (1 : ℝ))
      map_add' := hLadd
      map_smul' := fun c v => by simpa using hLsmul c v }
  let Lam : Lp ℝ 2 (GaussMeasure n) →L[ℝ] ℝ := L.mkContinuous (D * C) hbound
  have hLam : ∀ v : Lp ℝ 2 (GaussMeasure n), Lam v
      = ∫ x, (v : EuclideanSpace ℝ (Fin n) → ℝ) x
        * fderiv ℝ ψ x (EuclideanSpace.single i (1 : ℝ)) := fun v => rfl
  -- Step 7: push the functional inside the subordination integral
  have hsub := SubordinationPseudoInverse u
  have hBoch := ContinuousLinearMap.integral_comp_commSL (by simp) Lam hsub.1
  have hΛw : Lam (FracPow (-(1 : ℝ) / 2) u)
      = (Real.sqrt Real.pi)⁻¹ * ∫ s in Set.Ioi (0 : ℝ),
          (Real.sqrt s)⁻¹ * Lam (OUSemigroup s (FracPow (0 : ℝ) u)) := by
    rw [hsub.2, map_smul, smul_eq_mul, ← hBoch]
    congr 1
    refine setIntegral_congr_fun measurableSet_Ioi fun s _ => ?_
    rw [map_smul, smul_eq_mul]
  -- the fixed-time identity, by import
  have hfix : ∀ s : ℝ, 0 < s → Lam (OUSemigroup s (FracPow (0 : ℝ) u))
      = -(Real.exp (-s) * ∫ x, A s i x * ψ x) := by
    intro s hs
    rw [hLam, hu, hA]
    exact (MehlerFixedTimeTesting f hf hfc hmem ψ hψ hψc i s hs).2.2
  -- Step 10: Fubini in `(s, x)`
  have hGmeas : Measurable (Function.uncurry (fun (s : ℝ) (x : EuclideanSpace ℝ (Fin n)) =>
      (Real.sqrt s)⁻¹ * (Real.exp (-s) * ((Real.sqrt 2)⁻¹ * A s i x))
        * (Real.sqrt 2 * ψ x))) := by
    have h1 : Measurable fun p : ℝ × EuclideanSpace ℝ (Fin n) => (Real.sqrt p.1)⁻¹ :=
      (Real.continuous_sqrt.measurable.inv).comp measurable_fst
    have h2 : Measurable fun p : ℝ × EuclideanSpace ℝ (Fin n) => Real.exp (-p.1) :=
      ((Real.continuous_exp.comp continuous_neg).measurable).comp measurable_fst
    have h3 : Measurable fun p : ℝ × EuclideanSpace ℝ (Fin n) => A p.1 i p.2 :=
      (hAjoint i).measurable
    have h4 : Measurable fun p : ℝ × EuclideanSpace ℝ (Fin n) => ψ p.2 :=
      hψ.continuous.measurable.comp measurable_snd
    exact (h1.mul (h2.mul (measurable_const.mul h3))).mul (measurable_const.mul h4)
  have hprodint : Integrable (Function.uncurry
      (fun (s : ℝ) (x : EuclideanSpace ℝ (Fin n)) =>
        (Real.sqrt s)⁻¹ * (Real.exp (-s) * ((Real.sqrt 2)⁻¹ * A s i x))
          * (Real.sqrt 2 * ψ x)))
      ((volume.restrict (Set.Ioi (0 : ℝ))).prod
        (volume : Measure (EuclideanSpace ℝ (Fin n)))) := by
    have hmajx : Integrable (fun x : EuclideanSpace ℝ (Fin n) => N * |ψ x|) volume :=
      ((hψ.continuous.abs).const_mul N).integrable_of_hasCompactSupport
        (hψc.abs.mul_left)
    refine Integrable.mono' (hwt.mul_prod hmajx) hGmeas.aestronglyMeasurable ?_
    filter_upwards with p
    have h2 : |A p.1 i p.2| ≤ N := by rw [← Real.norm_eq_abs]; exact hAbd p.1 i p.2
    have h3 : (0 : ℝ) ≤ (Real.sqrt p.1)⁻¹ := by positivity
    have h4 : (0 : ℝ) < Real.exp (-p.1) := Real.exp_pos _
    have h7 : (0 : ℝ) ≤ |ψ p.2| := abs_nonneg _
    have h8 : Real.sqrt 2 ≠ 0 := by positivity
    rw [Function.uncurry_apply_pair, Real.norm_eq_abs]
    calc |(Real.sqrt p.1)⁻¹ * (Real.exp (-p.1) * ((Real.sqrt 2)⁻¹ * A p.1 i p.2))
            * (Real.sqrt 2 * ψ p.2)|
        = (Real.sqrt p.1)⁻¹ * Real.exp (-p.1) * |A p.1 i p.2| * |ψ p.2| := by
          rw [abs_mul, abs_mul, abs_mul, abs_mul, abs_mul, abs_inv, abs_inv,
            abs_of_nonneg (Real.sqrt_nonneg p.1), abs_of_nonneg (Real.sqrt_nonneg 2),
            abs_of_pos h4]
          field_simp
      _ ≤ (Real.sqrt p.1)⁻¹ * Real.exp (-p.1) * N * |ψ p.2| := by
          have h9 := mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left h2 (mul_nonneg h3 h4.le)) h7
          linarith
      _ = (Real.sqrt p.1)⁻¹ * Real.exp (-p.1) * (N * |ψ p.2|) := by ring
  have hswap := integral_integral_swap hprodint
  -- assemble
  have hstep : ∫ s in Set.Ioi (0 : ℝ),
        (Real.sqrt s)⁻¹ * Lam (OUSemigroup s (FracPow (0 : ℝ) u))
      = -∫ s in Set.Ioi (0 : ℝ), ∫ x, (Real.sqrt s)⁻¹ *
          (Real.exp (-s) * ((Real.sqrt 2)⁻¹ * A s i x)) * (Real.sqrt 2 * ψ x) := by
    rw [← integral_neg]
    refine setIntegral_congr_fun measurableSet_Ioi fun s hs => ?_
    rw [hfix s hs]
    have h8 : Real.sqrt 2 ≠ 0 := by positivity
    have hfun : (fun x => (Real.sqrt s)⁻¹ *
          (Real.exp (-s) * ((Real.sqrt 2)⁻¹ * A s i x)) * (Real.sqrt 2 * ψ x))
        = fun x => ((Real.sqrt s)⁻¹ * Real.exp (-s)) * (A s i x * ψ x) := by
      funext x
      field_simp
    rw [hfun, integral_const_mul]
    ring
  have hfinal : (Real.sqrt Real.pi)⁻¹ * (∫ x, ∫ s in Set.Ioi (0 : ℝ),
        (Real.sqrt s)⁻¹ * (Real.exp (-s) * ((Real.sqrt 2)⁻¹ * A s i x))
          * (Real.sqrt 2 * ψ x))
      = ∫ x, (Real.sqrt 2 * Phi i x) * ψ x := by
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only
    rw [integral_mul_const]
    simp only [hPhi]
    ring
  rw [← hLam (FracPow (-(1 : ℝ) / 2) u), hΛw, hstep, hswap, mul_neg, hfinal]
