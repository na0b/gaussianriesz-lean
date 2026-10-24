import GaussianRiesz.GaussD
import GaussianRiesz.HermiteL2
import GaussianRiesz.Hermite1Zero
import GaussianRiesz.GaussL2LocallyIntegrable
import GaussianRiesz.GaussCoordMemLp
import GaussianRiesz.GaussWeakGradAECongr
import GaussianRiesz.GaussDWitness
open MeasureTheory
theorem GaussDLinear {n : ℕ} :
    (∀ u v : Lp ℝ 2 (GaussMeasure n), u ∈ SobolevW12 n → v ∈ SobolevW12 n →
        u + v ∈ SobolevW12 n ∧ GaussD (u + v) = GaussD u + GaussD v)
      ∧ (∀ (c : ℝ) (u : Lp ℝ 2 (GaussMeasure n)), u ∈ SobolevW12 n →
          c • u ∈ SobolevW12 n ∧ GaussD (c • u) = c • GaussD u)
      ∧ (∀ c : ℝ, c • HermiteL2 (0 : Fin n → ℕ) ∈ SobolevW12 n
          ∧ GaussD (c • HermiteL2 (0 : Fin n → ℕ)) = 0) := by
  -- (1) testing an L²(γₙ) function against a continuous compactly supported weight
  have hintOf : ∀ (w : EuclideanSpace ℝ (Fin n) → ℝ), MemLp w 2 (GaussMeasure n) →
      ∀ χ : EuclideanSpace ℝ (Fin n) → ℝ, Continuous χ → HasCompactSupport χ →
        Integrable (fun x => w x * χ x) volume := by
    intro w hw χ hχ hχc
    simpa [smul_eq_mul] using
      (GaussL2LocallyIntegrable w hw).1.integrable_smul_right_of_hasCompactSupport
        (𝕜 := ℝ) hχ hχc
  -- (3) the test identity is linear in the pair (function, field)
  have hlin : ∀ (w₁ w₂ : EuclideanSpace ℝ (Fin n) → ℝ)
      (F₁ F₂ : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) (a b : ℝ),
      MemLp w₁ 2 (GaussMeasure n) → MemLp w₂ 2 (GaussMeasure n) →
      (∀ i, MemLp (fun x => F₁ x i) 2 (GaussMeasure n)) →
      (∀ i, MemLp (fun x => F₂ x i) 2 (GaussMeasure n)) →
      HasGaussWeakGrad w₁ F₁ → HasGaussWeakGrad w₂ F₂ →
      HasGaussWeakGrad (fun x => a * w₁ x + b * w₂ x) (fun x => a • F₁ x + b • F₂ x) := by
    intro w₁ w₂ F₁ F₂ a b h1 h2 hF1 hF2 hg1 hg2 j φ hφ hφc
    have hψc : Continuous (fun x => fderiv ℝ φ x (EuclideanSpace.single j (1 : ℝ))) :=
      (hφ.continuous_fderiv (by simp)).clm_apply continuous_const
    have hψcs : HasCompactSupport
        (fun x => fderiv ℝ φ x (EuclideanSpace.single j (1 : ℝ))) :=
      hφc.fderiv_apply ℝ _
    have i1 := hintOf _ h1 _ hψc hψcs
    have i2 := hintOf _ h2 _ hψc hψcs
    have j1 := hintOf _ (hF1 j) _ hφ.continuous hφc
    have j2 := hintOf _ (hF2 j) _ hφ.continuous hφc
    have e1 : ∫ x, (a * w₁ x + b * w₂ x) * fderiv ℝ φ x (EuclideanSpace.single j 1)
        = a * (∫ x, w₁ x * fderiv ℝ φ x (EuclideanSpace.single j 1))
          + b * ∫ x, w₂ x * fderiv ℝ φ x (EuclideanSpace.single j 1) := by
      rw [show (fun x => (a * w₁ x + b * w₂ x) * fderiv ℝ φ x (EuclideanSpace.single j 1))
            = (fun x => a * (w₁ x * fderiv ℝ φ x (EuclideanSpace.single j 1))
                + b * (w₂ x * fderiv ℝ φ x (EuclideanSpace.single j 1))) from
          funext fun x => by ring,
        integral_add (i1.const_mul a) (i2.const_mul b), integral_const_mul, integral_const_mul]
    have e2 : ∫ x, (a • F₁ x + b • F₂ x) j * φ x
        = a * (∫ x, F₁ x j * φ x) + b * ∫ x, F₂ x j * φ x := by
      rw [show (fun x => (a • F₁ x + b • F₂ x) j * φ x)
            = (fun x => a * (F₁ x j * φ x) + b * (F₂ x j * φ x)) from
          funext fun x => by simp; ring,
        integral_add (j1.const_mul a) (j2.const_mul b), integral_const_mul, integral_const_mul]
    show ∫ x, (a * w₁ x + b * w₂ x) * fderiv ℝ φ x (EuclideanSpace.single j 1)
        = -∫ x, (a • F₁ x + b • F₂ x) j * φ x
    rw [e1, e2, hg1 j φ hφ hφc, hg2 j φ hφ hφc]
    ring
  -- (4) coordinates of an L²(γₙ;ℝⁿ) element are in L²(γₙ)
  have hcoord : ∀ (W : Lp (EuclideanSpace ℝ (Fin n)) 2 (GaussMeasure n)) (c : ℝ) (i : Fin n),
      MemLp (fun x => (c • (W : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) x) i) 2
        (GaussMeasure n) := by
    intro W c i
    refine ((GaussCoordMemLp W i).const_smul c).ae_eq ?_
    filter_upwards with x
    simp
  -- (6) the mean-zero property of a derivative of a compactly supported smooth function
  have hFTC : ∀ (φ : EuclideanSpace ℝ (Fin n) → ℝ), ContDiff ℝ (⊤ : ℕ∞) φ →
      HasCompactSupport φ → ∀ j : Fin n,
      ∫ x, fderiv ℝ φ x (EuclideanSpace.single j (1 : ℝ)) = 0 := by
    intro φ hφ hφc j
    set e : EuclideanSpace ℝ (Fin n) := EuclideanSpace.single j (1 : ℝ) with he
    have hne : ‖e‖ = 1 := by simp [he]
    set ψ : EuclideanSpace ℝ (Fin n) → ℝ := fun x => fderiv ℝ φ x e with hψdef
    have hψc : Continuous ψ := (hφ.continuous_fderiv (by simp)).clm_apply continuous_const
    have hψcs : HasCompactSupport ψ := hφc.fderiv_apply ℝ e
    have hφint : Integrable φ (volume : Measure (EuclideanSpace ℝ (Fin n))) :=
      hφ.continuous.integrable_of_hasCompactSupport hφc
    have hcf : Continuous (fderiv ℝ φ) := hφ.continuous_fderiv (by simp)
    obtain ⟨M, hM⟩ := hcf.bounded_above_of_compact_support (hφc.fderiv ℝ)
    have hM0 : (0 : ℝ) ≤ M := le_trans (norm_nonneg _) (hM 0)
    have hlip : LipschitzWith (Real.toNNReal M) φ := by
      refine lipschitzWith_of_nnnorm_fderiv_le (hφ.differentiable (by simp)) ?_
      intro x
      rw [← NNReal.coe_le_coe, coe_nnnorm, Real.coe_toNNReal M hM0]
      exact hM x
    set K : Set (EuclideanSpace ℝ (Fin n)) := Metric.cthickening 1 (tsupport φ) with hKdef
    have hKc : IsCompact K := hφc.cthickening
    -- the increments
    set h : ℕ → ℝ := fun m => 1 / ((m : ℝ) + 1) with hhdef
    have hhpos : ∀ m, 0 < h m := fun m => by
      rw [hhdef]; positivity
    have hhle : ∀ m, h m ≤ 1 := fun m => by
      rw [hhdef]
      rw [div_le_one (by positivity)]
      simp only [le_add_iff_nonneg_left]
      positivity
    set D : ℕ → EuclideanSpace ℝ (Fin n) → ℝ :=
      fun m x => (φ (x + h m • e) - φ x) / h m with hDdef
    have htrint : ∀ a : EuclideanSpace ℝ (Fin n),
        Integrable (fun x => φ (x + a)) (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
      intro a
      refine Continuous.integrable_of_hasCompactSupport
        (hφ.continuous.comp (continuous_id.add continuous_const)) ?_
      exact hφc.comp_homeomorph (Homeomorph.addRight a)
    have hDint : ∀ m, ∫ x, D m x = 0 := by
      intro m
      have hstep : ∫ x, D m x
          = ((∫ x, φ (x + h m • e)) - ∫ x, φ x) / h m := by
        rw [hDdef]
        rw [integral_div]
        congr 1
        exact integral_sub (htrint _) hφint
      rw [hstep, integral_add_right_eq_self φ (h m • e), sub_self, zero_div]
    have hDc : ∀ m, Continuous (D m) := by
      intro m
      exact (((hφ.continuous.comp (continuous_id.add continuous_const)).sub
        hφ.continuous).div_const _)
    have hDlim : ∀ x, Filter.Tendsto (fun m => D m x) Filter.atTop (nhds (ψ x)) := by
      intro x
      have hd : HasDerivAt (fun s : ℝ => φ (x + s • e)) (ψ x) 0 := by
        have h1 : HasDerivAt (fun s : ℝ => x + s • e) e 0 := by
          simpa using ((hasDerivAt_id (0 : ℝ)).smul_const e).const_add x
        have h2 : HasFDerivAt φ (fderiv ℝ φ (x + (0 : ℝ) • e)) (x + (0 : ℝ) • e) :=
          (hφ.differentiable (by simp) _).hasFDerivAt
        have h3 := h2.comp_hasDerivAt (0 : ℝ) h1
        simp only [zero_smul, add_zero] at h3
        exact h3
      rw [hasDerivAt_iff_tendsto_slope] at hd
      have hhto : Filter.Tendsto h Filter.atTop (nhdsWithin 0 ({(0 : ℝ)}ᶜ)) := by
        refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
        · simpa [hhdef] using tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
        · exact Filter.Eventually.of_forall fun m => ne_of_gt (hhpos m)
      refine (hd.comp hhto).congr ?_
      intro m
      simp [slope_def_field, hDdef]
    have hDbd : ∀ m, ∀ x, ‖D m x‖ ≤ M * Set.indicator K (fun _ => (1 : ℝ)) x := by
      intro m x
      by_cases hx : x ∈ K
      · rw [Set.indicator_of_mem hx, mul_one, hDdef]
        simp only [norm_div, Real.norm_eq_abs, abs_of_pos (hhpos m)]
        rw [div_le_iff₀ (hhpos m)]
        have hd := hlip.dist_le_mul (x + h m • e) x
        rw [Real.dist_eq] at hd
        have hdx : dist (x + h m • e) x = h m := by
          rw [dist_eq_norm]
          simp [norm_smul, hne, abs_of_pos (hhpos m)]
        rw [hdx, Real.coe_toNNReal M hM0] at hd
        exact hd
      · have hx1 : x ∉ tsupport φ := fun hc => hx (Metric.self_subset_cthickening _ hc)
        have hx2 : x + h m • e ∉ tsupport φ := by
          intro hc
          refine hx ?_
          refine Metric.mem_cthickening_of_dist_le x (x + h m • e) 1 _ hc ?_
          rw [dist_eq_norm]
          simp only [sub_add_eq_sub_sub, sub_self, zero_sub, norm_neg, norm_smul, hne,
            Real.norm_eq_abs, mul_one, abs_of_pos (hhpos m)]
          exact hhle m
        rw [hDdef]
        simp only [image_eq_zero_of_notMem_tsupport hx1,
          image_eq_zero_of_notMem_tsupport hx2, sub_zero, zero_div, norm_zero]
        rw [Set.indicator_of_notMem hx, mul_zero]
    have hbdint : Integrable (fun x => M * Set.indicator K (fun _ => (1 : ℝ)) x)
        (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
      refine Integrable.const_mul ?_ M
      rw [integrable_indicator_iff hKc.measurableSet]
      exact integrableOn_const (ne_of_lt hKc.measure_lt_top)
    have hdct : Filter.Tendsto (fun m => ∫ x, D m x) Filter.atTop (nhds (∫ x, ψ x)) :=
      tendsto_integral_of_dominated_convergence _
        (fun m => (hDc m).aestronglyMeasurable) hbdint
        (fun m => Filter.Eventually.of_forall (hDbd m))
        (Filter.Eventually.of_forall hDlim)
    have hc0 : Filter.Tendsto (fun m => ∫ x, D m x) Filter.atTop (nhds 0) := by
      simp only [hDint]
      exact tendsto_const_nhds
    exact tendsto_nhds_unique hdct hc0
  -- now the three clauses
  refine ⟨?_, ?_, ?_⟩
  · intro u v hu hv
    obtain ⟨Gu, hGu⟩ := hu
    obtain ⟨Gv, hGv⟩ := hv
    have hu' : GaussD u = Gu := (GaussDWitness u Gu hGu).2
    have hv' : GaussD v = Gv := (GaussDWitness v Gv hGv).2
    have hsum : HasGaussWeakGrad ((u + v : Lp ℝ 2 (GaussMeasure n)) :
        EuclideanSpace ℝ (Fin n) → ℝ)
        (fun x => Real.sqrt 2 •
          ((Gu + Gv : Lp (EuclideanSpace ℝ (Fin n)) 2 (GaussMeasure n)) :
            EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) x) := by
      have hbase := hlin
        ((u : EuclideanSpace ℝ (Fin n) → ℝ)) ((v : EuclideanSpace ℝ (Fin n) → ℝ))
        (fun x => Real.sqrt 2 •
          (Gu : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) x)
        (fun x => Real.sqrt 2 •
          (Gv : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) x)
        1 1 (Lp.memLp u) (Lp.memLp v) (hcoord Gu (Real.sqrt 2)) (hcoord Gv (Real.sqrt 2))
        hGu hGv
      refine GaussWeakGradAECongr _ _ _ _ ?_ ?_ hbase
      · filter_upwards [Lp.coeFn_add u v] with x hx
        rw [hx, Pi.add_apply]
        ring
      · filter_upwards [Lp.coeFn_add Gu Gv] with x hx
        rw [hx, Pi.add_apply, smul_add]
        simp
    obtain ⟨hmem, heq⟩ := GaussDWitness (u + v) (Gu + Gv) hsum
    exact ⟨hmem, by rw [heq, hu', hv']⟩
  · intro c u hu
    obtain ⟨Gu, hGu⟩ := hu
    have hu' : GaussD u = Gu := (GaussDWitness u Gu hGu).2
    have hsum : HasGaussWeakGrad ((c • u : Lp ℝ 2 (GaussMeasure n)) :
        EuclideanSpace ℝ (Fin n) → ℝ)
        (fun x => Real.sqrt 2 •
          ((c • Gu : Lp (EuclideanSpace ℝ (Fin n)) 2 (GaussMeasure n)) :
            EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) x) := by
      have hbase := hlin
        ((u : EuclideanSpace ℝ (Fin n) → ℝ)) ((u : EuclideanSpace ℝ (Fin n) → ℝ))
        (fun x => Real.sqrt 2 •
          (Gu : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) x)
        (fun x => Real.sqrt 2 •
          (Gu : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) x)
        c 0 (Lp.memLp u) (Lp.memLp u) (hcoord Gu (Real.sqrt 2)) (hcoord Gu (Real.sqrt 2))
        hGu hGu
      refine GaussWeakGradAECongr _ _ _ _ ?_ ?_ hbase
      · filter_upwards [Lp.coeFn_smul c u] with x hx
        rw [hx, Pi.smul_apply, smul_eq_mul]
        ring
      · filter_upwards [Lp.coeFn_smul c Gu] with x hx
        rw [hx, Pi.smul_apply]
        simp [smul_smul, mul_comm]
    obtain ⟨hmem, heq⟩ := GaussDWitness (c • u) (c • Gu) hsum
    exact ⟨hmem, by rw [heq, hu']⟩
  · intro c
    have hconst : ((c • HermiteL2 (0 : Fin n → ℕ) : Lp ℝ 2 (GaussMeasure n)) :
        EuclideanSpace ℝ (Fin n) → ℝ) =ᵐ[GaussMeasure n] fun _ => c := by
      filter_upwards [Lp.coeFn_smul c (HermiteL2 (0 : Fin n → ℕ)),
        MemLp.coeFn_toLp (HermiteFunMemLp (0 : Fin n → ℕ))] with x hx hy
      rw [hx]
      simp only [Pi.smul_apply, smul_eq_mul]
      rw [show ((HermiteL2 (0 : Fin n → ℕ) : Lp ℝ 2 (GaussMeasure n)) :
          EuclideanSpace ℝ (Fin n) → ℝ) x = HermiteFun (0 : Fin n → ℕ) x from hy]
      simp [HermiteFun, Hermite1Zero]
    have hzero : HasGaussWeakGrad (fun _ : EuclideanSpace ℝ (Fin n) => c)
        (fun _ : EuclideanSpace ℝ (Fin n) => (0 : EuclideanSpace ℝ (Fin n))) := by
      intro j φ hφ hφc
      have h1 : ∫ x, c * fderiv ℝ φ x (EuclideanSpace.single j (1 : ℝ))
          = c * ∫ x, fderiv ℝ φ x (EuclideanSpace.single j (1 : ℝ)) :=
        integral_const_mul _ _
      rw [h1, hFTC φ hφ hφc j]
      simp
    have hfin : HasGaussWeakGrad ((c • HermiteL2 (0 : Fin n → ℕ) :
        Lp ℝ 2 (GaussMeasure n)) : EuclideanSpace ℝ (Fin n) → ℝ)
        (fun x => Real.sqrt 2 •
          ((0 : Lp (EuclideanSpace ℝ (Fin n)) 2 (GaussMeasure n)) :
            EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) x) := by
      refine GaussWeakGradAECongr _ _ _ _ hconst.symm ?_ hzero
      filter_upwards [Lp.coeFn_zero (E := EuclideanSpace ℝ (Fin n)) (p := 2)
        (μ := GaussMeasure n)] with x hx
      rw [hx]
      simp
    obtain ⟨hmem, heq⟩ := GaussDWitness (c • HermiteL2 (0 : Fin n → ℕ)) 0 hfin
    exact ⟨hmem, heq⟩
