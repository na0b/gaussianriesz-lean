import GaussianRiesz.HasGaussWeakGrad
import GaussianRiesz.GaussIsProb
import GaussianRiesz.L2IntoL1
import GaussianRiesz.GaussL2LocallyIntegrable
import GaussianRiesz.GaussCoordMemLp
open MeasureTheory
theorem GaussWeakGradClosed {n : ℕ} (v : Lp ℝ 2 (GaussMeasure n))
    (G : Lp (EuclideanSpace ℝ (Fin n)) 2 (GaussMeasure n))
    (vk : ℕ → Lp ℝ 2 (GaussMeasure n))
    (Gk : ℕ → Lp (EuclideanSpace ℝ (Fin n)) 2 (GaussMeasure n))
    (hgrad : ∀ k, HasGaussWeakGrad ((vk k : EuclideanSpace ℝ (Fin n) → ℝ))
      ((Gk k : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))))
    (hv : Filter.Tendsto vk Filter.atTop (nhds v))
    (hG : Filter.Tendsto Gk Filter.atTop (nhds G)) :
    HasGaussWeakGrad (v : EuclideanSpace ℝ (Fin n) → ℝ)
      (G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) := by
  classical
  -- a coordinate of a Euclidean vector is bounded by its norm
  have hcle : ∀ (y : EuclideanSpace ℝ (Fin n)) (i : Fin n), ‖y i‖ ≤ ‖y‖ :=
    fun y i => PiLp.norm_apply_le y i
  -- the master estimate: testing an `L²(γₙ)` function against a continuous compactly
  -- supported weight is controlled by its `L²(γₙ)` norm, with a constant free of the function
  have key : ∀ χ : EuclideanSpace ℝ (Fin n) → ℝ, Continuous χ → HasCompactSupport χ →
      ∃ A : ℝ, 0 ≤ A ∧ ∀ w : EuclideanSpace ℝ (Fin n) → ℝ, MemLp w 2 (GaussMeasure n) →
        |∫ x, w x * χ x| ≤ A * (eLpNorm w 2 (GaussMeasure n)).toReal := by
    intro χ hχ hχc
    obtain ⟨M, hM⟩ := hχ.bounded_above_of_compact_support hχc
    have hM0 : (0 : ℝ) ≤ M := le_trans (norm_nonneg (χ 0)) (hM 0)
    obtain ⟨C, hC0, hCbd⟩ :=
      (GaussL2LocallyIntegrable (v : EuclideanSpace ℝ (Fin n) → ℝ) (Lp.memLp v)).2.2
        (tsupport χ) hχc
    refine ⟨M * C, by positivity, ?_⟩
    intro w hw
    have hLI : LocallyIntegrable w volume := (GaussL2LocallyIntegrable w hw).1
    have hK : IsCompact (tsupport χ) := hχc
    have hint : Integrable (fun x => w x * χ x) volume := by
      simpa [smul_eq_mul] using
        hLI.integrable_smul_right_of_hasCompactSupport (𝕜 := ℝ) hχ hχc
    have h1 : |∫ x, w x * χ x| ≤ ∫ x, |w x * χ x| := by
      simpa [Real.norm_eq_abs] using
        norm_integral_le_integral_norm (μ := (volume : Measure (EuclideanSpace ℝ (Fin n))))
          (f := fun x => w x * χ x)
    have h2 : ∫ x, |w x * χ x| = ∫ x in tsupport χ, |w x * χ x| := by
      refine (setIntegral_eq_integral_of_forall_compl_eq_zero ?_).symm
      intro x hx
      simp [image_eq_zero_of_notMem_tsupport hx]
    have hwK : IntegrableOn w (tsupport χ) volume := hLI.integrableOn_isCompact hK
    have h3 : ∫ x in tsupport χ, |w x * χ x| ≤ ∫ x in tsupport χ, M * |w x| := by
      refine setIntegral_mono_on hint.abs.integrableOn (hwK.abs.const_mul M)
        hK.measurableSet ?_
      intro x _
      rw [abs_mul]
      calc |w x| * |χ x| ≤ |w x| * M :=
            mul_le_mul_of_nonneg_left (by simpa [Real.norm_eq_abs] using hM x) (abs_nonneg _)
        _ = M * |w x| := mul_comm _ _
    have h4 : ∫ x in tsupport χ, M * |w x| = M * ∫ x in tsupport χ, |w x| :=
      integral_const_mul _ _
    have h5 : ∫ x in tsupport χ, |w x| ≤ C * (eLpNorm w 2 (GaussMeasure n)).toReal := by
      simpa using (hCbd w hw).2
    calc |∫ x, w x * χ x| ≤ ∫ x, |w x * χ x| := h1
      _ = ∫ x in tsupport χ, |w x * χ x| := h2
      _ ≤ ∫ x in tsupport χ, M * |w x| := h3
      _ = M * ∫ x in tsupport χ, |w x| := h4
      _ ≤ M * (C * (eLpNorm w 2 (GaussMeasure n)).toReal) :=
          mul_le_mul_of_nonneg_left h5 hM0
      _ = M * C * (eLpNorm w 2 (GaussMeasure n)).toReal := by ring
  -- the convergence lemma obtained from the master estimate
  have conv : ∀ χ : EuclideanSpace ℝ (Fin n) → ℝ, Continuous χ → HasCompactSupport χ →
      ∀ (w : ℕ → EuclideanSpace ℝ (Fin n) → ℝ) (w₀ : EuclideanSpace ℝ (Fin n) → ℝ)
        (b : ℕ → ℝ),
        (∀ k, MemLp (w k) 2 (GaussMeasure n)) → MemLp w₀ 2 (GaussMeasure n) →
        (∀ k, (eLpNorm (fun x => w k x - w₀ x) 2 (GaussMeasure n)).toReal ≤ b k) →
        Filter.Tendsto b Filter.atTop (nhds 0) →
        Filter.Tendsto (fun k => ∫ x, w k x * χ x) Filter.atTop
          (nhds (∫ x, w₀ x * χ x)) := by
    intro χ hχ hχc w w₀ b hw hw₀ hb hb0
    obtain ⟨A, hA0, hAb⟩ := key χ hχ hχc
    have hintOf : ∀ u : EuclideanSpace ℝ (Fin n) → ℝ, MemLp u 2 (GaussMeasure n) →
        Integrable (fun x => u x * χ x) volume := by
      intro u hu
      simpa [smul_eq_mul] using
        (GaussL2LocallyIntegrable u hu).1.integrable_smul_right_of_hasCompactSupport
          (𝕜 := ℝ) hχ hχc
    have hdiff : ∀ k, ‖(∫ x, w k x * χ x) - ∫ x, w₀ x * χ x‖ ≤ A * b k := by
      intro k
      have hsub : (∫ x, w k x * χ x) - ∫ x, w₀ x * χ x
          = ∫ x, (w k x - w₀ x) * χ x := by
        rw [← integral_sub (hintOf _ (hw k)) (hintOf _ hw₀)]
        exact integral_congr_ae (Filter.Eventually.of_forall fun x => by ring)
      rw [hsub, Real.norm_eq_abs]
      calc |∫ x, (w k x - w₀ x) * χ x|
          ≤ A * (eLpNorm (fun x => w k x - w₀ x) 2 (GaussMeasure n)).toReal :=
            hAb _ ((hw k).sub hw₀)
        _ ≤ A * b k := mul_le_mul_of_nonneg_left (hb k) hA0
    have hz : Filter.Tendsto (fun k => (∫ x, w k x * χ x) - ∫ x, w₀ x * χ x)
        Filter.atTop (nhds 0) := by
      refine squeeze_zero_norm hdiff ?_
      simpa using hb0.const_mul A
    exact tendsto_sub_nhds_zero_iff.mp hz
  -- now the test identity
  intro j φ hφ hφc
  set e : EuclideanSpace ℝ (Fin n) := EuclideanSpace.single j (1 : ℝ) with he
  set ψ : EuclideanSpace ℝ (Fin n) → ℝ := fun x => fderiv ℝ φ x e with hψ
  have hψc : Continuous ψ :=
    (hφ.continuous_fderiv (by simp)).clm_apply continuous_const
  have hψcs : HasCompactSupport ψ := hφc.fderiv_apply ℝ e
  -- bounds along the two convergent sequences
  have hbv : Filter.Tendsto (fun k => ‖vk k - v‖) Filter.atTop (nhds 0) :=
    tendsto_iff_norm_sub_tendsto_zero.mp hv
  have hbG : Filter.Tendsto (fun k => ‖Gk k - G‖) Filter.atTop (nhds 0) :=
    tendsto_iff_norm_sub_tendsto_zero.mp hG
  have hvbd : ∀ k, (eLpNorm (fun x => (vk k : EuclideanSpace ℝ (Fin n) → ℝ) x
      - (v : EuclideanSpace ℝ (Fin n) → ℝ) x) 2 (GaussMeasure n)).toReal
      ≤ ‖vk k - v‖ := by
    intro k
    rw [Lp.norm_def]
    refine le_of_eq (congrArg ENNReal.toReal (eLpNorm_congr_ae ?_))
    exact (Lp.coeFn_sub (vk k) v).symm
  have hGbd : ∀ k, (eLpNorm (fun x => (Gk k : EuclideanSpace ℝ (Fin n) →
        EuclideanSpace ℝ (Fin n)) x j
      - (G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) x j) 2
        (GaussMeasure n)).toReal ≤ ‖Gk k - G‖ := by
    intro k
    rw [Lp.norm_def]
    refine ENNReal.toReal_mono (Lp.eLpNorm_ne_top _) (eLpNorm_mono_ae ?_)
    filter_upwards [Lp.coeFn_sub (Gk k) G] with x hx
    have hx' : ((Gk k - G : Lp (EuclideanSpace ℝ (Fin n)) 2 (GaussMeasure n)) :
        EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) x
        = (Gk k : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) x
          - (G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) x := by
      simpa using hx
    rw [hx']
    simpa using hcle ((Gk k : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) x
      - (G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) x) j
  -- the left-hand sides converge
  have hL : Filter.Tendsto (fun k => ∫ x, (vk k : EuclideanSpace ℝ (Fin n) → ℝ) x * ψ x)
      Filter.atTop (nhds (∫ x, (v : EuclideanSpace ℝ (Fin n) → ℝ) x * ψ x)) :=
    conv ψ hψc hψcs _ _ _ (fun k => Lp.memLp (vk k)) (Lp.memLp v) hvbd hbv
  -- the right-hand sides converge
  have hR : Filter.Tendsto
      (fun k => ∫ x, (Gk k : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) x j * φ x)
      Filter.atTop
      (nhds (∫ x, (G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) x j * φ x)) :=
    conv φ hφ.continuous hφc _ _ _ (fun k => GaussCoordMemLp (Gk k) j) (GaussCoordMemLp G j) hGbd hbG
  have hL' : Filter.Tendsto (fun k => ∫ x, (vk k : EuclideanSpace ℝ (Fin n) → ℝ) x * ψ x)
      Filter.atTop
      (nhds (-∫ x, (G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) x j * φ x)) := by
    have : (fun k => ∫ x, (vk k : EuclideanSpace ℝ (Fin n) → ℝ) x * ψ x)
        = fun k => -∫ x, (Gk k : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) x j
            * φ x := by
      funext k
      exact hgrad k j φ hφ hφc
    rw [this]
    exact hR.neg
  exact tendsto_nhds_unique hL hL'
