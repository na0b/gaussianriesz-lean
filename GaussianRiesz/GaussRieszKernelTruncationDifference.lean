module

public import GaussianRiesz.GaussRieszKernelHormanderDyadicBound
public import GaussianRiesz.GaussRieszKernelFarMajorant

@[expose] public section
open MeasureTheory Metric
open scoped ENNReal
theorem GaussRieszKernelTruncationDifference {n : ℕ} (j : Fin n) (R : ℝ) (hR : 1 ≤ R) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (g : EuclideanSpace ℝ (Fin n) → ℝ) (Φ N : ℝ)
        (x z : EuclideanSpace ℝ (Fin n)) (ε : ℝ),
        ‖x‖ ≤ R → 0 < ε → ε ≤ 1 → ‖x - z‖ < ε / 2 →
        MemLp g 1 (GaussMeasure n) →
        (∀ᵐ y ∂(volume : Measure (EuclideanSpace ℝ (Fin n))), ‖x - y‖ ≤ ε → g y = 0) →
        0 ≤ Φ →
        (∀ ρ : ℝ, 0 < ρ → ρ ≤ 2 →
            ∫⁻ y in closedBall x ρ, ‖g y‖ₑ
              ≤ ENNReal.ofReal Φ * volume (closedBall x ρ)) →
        Integrable (fun y => Real.exp (-‖y‖ ^ 2) * |g y|) volume →
        (∫ y, Real.exp (-‖y‖ ^ 2) * |g y|) ≤ N →
        |(∫ y, GaussRieszKernel j x y * g y) - ∫ y, GaussRieszKernel j z y * g y|
          ≤ C * (Φ + N) := by
  obtain ⟨Cd, hCd0, hCdtop, hCd⟩ := GaussRieszKernelHormanderDyadicBound j R hR
  obtain ⟨Ca, hCa0, hCaa, -⟩ := (GaussRieszKernelFarMajorant j).1 R 1 (by linarith) one_pos
  obtain ⟨Cb, hCb0, hCba, -⟩ :=
    (GaussRieszKernelFarMajorant j).1 (R + 1) (1/2) (by linarith) (by norm_num)
  have hCdr : 0 < Cd.toReal := ENNReal.toReal_pos hCd0 hCdtop
  refine ⟨max Cd.toReal (Ca + Cb), lt_of_lt_of_le hCdr (le_max_left _ _), ?_⟩
  intro g Φ N x z ε hxR hε0 hε1 hxz hgmem hgvan hΦ0 hmax hexpint hexp
  have hN0 : 0 ≤ N := le_trans (integral_nonneg (fun y => by positivity)) hexp
  have hzR : ‖z‖ ≤ R + 1 := by
    have h1 : ‖z‖ - ‖x‖ ≤ ‖z - x‖ := norm_sub_norm_le z x
    rw [show ‖z - x‖ = ‖x - z‖ from norm_sub_rev z x] at h1
    linarith
  -- measurability of the regions
  have hmeasIoi : ∀ a : ℝ, MeasurableSet {y : EuclideanSpace ℝ (Fin n) | a < ‖x - y‖} := by
    intro a
    have hc : Continuous fun y : EuclideanSpace ℝ (Fin n) => ‖x - y‖ :=
      (continuous_const.sub continuous_id).norm
    have he : {y : EuclideanSpace ℝ (Fin n) | a < ‖x - y‖}
        = (fun y : EuclideanSpace ℝ (Fin n) => ‖x - y‖) ⁻¹' Set.Ioi a := rfl
    rw [he]; exact hc.measurable measurableSet_Ioi
  -- integrability of the two kernel products on the support region
  obtain ⟨Cx, -, -, hCxb⟩ := (GaussRieszKernelFarMajorant j).1 R ε (by linarith) hε0
  obtain ⟨Cz, -, -, hCzb⟩ :=
    (GaussRieszKernelFarMajorant j).1 (R + 1) (ε/2) (by linarith) (by positivity)
  have hintx : IntegrableOn (fun y => GaussRieszKernel j x y * g y)
      {y : EuclideanSpace ℝ (Fin n) | ε < ‖x - y‖} volume := (hCxb g hgmem x hxR).1
  have hsubz : {y : EuclideanSpace ℝ (Fin n) | ε < ‖x - y‖}
      ⊆ {y : EuclideanSpace ℝ (Fin n) | ε/2 < ‖z - y‖} := by
    intro y hy
    have h1 : ‖x - y‖ - ‖x - z‖ ≤ ‖z - y‖ := by
      have e1 : x - y = (x - z) + (z - y) := by abel
      have h2 : ‖(x - z) + (z - y)‖ ≤ ‖x - z‖ + ‖z - y‖ := norm_add_le _ _
      rw [← e1] at h2; linarith
    have hy' : ε < ‖x - y‖ := hy
    simp only [Set.mem_ofPred_eq]
    linarith
  have hintz : IntegrableOn (fun y => GaussRieszKernel j z y * g y)
      {y : EuclideanSpace ℝ (Fin n) | ε < ‖x - y‖} volume :=
    ((hCzb g hgmem z hzR).1).mono_set hsubz
  -- the region decomposition
  have hA1sub : {y : EuclideanSpace ℝ (Fin n) | ε < ‖x - y‖ ∧ ‖x - y‖ ≤ 1}
      ⊆ {y : EuclideanSpace ℝ (Fin n) | ε < ‖x - y‖} := fun y hy => hy.1
  have hA2sub : {y : EuclideanSpace ℝ (Fin n) | 1 < ‖x - y‖}
      ⊆ {y : EuclideanSpace ℝ (Fin n) | ε < ‖x - y‖} := fun y hy => lt_of_le_of_lt hε1 hy
  have hunion : {y : EuclideanSpace ℝ (Fin n) | ε < ‖x - y‖}
      = {y : EuclideanSpace ℝ (Fin n) | ε < ‖x - y‖ ∧ ‖x - y‖ ≤ 1}
        ∪ {y : EuclideanSpace ℝ (Fin n) | 1 < ‖x - y‖} := by
    ext y
    simp only [Set.mem_union, Set.mem_ofPred_eq]
    constructor
    · intro h
      rcases le_or_gt ‖x - y‖ 1 with h1 | h1
      · exact Or.inl ⟨h, h1⟩
      · exact Or.inr h1
    · rintro (⟨h, -⟩ | h)
      · exact h
      · exact lt_of_le_of_lt hε1 h
  have hdisj : Disjoint {y : EuclideanSpace ℝ (Fin n) | ε < ‖x - y‖ ∧ ‖x - y‖ ≤ 1}
      {y : EuclideanSpace ℝ (Fin n) | 1 < ‖x - y‖} := by
    rw [Set.disjoint_left]
    intro y hy hy2
    exact absurd hy2 (not_lt.2 hy.2)
  -- the two whole-space integrals collapse to the support region
  have hcollapse : ∀ w : EuclideanSpace ℝ (Fin n),
      IntegrableOn (fun y => GaussRieszKernel j w y * g y)
          {y : EuclideanSpace ℝ (Fin n) | ε < ‖x - y‖} volume →
        ∫ y in {y : EuclideanSpace ℝ (Fin n) | ε < ‖x - y‖}, GaussRieszKernel j w y * g y
          = ∫ y, GaussRieszKernel j w y * g y := by
    intro w hw
    refine setIntegral_eq_integral_of_ae_compl_eq_zero ?_
    filter_upwards [hgvan] with y hy hmem
    have : ‖x - y‖ ≤ ε := by
      simp only [not_lt] at hmem
      exact hmem
    rw [hy this, mul_zero]
  -- the split over the two annuli
  have hsplitx := setIntegral_union hdisj (hmeasIoi 1)
    (hintx.mono_set hA1sub) (hintx.mono_set hA2sub)
  have hsplitz := setIntegral_union hdisj (hmeasIoi 1)
    (hintz.mono_set hA1sub) (hintz.mono_set hA2sub)
  have hA1diff : (∫ y in {y : EuclideanSpace ℝ (Fin n) | ε < ‖x - y‖ ∧ ‖x - y‖ ≤ 1}, GaussRieszKernel j x y * g y)
        - ∫ y in {y : EuclideanSpace ℝ (Fin n) | ε < ‖x - y‖ ∧ ‖x - y‖ ≤ 1}, GaussRieszKernel j z y * g y
      = ∫ y in {y : EuclideanSpace ℝ (Fin n) | ε < ‖x - y‖ ∧ ‖x - y‖ ≤ 1},
        (GaussRieszKernel j x y - GaussRieszKernel j z y) * g y := by
    rw [← integral_sub (hintx.mono_set hA1sub) (hintz.mono_set hA1sub)]
    refine integral_congr_ae ?_
    filter_upwards with y
    ring
  -- the near annulus, via the dyadic bound
  have hA1bd : |∫ y in {y : EuclideanSpace ℝ (Fin n) | ε < ‖x - y‖ ∧ ‖x - y‖ ≤ 1},
        (GaussRieszKernel j x y - GaussRieszKernel j z y) * g y| ≤ Cd.toReal * Φ := by
    have hH1 := hCd g (ENNReal.ofReal Φ) x z ε hxR hε0 hε1 hxz hmax
    have hle := norm_integral_le_lintegral_norm
      (μ := volume.restrict {y : EuclideanSpace ℝ (Fin n) | ε < ‖x - y‖ ∧ ‖x - y‖ ≤ 1})
      (fun y => (GaussRieszKernel j x y - GaussRieszKernel j z y) * g y)
    rw [Real.norm_eq_abs] at hle
    have henorm : ∫⁻ y in {y : EuclideanSpace ℝ (Fin n) | ε < ‖x - y‖ ∧ ‖x - y‖ ≤ 1},
          ENNReal.ofReal ‖(GaussRieszKernel j x y - GaussRieszKernel j z y) * g y‖
        = ∫⁻ y in {y : EuclideanSpace ℝ (Fin n) | ε < ‖x - y‖ ∧ ‖x - y‖ ≤ 1},
          ‖GaussRieszKernel j x y - GaussRieszKernel j z y‖ₑ * ‖g y‖ₑ := by
      refine lintegral_congr fun y => ?_
      rw [Real.norm_eq_abs, ← Real.enorm_eq_ofReal_abs, enorm_mul]
    rw [henorm] at hle
    refine le_trans hle ?_
    refine le_trans (ENNReal.toReal_mono (by finiteness) hH1) ?_
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hΦ0]
  -- the far annulus, via the pointwise far majorant at the two parameter pairs
  have hnn : (0 : EuclideanSpace ℝ (Fin n) → ℝ)
      ≤ᵐ[(volume : Measure (EuclideanSpace ℝ (Fin n)))]
      fun y => Real.exp (-‖y‖ ^ 2) * |g y| := by
    filter_upwards with y
    show (0:ℝ) ≤ _
    positivity
  have hA2x : |∫ y in {y : EuclideanSpace ℝ (Fin n) | 1 < ‖x - y‖}, GaussRieszKernel j x y * g y| ≤ Ca * N := by
    have hptx : ∀ y ∈ {y : EuclideanSpace ℝ (Fin n) | 1 < ‖x - y‖},
        |GaussRieszKernel j x y * g y| ≤ Ca * (Real.exp (-‖y‖ ^ 2) * |g y|) := by
      intro y hy
      have h1 := (hCaa x y hxR (le_of_lt hy)).2
      rw [abs_mul]
      calc |GaussRieszKernel j x y| * |g y| ≤ (Ca * Real.exp (-‖y‖ ^ 2)) * |g y| :=
            mul_le_mul_of_nonneg_right h1 (abs_nonneg _)
        _ = Ca * (Real.exp (-‖y‖ ^ 2) * |g y|) := by ring
    calc |∫ y in {y : EuclideanSpace ℝ (Fin n) | 1 < ‖x - y‖}, GaussRieszKernel j x y * g y|
        ≤ ∫ y in {y : EuclideanSpace ℝ (Fin n) | 1 < ‖x - y‖}, |GaussRieszKernel j x y * g y| :=
          abs_integral_le_integral_abs
      _ ≤ ∫ y in {y : EuclideanSpace ℝ (Fin n) | 1 < ‖x - y‖}, Ca * (Real.exp (-‖y‖ ^ 2) * |g y|) :=
          setIntegral_mono_on (hintx.mono_set hA2sub).abs
            (hexpint.const_mul Ca).integrableOn (hmeasIoi 1) hptx
      _ = Ca * ∫ y in {y : EuclideanSpace ℝ (Fin n) | 1 < ‖x - y‖}, (Real.exp (-‖y‖ ^ 2) * |g y|) := integral_const_mul _ _
      _ ≤ Ca * ∫ y, (Real.exp (-‖y‖ ^ 2) * |g y|) :=
          mul_le_mul_of_nonneg_left (setIntegral_le_integral hexpint hnn) hCa0.le
      _ ≤ Ca * N := mul_le_mul_of_nonneg_left hexp hCa0.le
  have hA2z : |∫ y in {y : EuclideanSpace ℝ (Fin n) | 1 < ‖x - y‖}, GaussRieszKernel j z y * g y| ≤ Cb * N := by
    have hptz : ∀ y ∈ {y : EuclideanSpace ℝ (Fin n) | 1 < ‖x - y‖},
        |GaussRieszKernel j z y * g y| ≤ Cb * (Real.exp (-‖y‖ ^ 2) * |g y|) := by
      intro y hy
      have hd : (1:ℝ) < ‖x - y‖ := hy
      have h2 : ‖x - y‖ - ‖x - z‖ ≤ ‖z - y‖ := by
        have e1 : x - y = (x - z) + (z - y) := by abel
        have h3 : ‖(x - z) + (z - y)‖ ≤ ‖x - z‖ + ‖z - y‖ := norm_add_le _ _
        rw [← e1] at h3; linarith
      have h1 := (hCba z y hzR (by linarith)).2
      rw [abs_mul]
      calc |GaussRieszKernel j z y| * |g y| ≤ (Cb * Real.exp (-‖y‖ ^ 2)) * |g y| :=
            mul_le_mul_of_nonneg_right h1 (abs_nonneg _)
        _ = Cb * (Real.exp (-‖y‖ ^ 2) * |g y|) := by ring
    calc |∫ y in {y : EuclideanSpace ℝ (Fin n) | 1 < ‖x - y‖}, GaussRieszKernel j z y * g y|
        ≤ ∫ y in {y : EuclideanSpace ℝ (Fin n) | 1 < ‖x - y‖}, |GaussRieszKernel j z y * g y| :=
          abs_integral_le_integral_abs
      _ ≤ ∫ y in {y : EuclideanSpace ℝ (Fin n) | 1 < ‖x - y‖}, Cb * (Real.exp (-‖y‖ ^ 2) * |g y|) :=
          setIntegral_mono_on (hintz.mono_set hA2sub).abs
            (hexpint.const_mul Cb).integrableOn (hmeasIoi 1) hptz
      _ = Cb * ∫ y in {y : EuclideanSpace ℝ (Fin n) | 1 < ‖x - y‖}, (Real.exp (-‖y‖ ^ 2) * |g y|) := integral_const_mul _ _
      _ ≤ Cb * ∫ y, (Real.exp (-‖y‖ ^ 2) * |g y|) :=
          mul_le_mul_of_nonneg_left (setIntegral_le_integral hexpint hnn) hCb0.le
      _ ≤ Cb * N := mul_le_mul_of_nonneg_left hexp hCb0.le
  -- assemble
  rw [← hcollapse x hintx, ← hcollapse z hintz, hunion, hsplitx, hsplitz]
  have hre : ((∫ y in {y : EuclideanSpace ℝ (Fin n) | ε < ‖x - y‖ ∧ ‖x - y‖ ≤ 1}, GaussRieszKernel j x y * g y)
          + ∫ y in {y : EuclideanSpace ℝ (Fin n) | 1 < ‖x - y‖}, GaussRieszKernel j x y * g y)
        - ((∫ y in {y : EuclideanSpace ℝ (Fin n) | ε < ‖x - y‖ ∧ ‖x - y‖ ≤ 1}, GaussRieszKernel j z y * g y)
          + ∫ y in {y : EuclideanSpace ℝ (Fin n) | 1 < ‖x - y‖}, GaussRieszKernel j z y * g y)
      = (∫ y in {y : EuclideanSpace ℝ (Fin n) | ε < ‖x - y‖ ∧ ‖x - y‖ ≤ 1},
            (GaussRieszKernel j x y - GaussRieszKernel j z y) * g y)
        + ((∫ y in {y : EuclideanSpace ℝ (Fin n) | 1 < ‖x - y‖}, GaussRieszKernel j x y * g y)
          - ∫ y in {y : EuclideanSpace ℝ (Fin n) | 1 < ‖x - y‖}, GaussRieszKernel j z y * g y) := by
    rw [← hA1diff]; ring
  rw [hre]
  have habs2 : |(∫ y in {y : EuclideanSpace ℝ (Fin n) | 1 < ‖x - y‖}, GaussRieszKernel j x y * g y)
        - ∫ y in {y : EuclideanSpace ℝ (Fin n) | 1 < ‖x - y‖}, GaussRieszKernel j z y * g y| ≤ Ca * N + Cb * N := by
    refine le_trans (abs_sub _ _) (add_le_add hA2x hA2z)
  have h1 : Cd.toReal ≤ max Cd.toReal (Ca + Cb) := le_max_left _ _
  have h2 : Ca + Cb ≤ max Cd.toReal (Ca + Cb) := le_max_right _ _
  refine le_trans (abs_add_le _ _) ?_
  refine le_trans (add_le_add hA1bd habs2) ?_
  nlinarith [mul_le_mul_of_nonneg_right h1 hΦ0, mul_le_mul_of_nonneg_right h2 hN0]
