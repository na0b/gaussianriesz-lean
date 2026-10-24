import GaussianRiesz.GaussRieszOffDiagonalL1
import GaussianRiesz.GaussRieszKernelNearBounds
import GaussianRiesz.LocalMaximalFunction
import GaussianRiesz.GaussRieszKernelTruncationDifference
import GaussianRiesz.CoordinateEndpointLevelSetSmall
import GaussianRiesz.LocalMaximalLevelSetSmall
import GaussianRiesz.GaussLebesgueL1DensityTransfer
open MeasureTheory Metric
open scoped ENNReal
theorem GaussRieszCotlarLocal {n : ℕ}
    (T : Lp ℝ 1 (GaussMeasure n) →ₗ[ℝ]
      (EuclideanSpace ℝ (Fin n) →ₘ[GaussMeasure n] EuclideanSpace ℝ (Fin n)))
    (hext : ∀ v : Lp ℝ 2 (GaussMeasure n),
      T (ToL1 v) = (RieszTransform v : EuclideanSpace ℝ (Fin n)
        →ₘ[GaussMeasure n] EuclideanSpace ℝ (Fin n)))
    (hT : ∀ (f : Lp ℝ 1 (GaussMeasure n)) (t : ℝ), 0 < t →
      ENNReal.ofReal t * GaussMeasure n {x | t < ‖T f x‖} ≤ ENNReal.ofReal (2 * ‖f‖))
    (j : Fin n) (R : ℝ) (hR : 1 ≤ R) :
    ∃ C : ℝ≥0∞, C ≠ 0 ∧ C ≠ ⊤ ∧
      ∀ (f : Lp ℝ 1 (GaussMeasure n)) (x : EuclideanSpace ℝ (Fin n)), ‖x‖ ≤ R →
        (⨆ ε ∈ Set.Ioi (0 : ℝ), ENNReal.ofReal
            |∫ y in {y : EuclideanSpace ℝ (Fin n) | ε < ‖x - y‖},
              GaussRieszKernel j x y * (f : EuclideanSpace ℝ (Fin n) → ℝ) y|)
          ≤ C * ((LocalMaximalFunction
                    (Set.indicator (closedBall (0 : EuclideanSpace ℝ (Fin n)) (R + 2))
                      (fun y => Real.sqrt
                        |(T f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) y j|)) x) ^ 2
                + LocalMaximalFunction
                    (Set.indicator (closedBall (0 : EuclideanSpace ℝ (Fin n)) (R + 2))
                      (f : EuclideanSpace ℝ (Fin n) → ℝ)) x
                + ENNReal.ofReal
                    (∫ y, |(f : EuclideanSpace ℝ (Fin n) → ℝ) y| ∂(GaussMeasure n))) := by
  classical
  have hn : 0 < n := Fin.pos j
  have : Nonempty (Fin n) := ⟨j⟩
  have hpi : (0:ℝ) < Real.pi ^ ((n:ℝ)/2) := Real.rpow_pos_of_pos Real.pi_pos _
  obtain ⟨C2, hC20, hC2⟩ := GaussRieszKernelTruncationDifference j R hR
  obtain ⟨K3, hK30, hK3⟩ := CoordinateEndpointLevelSetSmall T hext hT j R hR
  obtain ⟨K4, hK40, hK4⟩ := LocalMaximalLevelSetSmall hn R hR
  obtain ⟨Ca, hCa0, hCaa, hCaint⟩ := (GaussRieszKernelFarMajorant j).1 R 1 (by linarith) one_pos
  obtain ⟨p, hp0, hpdef⟩ : ∃ p : ℝ, 0 < p ∧ p = Real.pi ^ (-(n : ℝ) / 2) :=
    ⟨_, Real.rpow_pos_of_pos Real.pi_pos _, rfl⟩
  obtain ⟨q, hq0, hqdef⟩ : ∃ q : ℝ, 0 < q ∧ q = Real.pi ^ ((n : ℝ) / 2) :=
    ⟨_, Real.rpow_pos_of_pos Real.pi_pos _, rfl⟩
  -- the single constant
  obtain ⟨c, hc0, hcA, hcB, hcC, hcD⟩ : ∃ c : ℝ, 0 < c ∧ C2 + K3 * p ≤ c ∧ K4 ^ 2 ≤ c
      ∧ C2 * q ≤ c ∧ Ca * q ≤ c := by
    refine ⟨max (C2 + K3 * p) (max (K4 ^ 2) (max (C2 * q) (Ca * q))), ?_, le_max_left _ _,
      ?_, ?_, ?_⟩
    · exact lt_of_lt_of_le (by positivity) (le_max_left _ _)
    · exact le_trans (le_max_left _ _) (le_max_right _ _)
    · exact le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_right _ _)
    · exact le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) (le_max_right _ _)
  refine ⟨ENNReal.ofReal c, by simp [ENNReal.ofReal_eq_zero, not_le, hc0],
    ENNReal.ofReal_ne_top, ?_⟩
  intro f x hxR
  set F : EuclideanSpace ℝ (Fin n) → ℝ := (f : EuclideanSpace ℝ (Fin n) → ℝ) with hFdef
  set w : EuclideanSpace ℝ (Fin n) → ℝ :=
    Set.indicator (closedBall (0 : EuclideanSpace ℝ (Fin n)) (R + 2)) F with hwdef
  set u : EuclideanSpace ℝ (Fin n) → ℝ :=
    Set.indicator (closedBall (0 : EuclideanSpace ℝ (Fin n)) (R + 2))
      (fun y => Real.sqrt
        |(T f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) y j|) with hudef
  -- STEP 0: the infinite cases
  rcases eq_or_ne (LocalMaximalFunction w x) ⊤ with hΦtop | hΦtop
  · have htop : (LocalMaximalFunction u x) ^ 2 + LocalMaximalFunction w x
        + ENNReal.ofReal (∫ y, |F y| ∂(GaussMeasure n)) = ⊤ := by
      rw [hΦtop]; simp
    rw [htop, ENNReal.mul_top (by simp [ENNReal.ofReal_eq_zero, not_le, hc0])]
    exact le_top
  rcases eq_or_ne (LocalMaximalFunction u x) ⊤ with hΨtop | hΨtop
  · have htop : (LocalMaximalFunction u x) ^ 2 + LocalMaximalFunction w x
        + ENNReal.ofReal (∫ y, |F y| ∂(GaussMeasure n)) = ⊤ := by
      rw [hΨtop]; simp
    rw [htop, ENNReal.mul_top (by simp [ENNReal.ofReal_eq_zero, not_le, hc0])]
    exact le_top
  -- the two maximal values as reals
  obtain ⟨φ, hφ0, hφval⟩ : ∃ φ : ℝ, 0 ≤ φ ∧ ENNReal.ofReal φ = LocalMaximalFunction w x :=
    ⟨(LocalMaximalFunction w x).toReal, ENNReal.toReal_nonneg,
      ENNReal.ofReal_toReal hΦtop⟩
  obtain ⟨ψ, hψ0, hψval⟩ : ∃ ψ : ℝ, 0 ≤ ψ ∧ ENNReal.ofReal ψ = LocalMaximalFunction u x :=
    ⟨(LocalMaximalFunction u x).toReal, ENNReal.toReal_nonneg,
      ENNReal.ofReal_toReal hΨtop⟩
  -- STEP 1: the averaged bounds, in the shape the helpers want
  have hmaxgen : ∀ (v : EuclideanSpace ℝ (Fin n) → ℝ) (ρ : ℝ), 0 < ρ → ρ ≤ 2 →
      ∫⁻ y in closedBall x ρ, ‖v y‖ₑ
        ≤ LocalMaximalFunction v x * volume (closedBall x ρ) := by
    intro v ρ hρ0 hρ2
    have hle : (volume (closedBall x ρ))⁻¹ * ∫⁻ y in closedBall x ρ, ‖v y‖ₑ
        ≤ LocalMaximalFunction v x := by
      rw [LocalMaximalFunction]
      exact le_biSup (fun ρ : ℝ => (volume (closedBall x ρ))⁻¹
        * ∫⁻ y in closedBall x ρ, ‖v y‖ₑ) (Set.mem_Ioc.2 ⟨hρ0, hρ2⟩)
    have hv0 : volume (closedBall x ρ) ≠ 0 := (measure_closedBall_pos volume x hρ0).ne'
    have hvtop : volume (closedBall x ρ) ≠ ⊤ := measure_closedBall_lt_top.ne
    calc ∫⁻ y in closedBall x ρ, ‖v y‖ₑ
        = volume (closedBall x ρ)
            * ((volume (closedBall x ρ))⁻¹ * ∫⁻ y in closedBall x ρ, ‖v y‖ₑ) := by
          rw [← mul_assoc, ENNReal.mul_inv_cancel hv0 hvtop, one_mul]
      _ ≤ volume (closedBall x ρ) * LocalMaximalFunction v x := mul_le_mul' le_rfl hle
      _ = LocalMaximalFunction v x * volume (closedBall x ρ) := by ring
  -- STEP 2: the Gaussian-to-Lebesgue density conversion, by citation
  have hacv : (volume : Measure (EuclideanSpace ℝ (Fin n))) ≪ GaussMeasure n := by
    have h4 := (GaussLebesgueBallComparison (n := n)).2.2.2
    exact Measure.AbsolutelyContinuous.mk fun s _ hs0 => (h4 s).1 hs0
  have hFmem : MemLp F 1 (GaussMeasure n) := Lp.memLp f
  have hN0 : (0:ℝ) ≤ ∫ y, |F y| ∂(GaussMeasure n) := integral_nonneg fun y => abs_nonneg _
  obtain ⟨hexpF, hexpbd⟩ := GaussLebesgueL1DensityTransfer f
  rw [← hFdef] at hexpF hexpbd
  rw [← hqdef] at hexpbd
  -- reduce the `ENNReal` goal to a single real inequality
  rw [show ENNReal.ofReal c * ((LocalMaximalFunction u x) ^ 2 + LocalMaximalFunction w x
        + ENNReal.ofReal (∫ y, |F y| ∂(GaussMeasure n)))
      = ENNReal.ofReal (c * (ψ ^ 2 + φ + ∫ y, |F y| ∂(GaussMeasure n))) from by
    rw [← hψval, ← hφval, ← ENNReal.ofReal_pow hψ0, ← ENNReal.ofReal_add (by positivity) hφ0,
      ← ENNReal.ofReal_add (by positivity) hN0, ← ENNReal.ofReal_mul hc0.le]]
  refine iSup₂_le fun ε hε => ?_
  have hε0 : 0 < ε := hε
  refine ENNReal.ofReal_le_ofReal ?_
  have hSmeas : ∀ δ : ℝ, MeasurableSet {y : EuclideanSpace ℝ (Fin n) | δ < ‖x - y‖} :=
    fun δ => measurableSet_lt measurable_const (by fun_prop)
  -- STEP 3: the trivial range `ε ≥ 1`
  rcases le_or_gt 1 ε with hε1 | hε1
  · have hsub : {y : EuclideanSpace ℝ (Fin n) | ε < ‖x - y‖}
        ⊆ {y : EuclideanSpace ℝ (Fin n) | 1 < ‖x - y‖} := fun y hy => lt_of_le_of_lt hε1 hy
    have hintS : IntegrableOn (fun y => GaussRieszKernel j x y * F y)
        {y : EuclideanSpace ℝ (Fin n) | ε < ‖x - y‖} volume :=
      ((hCaint F hFmem x hxR).1).mono_set hsub
    calc |∫ y in {y : EuclideanSpace ℝ (Fin n) | ε < ‖x - y‖}, GaussRieszKernel j x y * F y|
        ≤ ∫ y in {y : EuclideanSpace ℝ (Fin n) | ε < ‖x - y‖},
            ‖GaussRieszKernel j x y * F y‖ := by
          rw [← Real.norm_eq_abs]; exact norm_integral_le_integral_norm _
      _ ≤ ∫ y in {y : EuclideanSpace ℝ (Fin n) | ε < ‖x - y‖},
            Ca * (Real.exp (-‖y‖ ^ 2) * |F y|) := by
          refine setIntegral_mono_on hintS.norm ((hexpF.const_mul Ca).integrableOn)
            (hSmeas ε) fun y hy => ?_
          rw [Real.norm_eq_abs, abs_mul, ← mul_assoc]
          exact mul_le_mul_of_nonneg_right ((hCaa x y hxR (le_of_lt (hsub hy))).2)
            (abs_nonneg _)
      _ ≤ ∫ y, Ca * (Real.exp (-‖y‖ ^ 2) * |F y|) :=
          setIntegral_le_integral (hexpF.const_mul Ca)
            (Filter.Eventually.of_forall fun y => by positivity)
      _ = Ca * ∫ y, Real.exp (-‖y‖ ^ 2) * |F y| := integral_const_mul _ _
      _ ≤ Ca * (q * ∫ y, |F y| ∂(GaussMeasure n)) :=
          mul_le_mul_of_nonneg_left hexpbd hCa0.le
      _ = (Ca * q) * ∫ y, |F y| ∂(GaussMeasure n) := by ring
      _ ≤ c * ∫ y, |F y| ∂(GaussMeasure n) := mul_le_mul_of_nonneg_right hcD hN0
      _ ≤ c * (ψ ^ 2 + φ + ∫ y, |F y| ∂(GaussMeasure n)) := by
          have : (0:ℝ) ≤ ψ ^ 2 + φ := by positivity
          nlinarith [hc0.le]
  have hε1' : ε ≤ 1 := hε1.le
  -- the averaged bound, transported to any function dominated by `|f|`
  have hdomw : ∀ (v : EuclideanSpace ℝ (Fin n) → ℝ) (ρ : ℝ), 0 < ρ → ρ ≤ 2 →
      (∀ y, |v y| ≤ |F y|) →
      ∫⁻ y in closedBall x ρ, ‖v y‖ₑ ≤ ENNReal.ofReal φ * volume (closedBall x ρ) := by
    intro v ρ hρ0 hρ2 hv
    calc ∫⁻ y in closedBall x ρ, ‖v y‖ₑ
        ≤ ∫⁻ y in closedBall x ρ, ‖w y‖ₑ := by
          refine lintegral_mono_ae (ae_restrict_of_forall_mem measurableSet_closedBall
            fun y hy => ?_)
          have hy2 : y ∈ closedBall (0 : EuclideanSpace ℝ (Fin n)) (R + 2) := by
            rw [mem_closedBall, dist_zero_right]
            have := mem_closedBall.1 hy
            rw [dist_eq_norm] at this
            have h1 : ‖y‖ ≤ ‖y - x‖ + ‖x‖ := by
              simpa using norm_add_le (y - x) x
            linarith
          rw [hwdef, Set.indicator_of_mem hy2, Real.enorm_eq_ofReal_abs,
            Real.enorm_eq_ofReal_abs]
          exact ENNReal.ofReal_le_ofReal (hv y)
      _ ≤ LocalMaximalFunction w x * volume (closedBall x ρ) := hmaxgen w ρ hρ0 hρ2
      _ = ENNReal.ofReal φ * volume (closedBall x ρ) := by rw [hφval]
  -- STEP 4: the splitting
  have hmemh : MemLp (Set.indicator (closedBall x ε) F) 1 (GaussMeasure n) :=
    hFmem.indicator measurableSet_closedBall
  obtain ⟨hL, hLcoe⟩ : ∃ hL : Lp ℝ 1 (GaussMeasure n),
      (hL : EuclideanSpace ℝ (Fin n) → ℝ)
        =ᵐ[GaussMeasure n] Set.indicator (closedBall x ε) F :=
    ⟨hmemh.toLp _, hmemh.coeFn_toLp⟩
  set G : EuclideanSpace ℝ (Fin n) → ℝ :=
    Set.indicator {y : EuclideanSpace ℝ (Fin n) | ε < ‖x - y‖} F with hGdef
  have hGcoe : ((f - hL : Lp ℝ 1 (GaussMeasure n)) : EuclideanSpace ℝ (Fin n) → ℝ)
      =ᵐ[GaussMeasure n] G := by
    filter_upwards [Lp.coeFn_sub f hL, hLcoe] with y h1 h2
    rw [h1, Pi.sub_apply, h2, hGdef]
    by_cases hy : ‖x - y‖ ≤ ε
    · have hyB : y ∈ closedBall x ε := by
        rw [mem_closedBall, dist_comm, dist_eq_norm]; exact hy
      rw [Set.indicator_of_mem hyB, Set.indicator_of_notMem (by
        simp only [Set.mem_ofPred_eq]; linarith), sub_self]
    · rw [Set.indicator_of_notMem (by
        simpa only [mem_closedBall, dist_comm y x, dist_eq_norm] using hy),
        Set.indicator_of_mem (by simp only [Set.mem_ofPred_eq]; linarith), sub_zero]
  have hGvan : ∀ y, ‖x - y‖ ≤ ε → G y = 0 := fun y hy => by
    rw [hGdef]
    exact Set.indicator_of_notMem (by simp only [Set.mem_ofPred_eq]; linarith) _
  have hGabs : ∀ y, |G y| ≤ |F y| := fun y => by
    rw [hGdef]
    by_cases hy : y ∈ {y : EuclideanSpace ℝ (Fin n) | ε < ‖x - y‖}
    · rw [Set.indicator_of_mem hy]
    · rw [Set.indicator_of_notMem hy, abs_zero]; exact abs_nonneg _
  have hGmem : MemLp G 1 (GaussMeasure n) := by
    rw [hGdef]; exact hFmem.indicator (hSmeas ε)
  -- STEP 5: the two representations
  have hgLvan : ∀ᵐ y ∂(GaussMeasure n), y ∈ ball x ε →
      ((f - hL : Lp ℝ 1 (GaussMeasure n)) : EuclideanSpace ℝ (Fin n) → ℝ) y = 0 := by
    filter_upwards [hGcoe] with y hy hmem
    rw [hy]
    exact hGvan y (le_of_lt (by
      simpa only [mem_ball, dist_comm y x, dist_eq_norm] using hmem))
  obtain ⟨hOD1, hOD2⟩ := GaussRieszOffDiagonalL1 T hext hT (f - hL) j x ε hε0 hgLvan
  have hGcoev : ((f - hL : Lp ℝ 1 (GaussMeasure n)) : EuclideanSpace ℝ (Fin n) → ℝ)
      =ᵐ[volume] G := hacv.ae_eq hGcoe
  have hODG : ∀ z ∈ ball x (ε / 2),
      (∫ y, GaussRieszKernel j z y
          * ((f - hL : Lp ℝ 1 (GaussMeasure n)) : EuclideanSpace ℝ (Fin n) → ℝ) y)
        = ∫ y, GaussRieszKernel j z y * G y := fun z hz =>
    integral_congr_ae (by filter_upwards [hGcoev] with y hy using by rw [hy])
  have h6 : (∫ y in {y : EuclideanSpace ℝ (Fin n) | ε < ‖x - y‖}, GaussRieszKernel j x y * F y)
      = ∫ y, GaussRieszKernel j x y * G y := by
    rw [← integral_indicator (hSmeas ε)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    by_cases hy : y ∈ {y : EuclideanSpace ℝ (Fin n) | ε < ‖x - y‖}
    · rw [Set.indicator_of_mem hy]
      show GaussRieszKernel j x y * F y = GaussRieszKernel j x y * G y
      rw [hGdef, Set.indicator_of_mem hy]
    · rw [Set.indicator_of_notMem hy]
      show (0:ℝ) = GaussRieszKernel j x y * G y
      rw [hGdef, Set.indicator_of_notMem hy, mul_zero]
  -- STEP 6: display (7), from the pre-built helper
  have hexpGeq : ∀ y : EuclideanSpace ℝ (Fin n), Real.exp (-‖y‖ ^ 2) * |G y|
      = Set.indicator {y : EuclideanSpace ℝ (Fin n) | ε < ‖x - y‖}
          (fun y => Real.exp (-‖y‖ ^ 2) * |F y|) y := fun y => by
    rw [hGdef]
    by_cases hy : y ∈ {y : EuclideanSpace ℝ (Fin n) | ε < ‖x - y‖}
    · rw [Set.indicator_of_mem hy, Set.indicator_of_mem hy]
    · rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem hy, abs_zero, mul_zero]
  have hexpG : Integrable (fun y => Real.exp (-‖y‖ ^ 2) * |G y|)
      (volume : Measure (EuclideanSpace ℝ (Fin n))) :=
    (hexpF.indicator (hSmeas ε)).congr (Filter.Eventually.of_forall fun y => (hexpGeq y).symm)
  have hexpGbd : (∫ y, Real.exp (-‖y‖ ^ 2) * |G y|)
      ≤ q * ∫ y, |F y| ∂(GaussMeasure n) :=
    le_trans (integral_mono hexpG hexpF fun y =>
      mul_le_mul_of_nonneg_left (hGabs y) (Real.exp_pos _).le) hexpbd
  have h7 : ∀ z ∈ ball x (ε / 2),
      |(∫ y, GaussRieszKernel j x y * G y) - ∫ y, GaussRieszKernel j z y * G y|
        ≤ C2 * (φ + q * ∫ y, |F y| ∂(GaussMeasure n)) := by
    intro z hz
    refine hC2 G φ (q * ∫ y, |F y| ∂(GaussMeasure n)) x z ε hxR hε0 hε1' ?_ hGmem
      (Filter.Eventually.of_forall hGvan) hφ0
      (fun ρ hρ0 hρ2 => hdomw G ρ hρ0 hρ2 hGabs) hexpG hexpGbd
    simpa only [mem_ball, dist_comm z x, dist_eq_norm] using hz
  -- STEP 7: the good set is nonempty
  have hγB0 : GaussMeasure n (ball x (ε / 2)) ≠ 0 := fun hcz =>
    (measure_ball_pos volume x (by positivity)).ne'
      (((GaussLebesgueBallComparison (n := n)).2.2.2 _).1 hcz)
  have hγBtop : GaussMeasure n (ball x (ε / 2)) ≠ ⊤ := measure_ne_top _ _
  have hvcb : volume (closedBall x ε) = volume (ball x ε) := by
    rw [Measure.addHaar_closedBall _ _ hε0.le, Measure.addHaar_ball _ _ hε0.le]
  -- the `E₁` input: the `L¹(γ)` norm of the near part
  have hhLbd : (∫ y, |(hL : EuclideanSpace ℝ (Fin n) → ℝ) y| ∂(GaussMeasure n))
      ≤ p * φ * (volume (ball x ε)).toReal := by
    obtain ⟨V, hV0, hVdef, hVr⟩ : ∃ V : ℝ, 0 ≤ V ∧ V = (volume (ball x ε)).toReal
        ∧ ENNReal.ofReal V = volume (ball x ε) :=
      ⟨_, ENNReal.toReal_nonneg, rfl, ENNReal.ofReal_toReal (by
        rw [← hvcb]; exact measure_closedBall_lt_top.ne)⟩
    rw [← hVdef]
    refine (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 ?_
    have hhint : Integrable (hL : EuclideanSpace ℝ (Fin n) → ℝ) (GaussMeasure n) :=
      memLp_one_iff_integrable.1 (Lp.memLp hL)
    have hL1 : ENNReal.ofReal (∫ y, |(hL : EuclideanSpace ℝ (Fin n) → ℝ) y| ∂(GaussMeasure n))
        = ∫⁻ y, ‖(hL : EuclideanSpace ℝ (Fin n) → ℝ) y‖ₑ ∂(GaussMeasure n) := by
      rw [← ofReal_integral_norm_eq_lintegral_enorm hhint]
      simp [Real.norm_eq_abs]
    have hL2 : ∫⁻ y, ‖(hL : EuclideanSpace ℝ (Fin n) → ℝ) y‖ₑ ∂(GaussMeasure n)
        = ∫⁻ y in closedBall x ε, ‖F y‖ₑ ∂(GaussMeasure n) := by
      rw [← lintegral_indicator (μ := GaussMeasure n) (f := fun y => ‖F y‖ₑ)
        measurableSet_closedBall]
      refine lintegral_congr_ae ?_
      filter_upwards [hLcoe] with y hy
      rw [hy]
      by_cases hmem : y ∈ closedBall x ε
      · rw [Set.indicator_of_mem hmem, Set.indicator_of_mem hmem]
      · rw [Set.indicator_of_notMem hmem, Set.indicator_of_notMem hmem]
        simp
    have hγle : GaussMeasure n
        ≤ (ENNReal.ofReal p) • (volume : Measure (EuclideanSpace ℝ (Fin n))) :=
      Measure.le_iff.2 fun s _ => by
        rw [Measure.smul_apply, smul_eq_mul, hpdef]
        exact (GaussLebesgueBallComparison (n := n)).1 s
    have hL3 : ∫⁻ y in closedBall x ε, ‖F y‖ₑ ∂(GaussMeasure n)
        ≤ ENNReal.ofReal p
            * ∫⁻ y in closedBall x ε, ‖F y‖ₑ ∂(volume : Measure (EuclideanSpace ℝ (Fin n))) := by
      calc ∫⁻ y in closedBall x ε, ‖F y‖ₑ ∂(GaussMeasure n)
          ≤ ∫⁻ y in closedBall x ε, ‖F y‖ₑ
              ∂((ENNReal.ofReal p) • (volume : Measure (EuclideanSpace ℝ (Fin n)))) :=
            lintegral_mono' (Measure.restrict_mono subset_rfl hγle) le_rfl
        _ = _ := by rw [Measure.restrict_smul, lintegral_smul_measure, smul_eq_mul]
    rw [hL1, hL2, ENNReal.ofReal_mul (by positivity : (0:ℝ) ≤ p * φ),
      ENNReal.ofReal_mul hp0.le, hVr, ← hvcb, mul_assoc]
    exact le_trans hL3 (mul_le_mul' le_rfl (hdomw F ε hε0 (by linarith) fun _ => le_rfl))
  have hE1 := hK3 hL x ε (p * φ) hxR hε0 hε1' (by positivity) hhLbd
  -- the `E₂` input
  have hunn : ∀ y, 0 ≤ u y := fun y => by
    rw [hudef]
    by_cases hy : y ∈ closedBall (0 : EuclideanSpace ℝ (Fin n)) (R + 2)
    · rw [Set.indicator_of_mem hy]; exact Real.sqrt_nonneg _
    · rw [Set.indicator_of_notMem hy]
  have humeas : AEMeasurable u (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
    have h0 : AEStronglyMeasurable (T f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
        (GaussMeasure n) := AEEqFun.aestronglyMeasurable _
    have h1 : AEMeasurable (T f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
        (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
      obtain ⟨gg, hgg, hggae⟩ := h0
      exact ⟨gg, hgg.measurable, hacv.ae_eq hggae⟩
    have hcc : Continuous (fun v : EuclideanSpace ℝ (Fin n) => Real.sqrt |v j|) := by fun_prop
    rw [hudef]
    exact (hcc.measurable.comp_aemeasurable h1).indicator measurableSet_closedBall
  have hE2 := hK4 u x ε ψ hxR hε0 hε1' hψ0 hunn humeas (by
    rw [hψval]; exact hmaxgen u (ε / 2) (by positivity) (by linarith))
  -- the two free null sets
  have hN1 := ae_iff.1 hOD2
  have hN2 : GaussMeasure n {z : EuclideanSpace ℝ (Fin n) |
      ¬((T (f - hL) : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) z j
        = (T f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) z j
          - (T hL : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) z j)} = 0 := by
    refine ae_iff.1 ?_
    have h1 : T (f - hL) = T f - T hL := map_sub T f hL
    filter_upwards [AEEqFun.coeFn_sub (T f) (T hL)] with z hz
    rw [h1, hz]
    rfl
  -- subadditivity: a ball cannot be covered by two quarter-sets and two null sets
  have hkey : ∀ A1 A2 A3 A4 : Set (EuclideanSpace ℝ (Fin n)),
      GaussMeasure n A1 ≤ GaussMeasure n (ball x (ε / 2)) / 4 →
      GaussMeasure n A2 ≤ GaussMeasure n (ball x (ε / 2)) / 4 →
      GaussMeasure n A3 = 0 → GaussMeasure n A4 = 0 →
      ¬(ball x (ε / 2) ⊆ A1 ∪ A2 ∪ A3 ∪ A4) := by
    intro A1 A2 A3 A4 h1 h2 h3 h4 hs
    have hmm : GaussMeasure n (ball x (ε / 2)) ≤ GaussMeasure n (A1 ∪ A2 ∪ A3 ∪ A4) :=
      measure_mono hs
    refine absurd hmm (not_le.2 ?_)
    calc GaussMeasure n (A1 ∪ A2 ∪ A3 ∪ A4)
        ≤ GaussMeasure n A1 + GaussMeasure n A2 + GaussMeasure n A3 + GaussMeasure n A4 :=
          le_trans (measure_union_le _ _) (add_le_add (le_trans (measure_union_le _ _)
            (add_le_add (measure_union_le _ _) le_rfl)) le_rfl)
      _ ≤ GaussMeasure n (ball x (ε / 2)) / 4 + GaussMeasure n (ball x (ε / 2)) / 4 + 0 + 0 := by
          rw [h3, h4]
          exact add_le_add (add_le_add (add_le_add h1 h2) le_rfl) le_rfl
      _ < GaussMeasure n (ball x (ε / 2)) := by
          rw [add_zero, add_zero, ENNReal.div_add_div_same,
            ENNReal.div_lt_iff (by norm_num) (by norm_num),
            show GaussMeasure n (ball x (ε / 2)) * 4
              = (GaussMeasure n (ball x (ε / 2)) + GaussMeasure n (ball x (ε / 2)))
                + (GaussMeasure n (ball x (ε / 2)) + GaussMeasure n (ball x (ε / 2))) from by
              ring]
          exact ENNReal.lt_add_right (ENNReal.add_ne_top.2 ⟨hγBtop, hγBtop⟩) (by simp [hγB0])
  obtain ⟨z, hzB, hzE1, hzE2, hz5, hz9⟩ : ∃ z, z ∈ ball x (ε / 2)
      ∧ |(T hL : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) z j| ≤ K3 * (p * φ)
      ∧ u z ≤ K4 * ψ
      ∧ (T (f - hL) : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) z j
          = ∫ y, GaussRieszKernel j z y
              * ((f - hL : Lp ℝ 1 (GaussMeasure n)) : EuclideanSpace ℝ (Fin n) → ℝ) y
      ∧ (T (f - hL) : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) z j
          = (T f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) z j
            - (T hL : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) z j := by
    by_contra hcon
    refine hkey _ _ _ _ hE1 hE2 hN1 hN2 fun z hz => ?_
    by_cases h1 : K3 * (p * φ)
        < |(T hL : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) z j|
    · exact Or.inl (Or.inl (Or.inl ⟨hz, h1⟩))
    by_cases h2 : K4 * ψ < u z
    · exact Or.inl (Or.inl (Or.inr ⟨hz, h2⟩))
    by_cases h3 : (T (f - hL) : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) z j
        = ∫ y, GaussRieszKernel j z y
            * ((f - hL : Lp ℝ 1 (GaussMeasure n)) : EuclideanSpace ℝ (Fin n) → ℝ) y
    · by_cases h4 : (T (f - hL) : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) z j
          = (T f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) z j
            - (T hL : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) z j
      · exact absurd ⟨z, hz, not_lt.1 h1, not_lt.1 h2, h3, h4⟩ hcon
      · exact Or.inr h4
    · exact Or.inl (Or.inr fun hh => h3 (hh hz))
  -- STEP 8: conclusion
  have hzmem : z ∈ closedBall (0 : EuclideanSpace ℝ (Fin n)) (R + 2) := by
    rw [mem_closedBall, dist_zero_right]
    have h1 : ‖z‖ ≤ ‖z - x‖ + ‖x‖ := by simpa using norm_add_le (z - x) x
    have h2 : ‖z - x‖ < ε / 2 := by
      simpa only [mem_ball, dist_eq_norm] using hzB
    linarith
  have hTf2 : |(T f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) z j|
      ≤ (K4 * ψ) ^ 2 := by
    have h1 : Real.sqrt |(T f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) z j|
        ≤ K4 * ψ := by
      have h0 : u z = Real.sqrt
          |(T f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) z j| := by
        rw [hudef, Set.indicator_of_mem hzmem]
      rw [← h0]; exact hzE2
    nlinarith [Real.sq_sqrt (abs_nonneg
      ((T f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) z j)),
      Real.sqrt_nonneg |(T f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) z j|]
  rw [h6]
  calc |∫ y, GaussRieszKernel j x y * G y|
      ≤ |(∫ y, GaussRieszKernel j x y * G y) - ∫ y, GaussRieszKernel j z y * G y|
          + |∫ y, GaussRieszKernel j z y * G y| := by
        simpa using abs_add_le ((∫ y, GaussRieszKernel j x y * G y)
          - ∫ y, GaussRieszKernel j z y * G y) (∫ y, GaussRieszKernel j z y * G y)
    _ ≤ C2 * (φ + q * ∫ y, |F y| ∂(GaussMeasure n)) + ((K4 * ψ) ^ 2 + K3 * (p * φ)) := by
        refine add_le_add (h7 z hzB) ?_
        rw [← hODG z hzB, ← hz5, hz9]
        exact le_trans (abs_sub _ _) (add_le_add hTf2 hzE1)
    _ = (C2 + K3 * p) * φ + K4 ^ 2 * ψ ^ 2
          + (C2 * q) * ∫ y, |F y| ∂(GaussMeasure n) := by ring
    _ ≤ c * φ + c * ψ ^ 2 + c * ∫ y, |F y| ∂(GaussMeasure n) := by
        have e1 := mul_le_mul_of_nonneg_right hcA hφ0
        have e2 := mul_le_mul_of_nonneg_right hcB (sq_nonneg ψ)
        have e3 := mul_le_mul_of_nonneg_right hcC hN0
        linarith
    _ = c * (ψ ^ 2 + φ + ∫ y, |F y| ∂(GaussMeasure n)) := by ring
