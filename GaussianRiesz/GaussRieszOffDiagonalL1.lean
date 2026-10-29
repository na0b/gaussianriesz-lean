module

public import GaussianRiesz.GaussRieszKernelFarMajorant
public import GaussianRiesz.PVCoreSmooth
public import GaussianRiesz.CoordinateEndpointBound
public import GaussianRiesz.SmoothCompactDenseL1Gauss
public import GaussianRiesz.GaussRieszKernelTruncationRedundant
public import GaussianRiesz.GaussRieszKernelSmoothOffDiagonal
public import GaussianRiesz.RieszSemigroupPointwise
public import GaussianRiesz.GaussLebesgueBallComparison

@[expose] public section
open MeasureTheory Filter Topology
open scoped ENNReal
theorem GaussRieszOffDiagonalL1 {n : ℕ}
    (T : Lp ℝ 1 (GaussMeasure n) →ₗ[ℝ]
      (EuclideanSpace ℝ (Fin n) →ₘ[GaussMeasure n] EuclideanSpace ℝ (Fin n)))
    (hext : ∀ v : Lp ℝ 2 (GaussMeasure n),
      T (ToL1 v) = (RieszTransform v : EuclideanSpace ℝ (Fin n)
        →ₘ[GaussMeasure n] EuclideanSpace ℝ (Fin n)))
    (hT : ∀ (f : Lp ℝ 1 (GaussMeasure n)) (t : ℝ), 0 < t →
      ENNReal.ofReal t * GaussMeasure n {x | t < ‖T f x‖} ≤ ENNReal.ofReal (2 * ‖f‖))
    (g : Lp ℝ 1 (GaussMeasure n)) (j : Fin n)
    (x₀ : EuclideanSpace ℝ (Fin n)) (ρ : ℝ) (hρ : 0 < ρ)
    (hvanish : ∀ᵐ y ∂(GaussMeasure n),
      y ∈ Metric.ball x₀ ρ → (g : EuclideanSpace ℝ (Fin n) → ℝ) y = 0) :
    (∀ z ∈ Metric.ball x₀ (ρ / 2),
        Integrable (fun y => GaussRieszKernel j z y
          * (g : EuclideanSpace ℝ (Fin n) → ℝ) y) volume)
      ∧ (∀ᵐ z ∂(GaussMeasure n), z ∈ Metric.ball x₀ (ρ / 2) →
          (T g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) z j
            = ∫ y, GaussRieszKernel j z y * (g : EuclideanSpace ℝ (Fin n) → ℝ) y) := by
  classical
  have hprob : IsProbabilityMeasure (GaussMeasure n) := GaussIsProb n
  -- STEP 0: the vanishing holds Lebesgue-a.e. too, since the two measures have the same
  -- null sets (clause (4) of `GaussLebesgueBallComparison`).
  have hac : (volume : Measure (EuclideanSpace ℝ (Fin n))) ≪ GaussMeasure n := by
    have h4 := (GaussLebesgueBallComparison (n := n)).2.2.2
    exact Measure.AbsolutelyContinuous.mk fun s _ hs0 => (h4 s).1 hs0
  have hvan34 : ∀ᵐ y ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
      y ∈ Metric.ball x₀ (3 * ρ / 4) → (g : EuclideanSpace ℝ (Fin n) → ℝ) y = 0 := by
    refine hac.ae_le ?_
    filter_upwards [hvanish] with y hy hmem
    exact hy (Metric.ball_subset_ball (by linarith) hmem)
  -- STEP 2 applied to `g`: clause (1) of the lemma, and the truncated form of the integral
  have hgtr := GaussRieszKernelTruncationRedundant j x₀ ρ hρ
    (g : EuclideanSpace ℝ (Fin n) → ℝ) (Lp.memLp g) hvan34
  refine ⟨fun z hz => (hgtr z hz).1, ?_⟩
  -- the far-majorant constant for the pair `(R, rho/4)`, `R = ||x_0|| + rho + 1`
  obtain ⟨C, hC0, -, hCb⟩ := (GaussRieszKernelFarMajorant j).1 (‖x₀‖ + ρ + 1) (ρ / 4)
    (by positivity) (by positivity)
  have hCtend : Tendsto (fun k : ℕ => C * (1 / ((k : ℝ) + 1))) atTop (𝓝 0) := by
    simpa using (tendsto_one_div_add_atTop_nhds_zero_nat).const_mul C
  -- STEP 4, first half: the cut-off, from one `ContDiffBump` at centre `x_0`
  obtain ⟨χ, hχsm, hχ0, hχ1, hχvan, hχoff⟩ :
      ∃ χ : EuclideanSpace ℝ (Fin n) → ℝ, ContDiff ℝ (⊤ : ℕ∞) χ
        ∧ (∀ y, 0 ≤ χ y) ∧ (∀ y, χ y ≤ 1)
        ∧ (∀ y, ‖x₀ - y‖ ≤ 7 * ρ / 8 → χ y = 0)
        ∧ (∀ y, y ∉ Metric.ball x₀ (15 * ρ / 16) → χ y = 1) := by
    obtain ⟨b, hbIn, hbOut⟩ : ∃ b : ContDiffBump x₀, b.rIn = 7 * ρ / 8 ∧ b.rOut = 15 * ρ / 16 :=
      ⟨⟨7 * ρ / 8, 15 * ρ / 16, by positivity, by linarith⟩, rfl, rfl⟩
    refine ⟨fun y => 1 - (b : EuclideanSpace ℝ (Fin n) → ℝ) y, contDiff_const.sub b.contDiff,
      fun y => by linarith [ContDiffBump.le_one (f := b) (x := y)],
      fun y => by linarith [ContDiffBump.nonneg (f := b) (x := y)],
      fun y hy => ?_, fun y hy => ?_⟩
    · have hin : y ∈ Metric.closedBall x₀ b.rIn := by
        rw [hbIn]
        simpa [Metric.mem_closedBall, dist_eq_norm, norm_sub_rev] using hy
      show 1 - (b : EuclideanSpace ℝ (Fin n) → ℝ) y = 0
      rw [ContDiffBump.one_of_mem_closedBall b hin]; ring
    · have hout : b.rOut ≤ dist y x₀ := by
        rw [hbOut]
        simpa [Metric.mem_ball, not_lt, dist_comm] using hy
      show 1 - (b : EuclideanSpace ℝ (Fin n) → ℝ) y = 1
      rw [ContDiffBump.zero_of_le_dist (f := b) hout]; ring
  -- STEP 4, second half: the approximants `psi_k = chi * phi_k`
  have hstep4 : ∀ k : ℕ, ∃ (ψ : EuclideanSpace ℝ (Fin n) → ℝ)
      (hm2 : MemLp ψ 2 (GaussMeasure n)), ContDiff ℝ (⊤ : ℕ∞) ψ ∧ HasCompactSupport ψ
        ∧ MemLp ψ 1 (GaussMeasure n)
        ∧ (∀ y, ‖x₀ - y‖ ≤ 7 * ρ / 8 → ψ y = 0)
        ∧ ‖g - ToL1 (hm2.toLp ψ)‖ < 1 / ((k : ℝ) + 1) := by
    intro k
    obtain ⟨φ, hφsm, hφcs, hφmem, hφlt⟩ :=
      SmoothCompactDenseL1Gauss g (1 / ((k : ℝ) + 1)) (by positivity)
    have hsm : ContDiff ℝ (⊤ : ℕ∞) (fun y => χ y * φ y) := hχsm.mul hφsm
    have hcs : HasCompactSupport (fun y => χ y * φ y) := hφcs.mul_left
    obtain ⟨M, hM⟩ := hcs.exists_bound_of_continuous hsm.continuous
    have hm2 : MemLp (fun y => χ y * φ y) 2 (GaussMeasure n) :=
      MemLp.of_bound hsm.continuous.aestronglyMeasurable M (Filter.Eventually.of_forall hM)
    have hm1 : MemLp (fun y => χ y * φ y) 1 (GaussMeasure n) :=
      MemLp.of_bound hsm.continuous.aestronglyMeasurable M (Filter.Eventually.of_forall hM)
    refine ⟨fun y => χ y * φ y, hm2, hsm, hcs, hm1,
      fun y hy => by show χ y * φ y = 0; rw [hχvan y hy]; ring, ?_⟩
    -- the representative of `iota psi_k` is `psi_k`, so the `L^1` norm is the seminorm
    have hrep : ((ToL1 (hm2.toLp (fun y => χ y * φ y))) : EuclideanSpace ℝ (Fin n) → ℝ)
        =ᵐ[GaussMeasure n] fun y => χ y * φ y := by
      refine Filter.EventuallyEq.trans ?_ hm2.coeFn_toLp
      rw [ToL1]; exact MemLp.coeFn_toLp _
    -- `(1 - chi) g = 0` gamma-a.e., so `g - psi_k = chi (g - phi_k)` gamma-a.e.
    have hdiff : ((g - ToL1 (hm2.toLp (fun y => χ y * φ y)) : Lp ℝ 1 (GaussMeasure n)) :
          EuclideanSpace ℝ (Fin n) → ℝ)
        =ᵐ[GaussMeasure n] fun y => χ y * ((g : EuclideanSpace ℝ (Fin n) → ℝ) y - φ y) := by
      filter_upwards [Lp.coeFn_sub g (ToL1 (hm2.toLp (fun y => χ y * φ y))), hrep, hvanish]
        with y h1 h2 h3
      simp only [h1, Pi.sub_apply, h2]
      by_cases hb : y ∈ Metric.ball x₀ (15 * ρ / 16)
      · rw [h3 (Metric.ball_subset_ball (by linarith) hb)]; ring
      · rw [hχoff y hb]; ring
    rw [Lp.norm_def, eLpNorm_congr_ae hdiff]
    refine ENNReal.toReal_lt_of_lt_ofReal (lt_of_le_of_lt (eLpNorm_mono
      (hχsm.continuous.aestronglyMeasurable.mul
        ((Lp.aestronglyMeasurable g).sub hφsm.continuous.aestronglyMeasurable)) ?_) hφlt)
    intro y
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul]
    refine mul_le_of_le_one_left (abs_nonneg _) ?_
    exact abs_le.2 ⟨by linarith [hχ0 y], hχ1 y⟩
  choose ψ hm2 hsm hcs hm1 hvanψ hnorm using hstep4
  -- the canonical representative of `iota psi_k`
  have hToL1 : ∀ k : ℕ, ((ToL1 ((hm2 k).toLp (ψ k))) : EuclideanSpace ℝ (Fin n) → ℝ)
      =ᵐ[GaussMeasure n] ψ k := by
    intro k
    refine Filter.EventuallyEq.trans ?_ (hm2 k).coeFn_toLp
    rw [ToL1]; exact MemLp.coeFn_toLp _
  -- STEP 2 applied to each `psi_k`
  have hψtr : ∀ k : ℕ, ∀ z ∈ Metric.ball x₀ (ρ / 2),
      Integrable (fun y => GaussRieszKernel j z y * ψ k y) volume
        ∧ ∫ y, GaussRieszKernel j z y * ψ k y
            = ∫ y in {y : EuclideanSpace ℝ (Fin n) | ρ / 4 < ‖z - y‖},
              GaussRieszKernel j z y * ψ k y := by
    intro k
    refine GaussRieszKernelTruncationRedundant j x₀ ρ hρ (ψ k) (hm1 k) ?_
    filter_upwards with y hy
    refine hvanψ k y ?_
    have h1 : ‖y - x₀‖ < 3 * ρ / 4 := by
      simpa [Metric.mem_ball, dist_eq_norm] using hy
    rw [norm_sub_rev]; linarith
  -- STEP 5: the right-hand side converges, uniformly on the ball
  have hstep5 : ∀ (k : ℕ) (z : EuclideanSpace ℝ (Fin n)), z ∈ Metric.ball x₀ (ρ / 2) →
      |(∫ y, GaussRieszKernel j z y * ψ k y)
          - ∫ y, GaussRieszKernel j z y * (g : EuclideanSpace ℝ (Fin n) → ℝ) y|
        ≤ C * (1 / ((k : ℝ) + 1)) := by
    intro k z hz
    have hzR : ‖z‖ ≤ ‖x₀‖ + ρ + 1 := by
      have h1 : ‖z - x₀‖ < ρ / 2 := by simpa [Metric.mem_ball, dist_eq_norm] using hz
      have h2 : ‖z‖ - ‖x₀‖ ≤ ‖z - x₀‖ := norm_sub_norm_le z x₀
      linarith
    obtain ⟨hψΩ, -⟩ := hCb (ψ k) (hm1 k) z hzR
    obtain ⟨hgΩ, -⟩ := hCb (g : EuclideanSpace ℝ (Fin n) → ℝ) (Lp.memLp g) z hzR
    obtain ⟨-, hdbd⟩ := hCb
      ((ToL1 ((hm2 k).toLp (ψ k)) - g : Lp ℝ 1 (GaussMeasure n)) :
        EuclideanSpace ℝ (Fin n) → ℝ) (Lp.memLp _) z hzR
    have hrep : ((ToL1 ((hm2 k).toLp (ψ k)) - g : Lp ℝ 1 (GaussMeasure n)) :
          EuclideanSpace ℝ (Fin n) → ℝ)
        =ᵐ[GaussMeasure n] fun y => ψ k y - (g : EuclideanSpace ℝ (Fin n) → ℝ) y := by
      filter_upwards [Lp.coeFn_sub (ToL1 ((hm2 k).toLp (ψ k))) g, hToL1 k] with y h1 h2
      simp only [h1, Pi.sub_apply, h2]
    have hsplit : (∫ y in {y : EuclideanSpace ℝ (Fin n) | ρ / 4 < ‖z - y‖},
          GaussRieszKernel j z y
            * ((ToL1 ((hm2 k).toLp (ψ k)) - g : Lp ℝ 1 (GaussMeasure n)) :
                EuclideanSpace ℝ (Fin n) → ℝ) y)
        = (∫ y in {y : EuclideanSpace ℝ (Fin n) | ρ / 4 < ‖z - y‖},
              GaussRieszKernel j z y * ψ k y)
          - ∫ y in {y : EuclideanSpace ℝ (Fin n) | ρ / 4 < ‖z - y‖},
              GaussRieszKernel j z y * (g : EuclideanSpace ℝ (Fin n) → ℝ) y := by
      rw [← integral_sub hψΩ hgΩ]
      refine integral_congr_ae ?_
      filter_upwards [ae_restrict_of_ae (hac.ae_le hrep)] with y hy
      simp only [hy]; ring
    have hnm : ∫ y, |((ToL1 ((hm2 k).toLp (ψ k)) - g : Lp ℝ 1 (GaussMeasure n)) :
          EuclideanSpace ℝ (Fin n) → ℝ) y| ∂(GaussMeasure n)
        = ‖g - ToL1 ((hm2 k).toLp (ψ k))‖ := by
      rw [← norm_sub_rev, L1.norm_eq_integral_norm]
      simp [Real.norm_eq_abs]
    rw [(hψtr k z hz).2, (hgtr z hz).2, ← hsplit]
    refine hdbd.trans ?_
    rw [hnm]
    exact mul_le_mul_of_nonneg_left (hnorm k).le hC0.le
  -- STEP 6: the left-hand side converges in measure, then along a subsequence a.e.
  have hmeas : ∀ t : ℝ, 0 < t → Tendsto (fun k : ℕ => GaussMeasure n
      {z : EuclideanSpace ℝ (Fin n) | t < |(T (ToL1 ((hm2 k).toLp (ψ k))) :
          EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) z j
        - (T g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) z j|}) atTop (𝓝 0) := by
    intro t ht
    have ht0 : ENNReal.ofReal t ≠ 0 := by
      simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]; exact ht
    have hb : ∀ k : ℕ, GaussMeasure n
        {z : EuclideanSpace ℝ (Fin n) | t < |(T (ToL1 ((hm2 k).toLp (ψ k))) :
            EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) z j
          - (T g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) z j|}
          ≤ (ENNReal.ofReal t)⁻¹ * ENNReal.ofReal (2 * (1 / ((k : ℝ) + 1))) := by
      intro k
      have hlin : T (ToL1 ((hm2 k).toLp (ψ k)) - g)
          = T (ToL1 ((hm2 k).toLp (ψ k))) - T g := map_sub T _ _
      have hset : {z : EuclideanSpace ℝ (Fin n) | t < |(T (ToL1 ((hm2 k).toLp (ψ k))) :
              EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) z j
            - (T g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) z j|}
          =ᵐ[GaussMeasure n] {z : EuclideanSpace ℝ (Fin n) |
            t < |(T (ToL1 ((hm2 k).toLp (ψ k)) - g) :
              EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) z j|} := by
        filter_upwards [AEEqFun.coeFn_sub (T (ToL1 ((hm2 k).toLp (ψ k)))) (T g)] with z hz
        have hzz : (T (ToL1 ((hm2 k).toLp (ψ k)) - g) :
              EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) z j
            = (T (ToL1 ((hm2 k).toLp (ψ k))) :
                EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) z j
              - (T g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) z j := by
          rw [hlin, hz]; rfl
        exact congrArg (fun r : ℝ => t < |r|) hzz.symm
      rw [measure_congr hset]
      have hce := CoordinateEndpointBound T hext hT
        (ToL1 ((hm2 k).toLp (ψ k)) - g) j t ht
      have h2 : ENNReal.ofReal (2 * ‖ToL1 ((hm2 k).toLp (ψ k)) - g‖)
          ≤ ENNReal.ofReal (2 * (1 / ((k : ℝ) + 1))) := by
        refine ENNReal.ofReal_le_ofReal ?_
        rw [norm_sub_rev]; linarith [(hnorm k).le]
      calc GaussMeasure n {z : EuclideanSpace ℝ (Fin n) |
              t < |(T (ToL1 ((hm2 k).toLp (ψ k)) - g) :
                EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) z j|}
          = (ENNReal.ofReal t)⁻¹ * (ENNReal.ofReal t * GaussMeasure n
              {z : EuclideanSpace ℝ (Fin n) |
                t < |(T (ToL1 ((hm2 k).toLp (ψ k)) - g) :
                  EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) z j|}) := by
            rw [← mul_assoc, ENNReal.inv_mul_cancel ht0 ENNReal.ofReal_ne_top, one_mul]
        _ ≤ (ENNReal.ofReal t)⁻¹ * ENNReal.ofReal (2 * (1 / ((k : ℝ) + 1))) :=
            mul_le_mul' le_rfl (hce.trans h2)
    have hreal : Tendsto (fun k : ℕ => 2 * (1 / ((k : ℝ) + 1))) atTop (𝓝 0) := by
      simpa using (tendsto_one_div_add_atTop_nhds_zero_nat).const_mul (2 : ℝ)
    have henn : Tendsto (fun k : ℕ => ENNReal.ofReal (2 * (1 / ((k : ℝ) + 1)))) atTop (𝓝 0) := by
      simpa using ENNReal.tendsto_ofReal hreal
    have hup := ENNReal.Tendsto.const_mul (a := (ENNReal.ofReal t)⁻¹) henn
      (Or.inr (by norm_num [ht]))
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ?_
      (fun _ => zero_le) hb
    simpa using hup
  have hTIM : TendstoInMeasure (GaussMeasure n)
      (fun k z => (T (ToL1 ((hm2 k).toLp (ψ k))) :
        EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) z j) atTop
      (fun z => (T g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) z j) := by
    refine tendstoInMeasure_of_ne_top ?_
    intro ε hε hεtop
    have ht0 : 0 < ε.toReal := ENNReal.toReal_pos (ne_of_gt hε) hεtop
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (hmeas (ε.toReal / 2) (by linarith)) (fun _ => zero_le) (fun k => ?_)
    refine measure_mono fun z hz => ?_
    simp only [Set.mem_ofPred_eq, edist_dist, Real.dist_eq] at hz ⊢
    have h1 : ENNReal.ofReal ε.toReal
        ≤ ENNReal.ofReal |(T (ToL1 ((hm2 k).toLp (ψ k))) :
          EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) z j
            - (T g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) z j| := by
      rwa [ENNReal.ofReal_toReal hεtop]
    have h2 : ε.toReal ≤ |(T (ToL1 ((hm2 k).toLp (ψ k))) :
        EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) z j
          - (T g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) z j| := by
      rwa [ENNReal.ofReal_le_ofReal_iff (abs_nonneg _)] at h1
    linarith
  -- STEP 7: identification of each approximant, and the conclusion
  have hid : ∀ k : ℕ, ∀ᵐ z ∂(GaussMeasure n),
      (T (ToL1 ((hm2 k).toLp (ψ k))) : EuclideanSpace ℝ (Fin n)
          → EuclideanSpace ℝ (Fin n)) z j
        = (Real.sqrt Real.pi)⁻¹ * ∫ s in Set.Ioi (0 : ℝ), (Real.sqrt s)⁻¹ * (Real.exp (-s) *
            ((Real.sqrt 2)⁻¹ * ∫ ζ, fderiv ℝ (ψ k) (Real.exp (-s) • z
                + Real.sqrt (1 - Real.exp (-2 * s)) • ζ)
              (EuclideanSpace.single j (1 : ℝ)) ∂(GaussMeasure n))) := by
    intro k
    rw [hext ((hm2 k).toLp (ψ k))]
    exact (RieszSemigroupPointwise (ψ k) (hsm k) (hcs k) (hm2 k) j).2.2.symm
  obtain ⟨ns, hnsmono, hnsae⟩ := hTIM.exists_seq_tendsto_ae
  filter_upwards [hnsae, ae_all_iff.2 (fun m : ℕ => hid (ns m))] with z hz1 hz2
  intro hzball
  have hzx : ‖x₀ - z‖ < ρ / 2 := by
    rw [norm_sub_rev]; simpa [Metric.mem_ball, dist_eq_norm] using hzball
  have hA : ∀ m : ℕ, (T (ToL1 ((hm2 (ns m)).toLp (ψ (ns m)))) :
      EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) z j
      = ∫ y, GaussRieszKernel j z y * ψ (ns m) y := by
    intro m
    rw [hz2 m]
    refine (GaussRieszKernelSmoothOffDiagonal (ψ (ns m)) (hsm (ns m)) (hcs (ns m)) j z (ρ / 4)
      (by positivity) (fun y hy => hvanψ (ns m) y ?_)).2
    have h3 := dist_triangle x₀ z y
    simp only [dist_eq_norm] at h3
    linarith
  have hB : Tendsto (fun m : ℕ => ∫ y, GaussRieszKernel j z y * ψ (ns m) y) atTop
      (𝓝 (∫ y, GaussRieszKernel j z y * (g : EuclideanSpace ℝ (Fin n) → ℝ) y)) := by
    have hsq : Tendsto (fun m : ℕ => (∫ y, GaussRieszKernel j z y * ψ (ns m) y)
        - ∫ y, GaussRieszKernel j z y * (g : EuclideanSpace ℝ (Fin n) → ℝ) y) atTop (𝓝 0) := by
      refine squeeze_zero_norm (fun m => ?_) (hCtend.comp hnsmono.tendsto_atTop)
      rw [Real.norm_eq_abs]; exact hstep5 (ns m) z hzball
    simpa using hsq.add_const
      (∫ y, GaussRieszKernel j z y * (g : EuclideanSpace ℝ (Fin n) → ℝ) y)
  exact tendsto_nhds_unique (hz1.congr hA) hB
