module

public import GaussianRiesz.SobolevChainRule
public import GaussianRiesz.GaussWeakGradClosed
public import GaussianRiesz.GaussWeakGradUnique
public import GaussianRiesz.GaussIsProb
public import GaussianRiesz.GaussDWitness
public import GaussianRiesz.GaussWeakGradAECongr

@[expose] public section
open MeasureTheory
open scoped ENNReal
theorem GradientLocality {n : ℕ} (u : Lp ℝ 2 (GaussMeasure n)) (hu : u ∈ SobolevW12 n)
    (hu0 : 0 ≤ᵐ[GaussMeasure n] (u : EuclideanSpace ℝ (Fin n) → ℝ)) :
    ∀ᵐ x ∂(GaussMeasure n), (u : EuclideanSpace ℝ (Fin n) → ℝ) x ≤ 0
      → (GaussD u : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) x = 0 := by
  classical
  -- (0) elementary properties of `q_d(t) = sqrt(t^2+d^2) - d` and its derivative factor
  have hqb : ∀ d t : ℝ, 0 < d → |Real.sqrt (t ^ 2 + d ^ 2) - d| ≤ |t| := by
    intro d t hd
    have hd1 : d ≤ Real.sqrt (t ^ 2 + d ^ 2) := by
      have h := Real.sqrt_le_sqrt (show d ^ 2 ≤ t ^ 2 + d ^ 2 by nlinarith [sq_nonneg t])
      rwa [Real.sqrt_sq hd.le] at h
    have hd2 : Real.sqrt (t ^ 2 + d ^ 2) ≤ |t| + d := by
      have hnn : (0:ℝ) ≤ |t| + d := by positivity
      have h := Real.sqrt_le_sqrt
        (show t ^ 2 + d ^ 2 ≤ (|t| + d) ^ 2 by nlinarith [abs_nonneg t, sq_abs t, hd.le])
      rwa [Real.sqrt_sq hnn] at h
    rw [abs_le]
    exact ⟨by linarith [abs_nonneg t], by linarith⟩
  have hq1 : ∀ d t : ℝ, 0 < d → 0 ≤ t → |Real.sqrt (t ^ 2 + d ^ 2) - d - t| ≤ d := by
    intro d t hd ht
    have h1 : t ≤ Real.sqrt (t ^ 2 + d ^ 2) := by
      have h := Real.sqrt_le_sqrt (show t ^ 2 ≤ t ^ 2 + d ^ 2 by nlinarith [sq_nonneg d])
      rwa [Real.sqrt_sq ht] at h
    have h2 : Real.sqrt (t ^ 2 + d ^ 2) ≤ t + d := by
      have hnn : (0:ℝ) ≤ t + d := by linarith
      have h := Real.sqrt_le_sqrt (show t ^ 2 + d ^ 2 ≤ (t + d) ^ 2 by nlinarith)
      rwa [Real.sqrt_sq hnn] at h
    rw [abs_le]
    exact ⟨by linarith, by linarith⟩
  have hΘb : ∀ d t : ℝ, 0 < d → |t / Real.sqrt (t ^ 2 + d ^ 2)| ≤ 1 := by
    intro d t hd
    have hpos : (0:ℝ) < Real.sqrt (t ^ 2 + d ^ 2) := Real.sqrt_pos.2 (by positivity)
    rw [abs_div, abs_of_pos hpos, div_le_one hpos]
    calc |t| = Real.sqrt (t ^ 2) := (Real.sqrt_sq_eq_abs t).symm
      _ ≤ Real.sqrt (t ^ 2 + d ^ 2) := Real.sqrt_le_sqrt (by nlinarith [sq_nonneg d])
  -- (1) the mollification parameters `d k = 1/(k+1)`
  have hδpos : ∀ k : ℕ, (0:ℝ) < 1 / ((k:ℝ) + 1) := by
    intro k
    positivity
  have hδ0 : Filter.Tendsto (fun k : ℕ => 1 / ((k:ℝ) + 1)) Filter.atTop (nhds 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  -- (2) the data of the problem, and a strongly measurable representative of `u`
  have hUm : AEStronglyMeasurable (u : EuclideanSpace ℝ (Fin n) → ℝ) (GaussMeasure n) := Lp.aestronglyMeasurable u
  have hUL2 : MemLp (u : EuclideanSpace ℝ (Fin n) → ℝ) 2 (GaussMeasure n) := Lp.memLp u
  have hGL2 : MemLp (GaussD u : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) 2 (GaussMeasure n) := Lp.memLp (GaussD u)
  have hu0' : ∀ᵐ x ∂(GaussMeasure n), 0 ≤ (u : EuclideanSpace ℝ (Fin n) → ℝ) x := hu0
  obtain ⟨Um, hUmSM, hUmae⟩ : ∃ g : EuclideanSpace ℝ (Fin n) → ℝ,
      StronglyMeasurable g ∧ (u : EuclideanSpace ℝ (Fin n) → ℝ) =ᵐ[GaussMeasure n] g :=
    ⟨hUm.mk _, hUm.stronglyMeasurable_mk, hUm.ae_eq_mk⟩
  have hS : MeasurableSet (Um ⁻¹' Set.Ioi (0:ℝ)) := hUmSM.measurable measurableSet_Ioi
  -- (3) the limit field `1_{u>0} Du`
  have hPmem : MemLp (Set.indicator (Um ⁻¹' Set.Ioi (0:ℝ)) (GaussD u : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))) 2 (GaussMeasure n) :=
    MemLp.indicator hS hGL2
  have hPlcoe : ((hPmem.toLp _ : Lp (EuclideanSpace ℝ (Fin n)) 2 (GaussMeasure n)) : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
      =ᵐ[GaussMeasure n] Set.indicator (Um ⁻¹' Set.Ioi (0:ℝ)) (GaussD u : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) := hPmem.coeFn_toLp
  -- (4) the mollified functions and the chain rule
  have hwmem : ∀ k : ℕ, MemLp
      (fun x => Real.sqrt ((u : EuclideanSpace ℝ (Fin n) → ℝ) x ^ 2 + (1 / ((k:ℝ) + 1)) ^ 2) - 1 / ((k:ℝ) + 1)) 2
      (GaussMeasure n) := by
    intro k
    refine MemLp.of_le hUL2 ?_ (Filter.Eventually.of_forall fun x => ?_)
    · have hc : Continuous (fun t : ℝ =>
          Real.sqrt (t ^ 2 + (1 / ((k:ℝ) + 1)) ^ 2) - 1 / ((k:ℝ) + 1)) := by fun_prop
      exact hc.comp_aestronglyMeasurable hUm
    · show ‖Real.sqrt ((u : EuclideanSpace ℝ (Fin n) → ℝ) x ^ 2 + (1 / ((k:ℝ) + 1)) ^ 2) - 1 / ((k:ℝ) + 1)‖ ≤ ‖(u : EuclideanSpace ℝ (Fin n) → ℝ) x‖
      rw [Real.norm_eq_abs, Real.norm_eq_abs]
      exact hqb _ _ (hδpos k)
  have hCR : ∀ k : ℕ, (hwmem k).toLp _ ∈ SobolevW12 n ∧
      ((GaussD ((hwmem k).toLp _ : Lp ℝ 2 (GaussMeasure n)) : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
        =ᵐ[GaussMeasure n] fun x =>
          ((u : EuclideanSpace ℝ (Fin n) → ℝ) x / Real.sqrt ((u : EuclideanSpace ℝ (Fin n) → ℝ) x ^ 2 + (1 / ((k:ℝ) + 1)) ^ 2)) • (GaussD u : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) x) :=
    fun k => SobolevChainRule _ (hδpos k) u hu ((hwmem k).toLp _) (hwmem k).coeFn_toLp
  -- (5) Step 1: `w_k -> u` in `L²(γₙ)`
  have hstep1 : Filter.Tendsto (fun k : ℕ => ((hwmem k).toLp _ : Lp ℝ 2 (GaussMeasure n)))
      Filter.atTop (nhds u) := by
    rw [tendsto_iff_dist_tendsto_zero]
    refine squeeze_zero (fun k => dist_nonneg) (fun k => ?_) hδ0
    rw [dist_eq_norm]
    refine le_trans (Lp.norm_le_of_ae_bound
      (f := (((hwmem k).toLp _ : Lp ℝ 2 (GaussMeasure n)) - u)) (hδpos k).le ?_) ?_
    · filter_upwards [Lp.coeFn_sub ((hwmem k).toLp _ : Lp ℝ 2 (GaussMeasure n)) u,
        (hwmem k).coeFn_toLp, hu0'] with x h1 h2 h3
      rw [h1]
      show ‖(((hwmem k).toLp _ : Lp ℝ 2 (GaussMeasure n)) : EuclideanSpace ℝ (Fin n) → ℝ) x - (u : EuclideanSpace ℝ (Fin n) → ℝ) x‖
          ≤ 1 / ((k:ℝ) + 1)
      rw [h2, Real.norm_eq_abs]
      exact hq1 _ _ (hδpos k) h3
    · have hone : measureUnivNNReal (GaussMeasure n) = 1 := by simp [measureUnivNNReal]
      rw [hone]
      simp
  -- (6) Step 2: `D w_k -> 1_{u>0} Du` in `L²(γₙ;ℝⁿ)`
  have hfin : ∫⁻ x, ‖(GaussD u : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) x‖ₑ ^ (2:ℝ≥0∞).toReal ∂(GaussMeasure n) ≠ ⊤ := by
    intro htop
    have h := hGL2.eLpNorm_lt_top
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num) hGL2.aestronglyMeasurable, htop,
      ENNReal.top_rpow_of_pos (by norm_num)] at h
    exact absurd h (by simp)
  have hreal : ∀ (k : ℕ) (x : EuclideanSpace ℝ (Fin n)),
      ‖((u : EuclideanSpace ℝ (Fin n) → ℝ) x / Real.sqrt ((u : EuclideanSpace ℝ (Fin n) → ℝ) x ^ 2 + (1 / ((k:ℝ) + 1)) ^ 2)) • (GaussD u : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) x
        - Set.indicator (Um ⁻¹' Set.Ioi (0:ℝ)) (GaussD u : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) x‖ ≤ 2 * ‖(GaussD u : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) x‖ := by
    intro k x
    have h1 : ‖((u : EuclideanSpace ℝ (Fin n) → ℝ) x / Real.sqrt ((u : EuclideanSpace ℝ (Fin n) → ℝ) x ^ 2 + (1 / ((k:ℝ) + 1)) ^ 2)) • (GaussD u : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) x‖
        ≤ ‖(GaussD u : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) x‖ := by
      rw [norm_smul, Real.norm_eq_abs]
      exact le_trans (mul_le_mul_of_nonneg_right (hΘb _ _ (hδpos k)) (norm_nonneg _))
        (by rw [one_mul])
    have h2 : ‖Set.indicator (Um ⁻¹' Set.Ioi (0:ℝ)) (GaussD u : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) x‖ ≤ ‖(GaussD u : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) x‖ := by
      by_cases hx : x ∈ Um ⁻¹' Set.Ioi (0:ℝ)
      · rw [Set.indicator_of_mem hx]
      · rw [Set.indicator_of_notMem hx, norm_zero]
        exact norm_nonneg _
    calc ‖((u : EuclideanSpace ℝ (Fin n) → ℝ) x / Real.sqrt ((u : EuclideanSpace ℝ (Fin n) → ℝ) x ^ 2 + (1 / ((k:ℝ) + 1)) ^ 2)) • (GaussD u : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) x
            - Set.indicator (Um ⁻¹' Set.Ioi (0:ℝ)) (GaussD u : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) x‖
        ≤ ‖((u : EuclideanSpace ℝ (Fin n) → ℝ) x / Real.sqrt ((u : EuclideanSpace ℝ (Fin n) → ℝ) x ^ 2 + (1 / ((k:ℝ) + 1)) ^ 2)) • (GaussD u : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) x‖
          + ‖Set.indicator (Um ⁻¹' Set.Ioi (0:ℝ)) (GaussD u : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) x‖ := norm_sub_le _ _
      _ ≤ ‖(GaussD u : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) x‖ + ‖(GaussD u : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) x‖ := add_le_add h1 h2
      _ = 2 * ‖(GaussD u : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) x‖ := by ring
  have hΘlim : ∀ᵐ x ∂(GaussMeasure n), Filter.Tendsto
      (fun k : ℕ => ((u : EuclideanSpace ℝ (Fin n) → ℝ) x / Real.sqrt ((u : EuclideanSpace ℝ (Fin n) → ℝ) x ^ 2 + (1 / ((k:ℝ) + 1)) ^ 2)) • (GaussD u : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) x)
      Filter.atTop (nhds (Set.indicator (Um ⁻¹' Set.Ioi (0:ℝ)) (GaussD u : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) x)) := by
    filter_upwards [hu0', hUmae] with x hx0 hxm
    by_cases hpos : 0 < (u : EuclideanSpace ℝ (Fin n) → ℝ) x
    · have hmem : x ∈ Um ⁻¹' Set.Ioi (0:ℝ) := by
        simp only [Set.mem_preimage, Set.mem_Ioi, ← hxm]
        exact hpos
      rw [Set.indicator_of_mem hmem]
      have hc : Continuous (fun d : ℝ => (u : EuclideanSpace ℝ (Fin n) → ℝ) x / Real.sqrt ((u : EuclideanSpace ℝ (Fin n) → ℝ) x ^ 2 + d ^ 2)) := by
        refine Continuous.div continuous_const (by fun_prop) (fun d => ?_)
        exact (Real.sqrt_pos.2 (by nlinarith [pow_pos hpos 2, sq_nonneg d])).ne'
      have hT := (hc.tendsto 0).comp hδ0
      have hval : (u : EuclideanSpace ℝ (Fin n) → ℝ) x / Real.sqrt ((u : EuclideanSpace ℝ (Fin n) → ℝ) x ^ 2 + (0:ℝ) ^ 2) = 1 := by
        rw [show ((0:ℝ)) ^ 2 = 0 by ring, add_zero, Real.sqrt_sq hpos.le, div_self hpos.ne']
      rw [hval] at hT
      have hfin2 := hT.smul_const ((GaussD u : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) x)
      simpa [Function.comp_def] using hfin2
    · have hx0' : (u : EuclideanSpace ℝ (Fin n) → ℝ) x = 0 := le_antisymm (not_lt.1 hpos) hx0
      have hnm : x ∉ Um ⁻¹' Set.Ioi (0:ℝ) := by
        simp only [Set.mem_preimage, Set.mem_Ioi, ← hxm, hx0']
        exact lt_irrefl 0
      rw [Set.indicator_of_notMem hnm]
      have hz : ∀ k : ℕ, (0 : EuclideanSpace ℝ (Fin n))
          = ((u : EuclideanSpace ℝ (Fin n) → ℝ) x / Real.sqrt ((u : EuclideanSpace ℝ (Fin n) → ℝ) x ^ 2 + (1 / ((k:ℝ) + 1)) ^ 2)) • (GaussD u : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) x := by
        intro k
        rw [hx0', zero_div, zero_smul]
      exact Filter.Tendsto.congr hz tendsto_const_nhds
  have hstep2 : Filter.Tendsto
      (fun k : ℕ => GaussD ((hwmem k).toLp _ : Lp ℝ 2 (GaussMeasure n)))
      Filter.atTop (nhds (hPmem.toLp _)) := by
    rw [tendsto_iff_dist_tendsto_zero]
    have hdist : ∀ k : ℕ,
        dist (GaussD ((hwmem k).toLp _ : Lp ℝ 2 (GaussMeasure n)))
            (hPmem.toLp _ : Lp (EuclideanSpace ℝ (Fin n)) 2 (GaussMeasure n))
          = (eLpNorm (fun x =>
              ((u : EuclideanSpace ℝ (Fin n) → ℝ) x / Real.sqrt ((u : EuclideanSpace ℝ (Fin n) → ℝ) x ^ 2 + (1 / ((k:ℝ) + 1)) ^ 2)) • (GaussD u : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) x
                - Set.indicator (Um ⁻¹' Set.Ioi (0:ℝ)) (GaussD u : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) x) 2 (GaussMeasure n)).toReal := by
      intro k
      rw [dist_eq_norm, Lp.norm_def]
      congr 1
      refine eLpNorm_congr_ae ?_
      filter_upwards [Lp.coeFn_sub (GaussD ((hwmem k).toLp _ : Lp ℝ 2 (GaussMeasure n)))
        (hPmem.toLp _ : Lp (EuclideanSpace ℝ (Fin n)) 2 (GaussMeasure n)), (hCR k).2, hPlcoe] with x h1 h2 h3
      rw [h1]
      show (GaussD ((hwmem k).toLp _ : Lp ℝ 2 (GaussMeasure n)) : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) x
            - ((hPmem.toLp _ : Lp (EuclideanSpace ℝ (Fin n)) 2 (GaussMeasure n)) : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) x
          = ((u : EuclideanSpace ℝ (Fin n) → ℝ) x / Real.sqrt ((u : EuclideanSpace ℝ (Fin n) → ℝ) x ^ 2 + (1 / ((k:ℝ) + 1)) ^ 2)) • (GaussD u : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) x
            - Set.indicator (Um ⁻¹' Set.Ioi (0:ℝ)) (GaussD u : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) x
      rw [h2, h3]
    rw [show (fun k : ℕ => dist (GaussD ((hwmem k).toLp _ : Lp ℝ 2 (GaussMeasure n)))
        (hPmem.toLp _ : Lp (EuclideanSpace ℝ (Fin n)) 2 (GaussMeasure n))) = _ from funext hdist]
    -- the `ℝ≥0∞`-valued `L²` distance tends to zero by dominated convergence
    have hL : Filter.Tendsto (fun k : ℕ => ∫⁻ x, ‖((u : EuclideanSpace ℝ (Fin n) → ℝ) x
          / Real.sqrt ((u : EuclideanSpace ℝ (Fin n) → ℝ) x ^ 2 + (1 / ((k:ℝ) + 1)) ^ 2)) • (GaussD u : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) x
            - Set.indicator (Um ⁻¹' Set.Ioi (0:ℝ)) (GaussD u : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) x‖ₑ ^ (2:ℝ≥0∞).toReal
          ∂(GaussMeasure n)) Filter.atTop (nhds 0) := by
      have hz : (0:ℝ≥0∞) = ∫⁻ _ : EuclideanSpace ℝ (Fin n), (0:ℝ≥0∞) ∂(GaussMeasure n) := by simp
      rw [hz]
      refine tendsto_lintegral_of_dominated_convergence'
        (fun x => ((2:ℝ≥0∞) * ‖(GaussD u : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) x‖ₑ) ^ (2:ℝ≥0∞).toReal) ?_ ?_ ?_ ?_
      · intro k
        have hc : Continuous (fun t : ℝ => t / Real.sqrt (t ^ 2 + (1 / ((k:ℝ) + 1)) ^ 2)) := by
          refine Continuous.div continuous_id (by fun_prop) (fun t => ?_)
          exact (Real.sqrt_pos.2 (by positivity)).ne'
        have hm : AEStronglyMeasurable (fun x => ((u : EuclideanSpace ℝ (Fin n) → ℝ) x
            / Real.sqrt ((u : EuclideanSpace ℝ (Fin n) → ℝ) x ^ 2 + (1 / ((k:ℝ) + 1)) ^ 2)) • (GaussD u : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) x
              - Set.indicator (Um ⁻¹' Set.Ioi (0:ℝ)) (GaussD u : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) x) (GaussMeasure n) :=
          ((hc.comp_aestronglyMeasurable hUm).smul hGL2.aestronglyMeasurable).sub
            (hGL2.aestronglyMeasurable.indicator hS)
        exact (hm.enorm).pow_const _
      · intro k
        refine Filter.Eventually.of_forall fun x => ?_
        refine ENNReal.rpow_le_rpow ?_ (by norm_num)
        calc ‖((u : EuclideanSpace ℝ (Fin n) → ℝ) x / Real.sqrt ((u : EuclideanSpace ℝ (Fin n) → ℝ) x ^ 2 + (1 / ((k:ℝ) + 1)) ^ 2)) • (GaussD u : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) x
                - Set.indicator (Um ⁻¹' Set.Ioi (0:ℝ)) (GaussD u : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) x‖ₑ
            = ENNReal.ofReal ‖((u : EuclideanSpace ℝ (Fin n) → ℝ) x
                / Real.sqrt ((u : EuclideanSpace ℝ (Fin n) → ℝ) x ^ 2 + (1 / ((k:ℝ) + 1)) ^ 2)) • (GaussD u : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) x
                  - Set.indicator (Um ⁻¹' Set.Ioi (0:ℝ)) (GaussD u : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) x‖ := (ofReal_norm _).symm
          _ ≤ ENNReal.ofReal (2 * ‖(GaussD u : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) x‖) := ENNReal.ofReal_le_ofReal (hreal k x)
          _ = (2:ℝ≥0∞) * ‖(GaussD u : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) x‖ₑ := by
              rw [ENNReal.ofReal_mul (by norm_num), ofReal_norm]
              norm_num
      · have heq : ∀ x : EuclideanSpace ℝ (Fin n), ((2:ℝ≥0∞) * ‖(GaussD u : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) x‖ₑ) ^ (2:ℝ≥0∞).toReal
            = (2:ℝ≥0∞) ^ (2:ℝ≥0∞).toReal * ‖(GaussD u : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) x‖ₑ ^ (2:ℝ≥0∞).toReal :=
          fun x => ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)
        rw [lintegral_congr heq,
          lintegral_const_mul' _ _ (ENNReal.rpow_ne_top_of_nonneg (by norm_num) (by norm_num))]
        exact ENNReal.mul_ne_top
          (ENNReal.rpow_ne_top_of_nonneg (by norm_num) (by norm_num)) hfin
      · filter_upwards [hΘlim] with x hx
        have h1 : Filter.Tendsto (fun k : ℕ =>
            ((u : EuclideanSpace ℝ (Fin n) → ℝ) x / Real.sqrt ((u : EuclideanSpace ℝ (Fin n) → ℝ) x ^ 2 + (1 / ((k:ℝ) + 1)) ^ 2)) • (GaussD u : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) x
              - Set.indicator (Um ⁻¹' Set.Ioi (0:ℝ)) (GaussD u : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) x) Filter.atTop (nhds 0) := by
          have h := hx.sub_const (Set.indicator (Um ⁻¹' Set.Ioi (0:ℝ)) (GaussD u : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) x)
          simpa using h
        have h2 : Filter.Tendsto (fun k : ℕ =>
            ‖((u : EuclideanSpace ℝ (Fin n) → ℝ) x / Real.sqrt ((u : EuclideanSpace ℝ (Fin n) → ℝ) x ^ 2 + (1 / ((k:ℝ) + 1)) ^ 2)) • (GaussD u : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) x
              - Set.indicator (Um ⁻¹' Set.Ioi (0:ℝ)) (GaussD u : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) x‖ₑ) Filter.atTop (nhds 0) := by
          have h := h1.enorm
          simpa using h
        have h3 := ((ENNReal.continuous_rpow_const
          (y := (2:ℝ≥0∞).toReal)).tendsto (0:ℝ≥0∞)).comp h2
        rw [ENNReal.zero_rpow_of_pos (by norm_num)] at h3
        simpa [Function.comp_def] using h3
    have hrp := (ENNReal.continuous_rpow_const
      (y := 1 / (2:ℝ≥0∞).toReal)).tendsto (0:ℝ≥0∞) |>.comp hL
    have hz0 : ((0:ℝ≥0∞)) ^ (1 / (2:ℝ≥0∞).toReal) = 0 :=
      ENNReal.zero_rpow_of_pos (by norm_num)
    rw [hz0] at hrp
    have hconv : Filter.Tendsto (fun k : ℕ => (eLpNorm (fun x =>
          ((u : EuclideanSpace ℝ (Fin n) → ℝ) x / Real.sqrt ((u : EuclideanSpace ℝ (Fin n) → ℝ) x ^ 2 + (1 / ((k:ℝ) + 1)) ^ 2)) • (GaussD u : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) x
            - Set.indicator (Um ⁻¹' Set.Ioi (0:ℝ)) (GaussD u : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) x) 2 (GaussMeasure n)))
        Filter.atTop (nhds 0) := by
      have hre : ∀ k : ℕ, eLpNorm (fun x =>
            ((u : EuclideanSpace ℝ (Fin n) → ℝ) x / Real.sqrt ((u : EuclideanSpace ℝ (Fin n) → ℝ) x ^ 2 + (1 / ((k:ℝ) + 1)) ^ 2)) • (GaussD u : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) x
              - Set.indicator (Um ⁻¹' Set.Ioi (0:ℝ)) (GaussD u : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) x) 2 (GaussMeasure n)
          = (∫⁻ x, ‖((u : EuclideanSpace ℝ (Fin n) → ℝ) x / Real.sqrt ((u : EuclideanSpace ℝ (Fin n) → ℝ) x ^ 2 + (1 / ((k:ℝ) + 1)) ^ 2)) • (GaussD u : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) x
              - Set.indicator (Um ⁻¹' Set.Ioi (0:ℝ)) (GaussD u : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) x‖ₑ ^ (2:ℝ≥0∞).toReal
              ∂(GaussMeasure n)) ^ (1 / (2:ℝ≥0∞).toReal) :=
        fun k => eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)
          ((((show Continuous (fun t : ℝ => t / Real.sqrt (t ^ 2 + (1 / ((k:ℝ) + 1)) ^ 2)) from
            Continuous.div continuous_id (by fun_prop)
              (fun t => (Real.sqrt_pos.2 (by positivity)).ne')).comp_aestronglyMeasurable hUm).smul
            hGL2.aestronglyMeasurable).sub (hGL2.aestronglyMeasurable.indicator hS))
      rw [show (fun k : ℕ => eLpNorm (fun x =>
            ((u : EuclideanSpace ℝ (Fin n) → ℝ) x / Real.sqrt ((u : EuclideanSpace ℝ (Fin n) → ℝ) x ^ 2 + (1 / ((k:ℝ) + 1)) ^ 2)) • (GaussD u : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) x
              - Set.indicator (Um ⁻¹' Set.Ioi (0:ℝ)) (GaussD u : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) x) 2 (GaussMeasure n)) = _
          from funext hre]
      simpa [Function.comp_def] using hrp
    simpa [Function.comp_def] using
      (ENNReal.tendsto_toReal (by simp : (0:ℝ≥0∞) ≠ ⊤)).comp hconv
  -- (7) Step 3: closedness of the weak gradient
  have hspec : ∀ z : Lp ℝ 2 (GaussMeasure n), z ∈ SobolevW12 n →
      HasGaussWeakGrad (z : EuclideanSpace ℝ (Fin n) → ℝ)
        (((Real.sqrt 2 • GaussD z : Lp (EuclideanSpace ℝ (Fin n)) 2 (GaussMeasure n)) : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))) := by
    intro z hz
    obtain ⟨Γ, hΓ⟩ := hz
    have hid := (GaussDWitness z Γ hΓ).2
    rw [← hid] at hΓ
    exact GaussWeakGradAECongr _ _ _ _ Filter.EventuallyEq.rfl
      (Lp.coeFn_smul (Real.sqrt 2) (GaussD z)).symm hΓ
  have hclosed : HasGaussWeakGrad (u : EuclideanSpace ℝ (Fin n) → ℝ)
      (((Real.sqrt 2 • (hPmem.toLp _ : Lp (EuclideanSpace ℝ (Fin n)) 2 (GaussMeasure n))
        : Lp (EuclideanSpace ℝ (Fin n)) 2 (GaussMeasure n)) : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))) := by
    refine GaussWeakGradClosed u (Real.sqrt 2 • (hPmem.toLp _))
      (fun k => ((hwmem k).toLp _ : Lp ℝ 2 (GaussMeasure n)))
      (fun k => Real.sqrt 2 • GaussD ((hwmem k).toLp _ : Lp ℝ 2 (GaussMeasure n)))
      (fun k => hspec _ (hCR k).1) hstep1 (hstep2.const_smul (Real.sqrt 2))
  -- (8) Step 4: identify the limit field with `Du`
  have hGDeq : GaussD u = (hPmem.toLp _ : Lp (EuclideanSpace ℝ (Fin n)) 2 (GaussMeasure n)) := by
    refine (GaussDWitness u (hPmem.toLp _) ?_).2
    refine GaussWeakGradAECongr _ _ _ _ Filter.EventuallyEq.rfl ?_ hclosed
    exact Lp.coeFn_smul (Real.sqrt 2) (hPmem.toLp _ : Lp (EuclideanSpace ℝ (Fin n)) 2 (GaussMeasure n))
  -- (9) conclusion
  have hGfP : (GaussD u : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) =ᵐ[GaussMeasure n] Set.indicator (Um ⁻¹' Set.Ioi (0:ℝ)) (GaussD u : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) := by
    have h := hPlcoe
    rw [← hGDeq] at h
    exact h
  filter_upwards [hu0', hUmae, hGfP] with x hx0 hxm hxP
  intro hxle
  have hx0' : (u : EuclideanSpace ℝ (Fin n) → ℝ) x = 0 := le_antisymm hxle hx0
  have hnm : x ∉ Um ⁻¹' Set.Ioi (0:ℝ) := by
    simp only [Set.mem_preimage, Set.mem_Ioi, ← hxm, hx0']
    exact lt_irrefl 0
  rw [hxP, Set.indicator_of_notMem hnm]
