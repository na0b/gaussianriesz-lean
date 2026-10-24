import GaussianRiesz.MainBound
import GaussianRiesz.FracPowLinear
import Mathlib.Topology.Algebra.InfiniteSum.Real
import GaussianRiesz.RieszTransformLinear
import GaussianRiesz.L1ApproxByL2Truncations
open MeasureTheory
theorem RieszL1Limit {n : ℕ} (f : Lp ℝ 1 (GaussMeasure n)) :
    ∃ (g : EuclideanSpace ℝ (Fin n) →ₘ[GaussMeasure n] EuclideanSpace ℝ (Fin n))
      (v : ℕ → Lp ℝ 2 (GaussMeasure n)),
      (∀ k, ‖ToL1 (v k)‖ ≤ ‖f‖)
      ∧ Filter.Tendsto (fun k => ToL1 (v k)) Filter.atTop (nhds f)
      ∧ (∀ᵐ x ∂(GaussMeasure n), Filter.Tendsto
          (fun k => (RieszTransform (v k) : EuclideanSpace ℝ (Fin n)
            → EuclideanSpace ℝ (Fin n)) x) Filter.atTop
          (nhds ((g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) x)))
      ∧ ∀ w : ℕ → Lp ℝ 2 (GaussMeasure n),
          Filter.Tendsto (fun k => ToL1 (w k)) Filter.atTop (nhds f) →
          TendstoInMeasure (GaussMeasure n)
            (fun k => (RieszTransform (w k) : EuclideanSpace ℝ (Fin n)
              → EuclideanSpace ℝ (Fin n)))
            Filter.atTop (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) := by
  classical
  have hprob : IsProbabilityMeasure (GaussMeasure n) := GaussIsProb n
  obtain ⟨hRadd, hRsmul⟩ := RieszTransformLinear (n := n)
  have hRsub : ∀ v w : Lp ℝ 2 (GaussMeasure n),
      RieszTransform (v - w) = RieszTransform v - RieszTransform w := by
    intro v w
    rw [show v - w = v + (-1 : ℝ) • w by rw [neg_smul, one_smul]; abel,
      hRadd, hRsmul, neg_smul, one_smul]
    abel
  -- the inclusion `ι : L² → L¹` is additive
  have hT1sub : ∀ v w : Lp ℝ 2 (GaussMeasure n),
      ToL1 (v - w) = ToL1 v - ToL1 w := by
    intro v w
    refine Lp.ext ?_
    have h1 : ((ToL1 (v - w) : Lp ℝ 1 (GaussMeasure n))
        : EuclideanSpace ℝ (Fin n) → ℝ)
        =ᵐ[GaussMeasure n] ((v - w : Lp ℝ 2 (GaussMeasure n))
          : EuclideanSpace ℝ (Fin n) → ℝ) := by
      rw [ToL1]; exact MemLp.coeFn_toLp _
    have h2 : ((ToL1 v : Lp ℝ 1 (GaussMeasure n)) : EuclideanSpace ℝ (Fin n) → ℝ)
        =ᵐ[GaussMeasure n] (v : EuclideanSpace ℝ (Fin n) → ℝ) := by
      rw [ToL1]; exact MemLp.coeFn_toLp _
    have h3 : ((ToL1 w : Lp ℝ 1 (GaussMeasure n)) : EuclideanSpace ℝ (Fin n) → ℝ)
        =ᵐ[GaussMeasure n] (w : EuclideanSpace ℝ (Fin n) → ℝ) := by
      rw [ToL1]; exact MemLp.coeFn_toLp _
    filter_upwards [h1, h2, h3, Lp.coeFn_sub v w,
      Lp.coeFn_sub (ToL1 v) (ToL1 w)] with x e1 e2 e3 e4 e5
    rw [e1, e5, Pi.sub_apply, e2, e3, e4, Pi.sub_apply]
  -- PART B: the Cauchy-in-measure estimate, in divided form
  have hstep0 : ∀ (v w : Lp ℝ 2 (GaussMeasure n)) (ε : ℝ), 0 < ε →
      GaussMeasure n {x | ε ≤ ‖(RieszTransform v : EuclideanSpace ℝ (Fin n)
          → EuclideanSpace ℝ (Fin n)) x
        - (RieszTransform w : EuclideanSpace ℝ (Fin n)
          → EuclideanSpace ℝ (Fin n)) x‖}
        ≤ ENNReal.ofReal (4 * ‖ToL1 v - ToL1 w‖ / ε) := by
    intro v w ε hε
    set S : Set (EuclideanSpace ℝ (Fin n)) :=
      {x | ε ≤ ‖(RieszTransform v : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) x
        - (RieszTransform w : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) x‖}
      with hSdef
    set N : ℝ := ‖ToL1 v - ToL1 w‖ with hNdef
    have hmb := MainBound (v - w) (ε / 2) (by positivity)
    rw [hRsub, hT1sub] at hmb
    have hsub : GaussMeasure n S
        ≤ GaussMeasure n {x | ε / 2 < ‖((RieszTransform v - RieszTransform w
            : Lp (EuclideanSpace ℝ (Fin n)) 2 (GaussMeasure n))
              : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) x‖} := by
      refine measure_mono_ae ?_
      filter_upwards [Lp.coeFn_sub (RieszTransform v) (RieszTransform w)] with x hx
      intro hmem
      have hmem' : ε ≤ ‖(RieszTransform v : EuclideanSpace ℝ (Fin n)
          → EuclideanSpace ℝ (Fin n)) x
        - (RieszTransform w : EuclideanSpace ℝ (Fin n)
          → EuclideanSpace ℝ (Fin n)) x‖ := hmem
      show ε / 2 < ‖((RieszTransform v - RieszTransform w
        : Lp (EuclideanSpace ℝ (Fin n)) 2 (GaussMeasure n))
          : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) x‖
      rw [hx, Pi.sub_apply]
      linarith
    have hkey : ENNReal.ofReal (ε / 2) * GaussMeasure n S
        ≤ ENNReal.ofReal (2 * N) := le_trans (by gcongr) hmb
    have hkey' : GaussMeasure n S * ENNReal.ofReal (ε / 2)
        ≤ ENNReal.ofReal (2 * N) := by rwa [mul_comm] at hkey
    have hne0 : ENNReal.ofReal (ε / 2) ≠ 0 := by
      simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]
      positivity
    have hdiv : GaussMeasure n S ≤ ENNReal.ofReal (2 * N) / ENNReal.ofReal (ε / 2) :=
      (ENNReal.le_div_iff_mul_le (Or.inl hne0) (Or.inl ENNReal.ofReal_ne_top)).mpr hkey'
    refine le_trans hdiv (le_of_eq ?_)
    rw [← ENNReal.ofReal_div_of_pos (by positivity)]
    congr 1
    field_simp
    ring
  -- PART D: the rapidly converging subsequence
  obtain ⟨v, hvn, hvc⟩ := L1ApproxByL2Truncations f
  have hvcn : Filter.Tendsto (fun k => ‖ToL1 (v k) - f‖) Filter.atTop (nhds 0) := by
    have h := (hvc.sub (tendsto_const_nhds (x := f) (f := Filter.atTop))).norm
    simpa using h
  have hchoice : ∀ j : ℕ, ∃ k : ℕ, ‖ToL1 (v k) - f‖ ≤ (1 / 8 : ℝ) ^ j / 2 := by
    intro j
    have hpos : (0 : ℝ) < (1 / 8 : ℝ) ^ j / 2 := by positivity
    obtain ⟨k, hk⟩ := (hvcn.eventually_lt_const hpos).exists
    exact ⟨k, hk.le⟩
  choose σ hσ using hchoice
  set u : ℕ → Lp ℝ 2 (GaussMeasure n) := fun j => v (σ j) with hudef
  have hun : ∀ k, ‖ToL1 (u k)‖ ≤ ‖f‖ := fun k => hvn (σ k)
  have hucn : Filter.Tendsto (fun j => ‖ToL1 (u j) - f‖) Filter.atTop (nhds 0) := by
    refine squeeze_zero (fun j => norm_nonneg _) (fun j => hσ j) ?_
    have h := tendsto_pow_atTop_nhds_zero_of_lt_one
      (r := (1 / 8 : ℝ)) (by norm_num) (by norm_num)
    simpa using h.div_const 2
  have huc : Filter.Tendsto (fun j => ToL1 (u j)) Filter.atTop (nhds f) := by
    have h3 := tendsto_zero_iff_norm_tendsto_zero.mpr hucn
    have h4 := h3.add (tendsto_const_nhds (x := f) (f := Filter.atTop))
    simpa using h4
  have hincr : ∀ j : ℕ, ‖ToL1 (u j) - ToL1 (u (j + 1))‖ ≤ (1 / 8 : ℝ) ^ j := by
    intro j
    have h1 := hσ j
    have h2 := hσ (j + 1)
    have hmono : (1 / 8 : ℝ) ^ (j + 1) ≤ (1 / 8 : ℝ) ^ j := by
      rw [pow_succ]
      nlinarith [pow_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 8) j]
    calc ‖ToL1 (u j) - ToL1 (u (j + 1))‖
        = ‖(ToL1 (u j) - f) - (ToL1 (u (j + 1)) - f)‖ := by congr 1; abel
      _ ≤ ‖ToL1 (u j) - f‖ + ‖ToL1 (u (j + 1)) - f‖ := norm_sub_le _ _
      _ ≤ (1 / 8 : ℝ) ^ j := by linarith
  -- PART E: Borel-Cantelli gives an almost-everywhere limit along the subsequence
  set E : ℕ → Set (EuclideanSpace ℝ (Fin n)) := fun j =>
    {x | (1 / 2 : ℝ) ^ j ≤ ‖(RieszTransform (u j) : EuclideanSpace ℝ (Fin n)
        → EuclideanSpace ℝ (Fin n)) x
      - (RieszTransform (u (j + 1)) : EuclideanSpace ℝ (Fin n)
        → EuclideanSpace ℝ (Fin n)) x‖} with hEdef
  have hE : ∀ j, GaussMeasure n (E j) ≤ ENNReal.ofReal (4 * (1 / 4 : ℝ) ^ j) := by
    intro j
    refine le_trans (hstep0 (u j) (u (j + 1)) ((1 / 2 : ℝ) ^ j) (by positivity)) ?_
    refine ENNReal.ofReal_le_ofReal ?_
    rw [div_le_iff₀ (by positivity)]
    have hkey : 4 * (1 / 4 : ℝ) ^ j * (1 / 2 : ℝ) ^ j = 4 * (1 / 8 : ℝ) ^ j := by
      rw [mul_assoc, ← mul_pow]
      norm_num
    rw [hkey]
    linarith [hincr j]
  have hsum : ∑' j, GaussMeasure n (E j) ≠ ⊤ := by
    have hgeo : Summable (fun j : ℕ => 4 * (1 / 4 : ℝ) ^ j) :=
      (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left 4
    refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum hE)
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun j => by positivity) hgeo]
    exact ENNReal.ofReal_ne_top
  have hbc : ∀ᵐ x ∂(GaussMeasure n), {j | x ∈ E j}.Finite :=
    MeasureTheory.ae_finite_setOfPred_mem hsum
  have hcauchy : ∀ᵐ x ∂(GaussMeasure n), ∃ a : EuclideanSpace ℝ (Fin n),
      Filter.Tendsto (fun j => (RieszTransform (u j) : EuclideanSpace ℝ (Fin n)
        → EuclideanSpace ℝ (Fin n)) x) Filter.atTop (nhds a) := by
    filter_upwards [hbc] with x hx
    obtain ⟨B, hB⟩ := hx.bddAbove
    have hdist : Summable (fun j => dist ((RieszTransform (u j) : EuclideanSpace ℝ (Fin n)
        → EuclideanSpace ℝ (Fin n)) x)
        ((RieszTransform (u (j + 1)) : EuclideanSpace ℝ (Fin n)
          → EuclideanSpace ℝ (Fin n)) x)) := by
      refine Summable.of_norm_bounded_eventually_nat (g := fun j => (1 / 2 : ℝ) ^ j)
        (summable_geometric_of_lt_one (by norm_num) (by norm_num)) ?_
      refine Filter.eventually_atTop.mpr ⟨B + 1, fun j hj => ?_⟩
      rw [Real.norm_eq_abs, abs_of_nonneg dist_nonneg, dist_eq_norm]
      by_contra hc
      rw [not_le] at hc
      have hmem : j ∈ {j | x ∈ E j} := hc.le
      have := hB hmem
      omega
    exact cauchySeq_tendsto_of_complete (cauchySeq_of_summable_dist hdist)
  set glim : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) := fun x =>
    if h : ∃ a : EuclideanSpace ℝ (Fin n),
        Filter.Tendsto (fun j => (RieszTransform (u j) : EuclideanSpace ℝ (Fin n)
          → EuclideanSpace ℝ (Fin n)) x) Filter.atTop (nhds a)
      then h.choose else 0 with hglimdef
  have hglim : ∀ᵐ x ∂(GaussMeasure n), Filter.Tendsto
      (fun j => (RieszTransform (u j) : EuclideanSpace ℝ (Fin n)
        → EuclideanSpace ℝ (Fin n)) x) Filter.atTop (nhds (glim x)) := by
    filter_upwards [hcauchy] with x hx
    simp only [hglimdef]
    rw [dif_pos hx]
    exact hx.choose_spec
  have hglimmeas : AEStronglyMeasurable glim (GaussMeasure n) :=
    aestronglyMeasurable_of_tendsto_ae Filter.atTop
      (fun j => Lp.aestronglyMeasurable (RieszTransform (u j))) hglim
  have hgc : ((AEEqFun.mk glim hglimmeas : EuclideanSpace ℝ (Fin n)
      →ₘ[GaussMeasure n] EuclideanSpace ℝ (Fin n))
      : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
      =ᵐ[GaussMeasure n] glim := AEEqFun.coeFn_mk _ _
  have hglim' : ∀ᵐ x ∂(GaussMeasure n), Filter.Tendsto
      (fun j => (RieszTransform (u j) : EuclideanSpace ℝ (Fin n)
        → EuclideanSpace ℝ (Fin n)) x) Filter.atTop
      (nhds (((AEEqFun.mk glim hglimmeas : EuclideanSpace ℝ (Fin n)
        →ₘ[GaussMeasure n] EuclideanSpace ℝ (Fin n))
        : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) x)) := by
    filter_upwards [hglim, hgc] with x h1 h2
    rw [h2]
    exact h1
  refine ⟨AEEqFun.mk glim hglimmeas, u, hun, huc, hglim', ?_⟩
  -- PART F: every approximating sequence has the same limit in measure
  intro w hw
  have hbase : TendstoInMeasure (GaussMeasure n)
      (fun k => (RieszTransform (u k) : EuclideanSpace ℝ (Fin n)
        → EuclideanSpace ℝ (Fin n))) Filter.atTop
      ((AEEqFun.mk glim hglimmeas : EuclideanSpace ℝ (Fin n)
        →ₘ[GaussMeasure n] EuclideanSpace ℝ (Fin n))
        : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) :=
    tendstoInMeasure_of_tendsto_ae
      (fun k => Lp.aestronglyMeasurable (RieszTransform (u k))) hglim'
  rw [tendstoInMeasure_iff_norm] at hbase ⊢
  intro ε hε
  have hdiff : Filter.Tendsto (fun k => ‖ToL1 (w k) - ToL1 (u k)‖) Filter.atTop (nhds 0) := by
    have h := (hw.sub huc).norm
    simpa using h
  have hA : Filter.Tendsto (fun k => GaussMeasure n
      {x | ε / 2 ≤ ‖(RieszTransform (w k) : EuclideanSpace ℝ (Fin n)
          → EuclideanSpace ℝ (Fin n)) x
        - (RieszTransform (u k) : EuclideanSpace ℝ (Fin n)
          → EuclideanSpace ℝ (Fin n)) x‖}) Filter.atTop (nhds 0) := by
    have hlim : Filter.Tendsto (fun k => ENNReal.ofReal
        (4 * ‖ToL1 (w k) - ToL1 (u k)‖ / (ε / 2))) Filter.atTop (nhds 0) := by
      have h : Filter.Tendsto (fun k => 4 * ‖ToL1 (w k) - ToL1 (u k)‖ / (ε / 2))
          Filter.atTop (nhds 0) := by
        have := (hdiff.const_mul (4 : ℝ)).div_const (ε / 2)
        simpa using this
      have h2 := ENNReal.tendsto_ofReal h
      simpa using h2
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le
      (g := fun _ : ℕ => (0 : ENNReal)) tendsto_const_nhds hlim (fun _ => by positivity)
      (fun k => hstep0 (w k) (u k) (ε / 2) (by positivity))
  have hB2 := hbase (ε / 2) (by positivity)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le
    (g := fun _ : ℕ => (0 : ENNReal)) tendsto_const_nhds
    (by simpa using hA.add hB2) (fun _ => by positivity) (fun k => ?_)
  refine le_trans (measure_mono ?_) (measure_union_le _ _)
  intro x hxmem
  have hx : ε ≤ ‖(RieszTransform (w k) : EuclideanSpace ℝ (Fin n)
      → EuclideanSpace ℝ (Fin n)) x
    - ((AEEqFun.mk glim hglimmeas : EuclideanSpace ℝ (Fin n)
      →ₘ[GaussMeasure n] EuclideanSpace ℝ (Fin n))
      : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) x‖ := hxmem
  by_contra hc
  simp only [Set.mem_union, not_or] at hc
  obtain ⟨hc1', hc2'⟩ := hc
  have h1 : ‖(RieszTransform (w k) : EuclideanSpace ℝ (Fin n)
      → EuclideanSpace ℝ (Fin n)) x
    - (RieszTransform (u k) : EuclideanSpace ℝ (Fin n)
      → EuclideanSpace ℝ (Fin n)) x‖ < ε / 2 := by
    by_contra hcc
    exact hc1' (not_lt.mp hcc)
  have h2 : ‖(RieszTransform (u k) : EuclideanSpace ℝ (Fin n)
      → EuclideanSpace ℝ (Fin n)) x
    - ((AEEqFun.mk glim hglimmeas : EuclideanSpace ℝ (Fin n)
      →ₘ[GaussMeasure n] EuclideanSpace ℝ (Fin n))
      : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) x‖ < ε / 2 := by
    by_contra hcc
    exact hc2' (not_lt.mp hcc)
  have htri := norm_add_le ((RieszTransform (w k) : EuclideanSpace ℝ (Fin n)
      → EuclideanSpace ℝ (Fin n)) x
    - (RieszTransform (u k) : EuclideanSpace ℝ (Fin n)
      → EuclideanSpace ℝ (Fin n)) x)
    ((RieszTransform (u k) : EuclideanSpace ℝ (Fin n)
      → EuclideanSpace ℝ (Fin n)) x
    - ((AEEqFun.mk glim hglimmeas : EuclideanSpace ℝ (Fin n)
      →ₘ[GaussMeasure n] EuclideanSpace ℝ (Fin n))
      : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) x)
  rw [sub_add_sub_cancel] at htri
  linarith
