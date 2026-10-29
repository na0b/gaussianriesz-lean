module

public import GaussianRiesz.ObstacleDecomposition
public import GaussianRiesz.ToL1
public import GaussianRiesz.GaussDLinear
public import GaussianRiesz.FracPowLinear

@[expose] public section
open MeasureTheory
theorem SignedDecomposition {n : ℕ} (f : Lp ℝ 2 (GaussMeasure n)) (t : ℝ)
    (ht : ‖ToL1 f‖ < t) :
    ∃ u ∈ FracPowDomain ((1 : ℝ) / 2), ∃ g : Lp ℝ 2 (GaussMeasure n),
      ∃ Ω : Set (EuclideanSpace ℝ (Fin n)),
      MeasurableSet Ω
      ∧ f = g + FracPow ((1 : ℝ) / 2) u
      ∧ ENNReal.ofReal t * GaussMeasure n Ω ≤ ENNReal.ofReal ‖ToL1 f‖
      ∧ (∀ᵐ x ∂(GaussMeasure n), |(g : EuclideanSpace ℝ (Fin n) → ℝ) x| ≤ t)
      ∧ ‖ToL1 g‖ ≤ ‖ToL1 f‖
      ∧ ‖g‖ ^ 2 ≤ t * ‖ToL1 f‖
      ∧ (∀ᵐ x ∂(GaussMeasure n), x ∉ Ω
          → (GaussD u : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) x = 0) := by
  classical
  have hprob : IsProbabilityMeasure (GaussMeasure n) := GaussIsProb n
  have ht0 : (0 : ℝ) < t := lt_of_le_of_lt (norm_nonneg _) ht
  -- the `L¹` norm is the integral of the absolute value
  have hL1 : ∀ v : Lp ℝ 2 (GaussMeasure n),
      ‖ToL1 v‖ = ∫ x, |(v : EuclideanSpace ℝ (Fin n) → ℝ) x| ∂(GaussMeasure n) := by
    intro v
    have hc : ((ToL1 v : Lp ℝ 1 (GaussMeasure n)) : EuclideanSpace ℝ (Fin n) → ℝ)
        =ᵐ[GaussMeasure n] (v : EuclideanSpace ℝ (Fin n) → ℝ) := by
      rw [ToL1]
      exact MemLp.coeFn_toLp _
    rw [L1.norm_eq_integral_norm]
    refine integral_congr_ae ?_
    filter_upwards [hc] with x hx
    rw [hx, Real.norm_eq_abs]
  -- STEP 0: the two nonnegative parts of `f`, as `L²` elements
  have hpm : AEStronglyMeasurable
      (fun x => max ((f : EuclideanSpace ℝ (Fin n) → ℝ) x) 0) (GaussMeasure n) :=
    (Lp.aestronglyMeasurable f).sup aestronglyMeasurable_const
  have hpL : MemLp (fun x => max ((f : EuclideanSpace ℝ (Fin n) → ℝ) x) 0) 2
      (GaussMeasure n) := by
    refine MemLp.of_le (Lp.memLp f) hpm (Filter.Eventually.of_forall fun x => ?_)
    simp only [Real.norm_eq_abs]
    rw [abs_of_nonneg (le_max_right _ _)]
    exact max_le (le_abs_self _) (abs_nonneg _)
  have hmm : AEStronglyMeasurable
      (fun x => max (-((f : EuclideanSpace ℝ (Fin n) → ℝ) x)) 0) (GaussMeasure n) :=
    ((Lp.aestronglyMeasurable f).neg).sup aestronglyMeasurable_const
  have hmL : MemLp (fun x => max (-((f : EuclideanSpace ℝ (Fin n) → ℝ) x)) 0) 2
      (GaussMeasure n) := by
    refine MemLp.of_le (Lp.memLp f) hmm (Filter.Eventually.of_forall fun x => ?_)
    simp only [Real.norm_eq_abs]
    rw [abs_of_nonneg (le_max_right _ _)]
    exact max_le (neg_le_abs _) (abs_nonneg _)
  set fp : Lp ℝ 2 (GaussMeasure n) := hpL.toLp _ with hfpdef
  set fm : Lp ℝ 2 (GaussMeasure n) := hmL.toLp _ with hfmdef
  have hfpc : (fp : EuclideanSpace ℝ (Fin n) → ℝ)
      =ᵐ[GaussMeasure n] fun x => max ((f : EuclideanSpace ℝ (Fin n) → ℝ) x) 0 :=
    hpL.coeFn_toLp
  have hfmc : (fm : EuclideanSpace ℝ (Fin n) → ℝ)
      =ᵐ[GaussMeasure n] fun x => max (-((f : EuclideanSpace ℝ (Fin n) → ℝ) x)) 0 :=
    hmL.coeFn_toLp
  have hfpnn : 0 ≤ᵐ[GaussMeasure n] (fp : EuclideanSpace ℝ (Fin n) → ℝ) := by
    filter_upwards [hfpc] with x hx
    rw [hx]
    exact le_max_right _ _
  have hfmnn : 0 ≤ᵐ[GaussMeasure n] (fm : EuclideanSpace ℝ (Fin n) → ℝ) := by
    filter_upwards [hfmc] with x hx
    rw [hx]
    exact le_max_right _ _
  -- `f = f⁺ - f⁻` in `L²`
  have hfeq : f = fp - fm := by
    refine Lp.ext ?_
    filter_upwards [hfpc, hfmc, Lp.coeFn_sub fp fm] with x h1 h2 h3
    rw [h3, Pi.sub_apply, h1, h2]
    rcases le_or_gt ((f : EuclideanSpace ℝ (Fin n) → ℝ) x) 0 with h | h
    · rw [max_eq_right h, max_eq_left (by linarith)]; ring
    · rw [max_eq_left (le_of_lt h), max_eq_right (by linarith)]; ring
  -- the two masses, and `m₊ + m₋ = ‖f‖₁`
  set mp : ℝ := ∫ x, (fp : EuclideanSpace ℝ (Fin n) → ℝ) x ∂(GaussMeasure n) with hmpdef
  set mq : ℝ := ∫ x, (fm : EuclideanSpace ℝ (Fin n) → ℝ) x ∂(GaussMeasure n) with hmqdef
  have hfpint : Integrable (fp : EuclideanSpace ℝ (Fin n) → ℝ) (GaussMeasure n) :=
    (Lp.memLp fp).integrable (by norm_num)
  have hfmint : Integrable (fm : EuclideanSpace ℝ (Fin n) → ℝ) (GaussMeasure n) :=
    (Lp.memLp fm).integrable (by norm_num)
  have hmpnn : (0 : ℝ) ≤ mp := integral_nonneg_of_ae hfpnn
  have hmqnn : (0 : ℝ) ≤ mq := integral_nonneg_of_ae hfmnn
  have hsum : mp + mq = ‖ToL1 f‖ := by
    rw [hmpdef, hmqdef, ← integral_add hfpint hfmint, hL1 f]
    refine integral_congr_ae ?_
    filter_upwards [hfpc, hfmc] with x h1 h2
    rw [h1, h2]
    rcases le_or_gt ((f : EuclideanSpace ℝ (Fin n) → ℝ) x) 0 with h | h
    · rw [max_eq_right h, max_eq_left (by linarith), abs_of_nonpos h]; ring
    · rw [max_eq_left (le_of_lt h), max_eq_right (by linarith), abs_of_pos h]; ring
  have hmpt : mp < t := by linarith [hsum, ht]
  have hmqt : mq < t := by linarith [hsum, ht]
  -- STEP 1: two applications of the obstacle decomposition at height `a = t`
  obtain ⟨up, hupdom, gp, -, hfpeq, hgpbd, hgpint, -, hOmp, hlocp, -, -, -⟩ :=
    ObstacleDecomposition fp hfpnn mp t hmpdef hmpt
  obtain ⟨um, humdom, gm, -, hfmeq, hgmbd, hgmint, -, hOmq, hlocm, -, -, -⟩ :=
    ObstacleDecomposition fm hfmnn mq t hmqdef hmqt
  -- `0 ≤ g± ≤ t` almost everywhere
  have hgpnn : ∀ᵐ x ∂(GaussMeasure n), 0 ≤ (gp : EuclideanSpace ℝ (Fin n) → ℝ) x
      ∧ (gp : EuclideanSpace ℝ (Fin n) → ℝ) x ≤ t := by
    filter_upwards [hgpbd, hfpnn] with x h1 h2
    simp only [Pi.zero_apply] at h2
    exact ⟨le_trans (le_min h2 ht0.le) h1.1, h1.2⟩
  have hgmnn : ∀ᵐ x ∂(GaussMeasure n), 0 ≤ (gm : EuclideanSpace ℝ (Fin n) → ℝ) x
      ∧ (gm : EuclideanSpace ℝ (Fin n) → ℝ) x ≤ t := by
    filter_upwards [hgmbd, hfmnn] with x h1 h2
    simp only [Pi.zero_apply] at h2
    exact ⟨le_trans (le_min h2 ht0.le) h1.1, h1.2⟩
  -- STEP 2: the signed objects
  obtain ⟨-, hFPadd, hFPsmul⟩ := FracPowLinear ((1 : ℝ) / 2) (n := n)
  obtain ⟨hnegdom, hnegval⟩ := hFPsmul (-1 : ℝ) um humdom
  obtain ⟨hudom, huval⟩ := hFPadd up ((-1 : ℝ) • um) hupdom hnegdom
  have hmeasp : MeasurableSet {x | 0 < (up : EuclideanSpace ℝ (Fin n) → ℝ) x} :=
    measurableSet_lt measurable_const (Lp.stronglyMeasurable up).measurable
  have hmeasq : MeasurableSet {x | 0 < (um : EuclideanSpace ℝ (Fin n) → ℝ) x} :=
    measurableSet_lt measurable_const (Lp.stronglyMeasurable um).measurable
  have hgc : ((gp - gm : Lp ℝ 2 (GaussMeasure n)) : EuclideanSpace ℝ (Fin n) → ℝ)
      =ᵐ[GaussMeasure n] fun x => (gp : EuclideanSpace ℝ (Fin n) → ℝ) x
        - (gm : EuclideanSpace ℝ (Fin n) → ℝ) x := Lp.coeFn_sub gp gm
  refine ⟨up + (-1 : ℝ) • um, hudom, gp - gm,
    {x | 0 < (up : EuclideanSpace ℝ (Fin n) → ℝ) x}
      ∪ {x | 0 < (um : EuclideanSpace ℝ (Fin n) → ℝ) x},
    hmeasp.union hmeasq, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- the decomposition identity
    rw [hfeq, hfpeq, hfmeq, huval, hnegval, neg_smul, one_smul]
    abel
  · -- STEP 3: the measure of `Ω`
    calc ENNReal.ofReal t * GaussMeasure n
            ({x | 0 < (up : EuclideanSpace ℝ (Fin n) → ℝ) x}
              ∪ {x | 0 < (um : EuclideanSpace ℝ (Fin n) → ℝ) x})
        ≤ ENNReal.ofReal t * (GaussMeasure n {x | 0 < (up : EuclideanSpace ℝ (Fin n) → ℝ) x}
            + GaussMeasure n {x | 0 < (um : EuclideanSpace ℝ (Fin n) → ℝ) x}) := by
          gcongr
          exact measure_union_le _ _
      _ = ENNReal.ofReal t * GaussMeasure n {x | 0 < (up : EuclideanSpace ℝ (Fin n) → ℝ) x}
            + ENNReal.ofReal t
              * GaussMeasure n {x | 0 < (um : EuclideanSpace ℝ (Fin n) → ℝ) x} :=
          mul_add _ _ _
      _ ≤ ENNReal.ofReal mp + ENNReal.ofReal mq := add_le_add hOmp hOmq
      _ = ENNReal.ofReal (mp + mq) := (ENNReal.ofReal_add hmpnn hmqnn).symm
      _ = ENNReal.ofReal ‖ToL1 f‖ := by rw [hsum]
  · -- STEP 4: the sup bound, `|g| ≤ t` and not `2t`
    filter_upwards [hgc, hgpnn, hgmnn] with x hx h1 h2
    rw [hx]
    exact abs_le.mpr ⟨by linarith [h1.1, h2.2], by linarith [h1.2, h2.1]⟩
  · -- STEP 5: the `L¹` bound
    rw [hL1, hL1]
    have hint1 : Integrable (fun x =>
        |((gp - gm : Lp ℝ 2 (GaussMeasure n)) : EuclideanSpace ℝ (Fin n) → ℝ) x|)
        (GaussMeasure n) :=
      ((Lp.memLp (gp - gm)).integrable (by norm_num)).abs
    have hint2 : Integrable (fun x => (gp : EuclideanSpace ℝ (Fin n) → ℝ) x
        + (gm : EuclideanSpace ℝ (Fin n) → ℝ) x) (GaussMeasure n) :=
      ((Lp.memLp gp).integrable (by norm_num)).add ((Lp.memLp gm).integrable (by norm_num))
    have hle : ∫ x, |((gp - gm : Lp ℝ 2 (GaussMeasure n))
            : EuclideanSpace ℝ (Fin n) → ℝ) x| ∂(GaussMeasure n)
        ≤ ∫ x, (gp : EuclideanSpace ℝ (Fin n) → ℝ) x
            + (gm : EuclideanSpace ℝ (Fin n) → ℝ) x ∂(GaussMeasure n) := by
      refine integral_mono_ae hint1 hint2 ?_
      filter_upwards [hgc, hgpnn, hgmnn] with x hx h1 h2
      rw [hx]
      exact abs_le.mpr ⟨by linarith [h1.1, h2.1], by linarith [h1.1, h2.1]⟩
    have heq : ∫ x, (gp : EuclideanSpace ℝ (Fin n) → ℝ) x
        + (gm : EuclideanSpace ℝ (Fin n) → ℝ) x ∂(GaussMeasure n) = mp + mq := by
      rw [integral_add ((Lp.memLp gp).integrable (by norm_num))
        ((Lp.memLp gm).integrable (by norm_num)), hgpint, hgmint]
    rw [hsum] at heq
    rw [← hL1 f]
    linarith [hle, heq]
  · -- STEP 6: the `L²` bound
    have habs : ∀ᵐ x ∂(GaussMeasure n),
        |((gp - gm : Lp ℝ 2 (GaussMeasure n)) : EuclideanSpace ℝ (Fin n) → ℝ) x| ≤ t := by
      filter_upwards [hgc, hgpnn, hgmnn] with x hx h1 h2
      rw [hx]
      exact abs_le.mpr ⟨by linarith [h1.1, h2.2], by linarith [h1.2, h2.1]⟩
    have hsq : ‖(gp - gm : Lp ℝ 2 (GaussMeasure n))‖ ^ 2
        = ∫ x, ((gp - gm : Lp ℝ 2 (GaussMeasure n)) : EuclideanSpace ℝ (Fin n) → ℝ) x
            * ((gp - gm : Lp ℝ 2 (GaussMeasure n))
              : EuclideanSpace ℝ (Fin n) → ℝ) x ∂(GaussMeasure n) := by
      rw [← real_inner_self_eq_norm_sq, L2.inner_def]
      refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      simp [sq]
    have hint1 : Integrable (fun x =>
        ((gp - gm : Lp ℝ 2 (GaussMeasure n)) : EuclideanSpace ℝ (Fin n) → ℝ) x
          * ((gp - gm : Lp ℝ 2 (GaussMeasure n)) : EuclideanSpace ℝ (Fin n) → ℝ) x)
        (GaussMeasure n) := (Lp.memLp (gp - gm)).integrable_mul (Lp.memLp (gp - gm))
    have hint2 : Integrable (fun x => t
        * |((gp - gm : Lp ℝ 2 (GaussMeasure n)) : EuclideanSpace ℝ (Fin n) → ℝ) x|)
        (GaussMeasure n) :=
      (((Lp.memLp (gp - gm)).integrable (by norm_num)).abs).const_mul t
    have hmono : ∫ x, ((gp - gm : Lp ℝ 2 (GaussMeasure n))
            : EuclideanSpace ℝ (Fin n) → ℝ) x
          * ((gp - gm : Lp ℝ 2 (GaussMeasure n))
            : EuclideanSpace ℝ (Fin n) → ℝ) x ∂(GaussMeasure n)
        ≤ ∫ x, t * |((gp - gm : Lp ℝ 2 (GaussMeasure n))
            : EuclideanSpace ℝ (Fin n) → ℝ) x| ∂(GaussMeasure n) := by
      refine integral_mono_ae hint1 hint2 ?_
      filter_upwards [habs] with x hx
      nlinarith [abs_nonneg (((gp - gm : Lp ℝ 2 (GaussMeasure n))
        : EuclideanSpace ℝ (Fin n) → ℝ) x),
        sq_abs (((gp - gm : Lp ℝ 2 (GaussMeasure n))
          : EuclideanSpace ℝ (Fin n) → ℝ) x), hx]
    -- the `L¹` bound again, to finish
    have hgL1 : ∫ x, |((gp - gm : Lp ℝ 2 (GaussMeasure n))
            : EuclideanSpace ℝ (Fin n) → ℝ) x| ∂(GaussMeasure n) ≤ ‖ToL1 f‖ := by
      have hint1' : Integrable (fun x =>
          |((gp - gm : Lp ℝ 2 (GaussMeasure n)) : EuclideanSpace ℝ (Fin n) → ℝ) x|)
          (GaussMeasure n) :=
        ((Lp.memLp (gp - gm)).integrable (by norm_num)).abs
      have hint2' : Integrable (fun x => (gp : EuclideanSpace ℝ (Fin n) → ℝ) x
          + (gm : EuclideanSpace ℝ (Fin n) → ℝ) x) (GaussMeasure n) :=
        ((Lp.memLp gp).integrable (by norm_num)).add ((Lp.memLp gm).integrable (by norm_num))
      have hle' := integral_mono_ae hint1' hint2' (by
        filter_upwards [hgc, hgpnn, hgmnn] with x hx h1 h2
        rw [hx]
        exact abs_le.mpr ⟨by linarith [h1.1, h2.1], by linarith [h1.1, h2.1]⟩)
      have heq' : ∫ x, (gp : EuclideanSpace ℝ (Fin n) → ℝ) x
          + (gm : EuclideanSpace ℝ (Fin n) → ℝ) x ∂(GaussMeasure n) = mp + mq := by
        rw [integral_add ((Lp.memLp gp).integrable (by norm_num))
          ((Lp.memLp gm).integrable (by norm_num)), hgpint, hgmint]
      rw [hsum] at heq'
      linarith [hle', heq']
    rw [integral_const_mul] at hmono
    rw [hsq]
    calc ∫ x, ((gp - gm : Lp ℝ 2 (GaussMeasure n)) : EuclideanSpace ℝ (Fin n) → ℝ) x
          * ((gp - gm : Lp ℝ 2 (GaussMeasure n))
            : EuclideanSpace ℝ (Fin n) → ℝ) x ∂(GaussMeasure n)
        ≤ t * ∫ x, |((gp - gm : Lp ℝ 2 (GaussMeasure n))
            : EuclideanSpace ℝ (Fin n) → ℝ) x| ∂(GaussMeasure n) := hmono
      _ ≤ t * ‖ToL1 f‖ := mul_le_mul_of_nonneg_left hgL1 ht0.le
  · -- STEP 7: locality of the signed gradient
    obtain ⟨hGDadd, hGDsmul, -⟩ := GaussDLinear (n := n)
    have hupS : up ∈ SobolevW12 n := (SqrtDomainSobolev up hupdom).1
    have humS : um ∈ SobolevW12 n := (SqrtDomainSobolev um humdom).1
    obtain ⟨hnegS, hnegGD⟩ := hGDsmul (-1 : ℝ) um humS
    obtain ⟨-, huGD⟩ := hGDadd up ((-1 : ℝ) • um) hupS hnegS
    rw [huGD, hnegGD]
    filter_upwards [hlocp, hlocm,
      Lp.coeFn_add (GaussD up) ((-1 : ℝ) • GaussD um),
      Lp.coeFn_smul (-1 : ℝ) (GaussD um)] with x h1 h2 h3 h4
    intro hx
    have hp : (up : EuclideanSpace ℝ (Fin n) → ℝ) x ≤ 0 := by
      by_contra hc
      exact hx (Or.inl (not_le.mp hc))
    have hq : (um : EuclideanSpace ℝ (Fin n) → ℝ) x ≤ 0 := by
      by_contra hc
      exact hx (Or.inr (not_le.mp hc))
    rw [h3, Pi.add_apply, h4, Pi.smul_apply, h1 hp, h2 hq]
    simp
