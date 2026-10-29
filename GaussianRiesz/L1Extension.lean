module

public import GaussianRiesz.MainBound
public import GaussianRiesz.RieszL1Limit
public import GaussianRiesz.RieszTransformLinear

@[expose] public section
open MeasureTheory
theorem L1Extension {n : ℕ} :
    ∃ T : Lp ℝ 1 (GaussMeasure n) →ₗ[ℝ]
        (EuclideanSpace ℝ (Fin n) →ₘ[GaussMeasure n] EuclideanSpace ℝ (Fin n)),
      (∀ v : Lp ℝ 2 (GaussMeasure n),
          T (ToL1 v) = (RieszTransform v : EuclideanSpace ℝ (Fin n)
            →ₘ[GaussMeasure n] EuclideanSpace ℝ (Fin n)))
        ∧ ∀ (f : Lp ℝ 1 (GaussMeasure n)) (t : ℝ), 0 < t →
            ENNReal.ofReal t * GaussMeasure n {x | t < ‖T f x‖}
              ≤ ENNReal.ofReal (2 * ‖f‖) := by
  classical
  have hprob : IsProbabilityMeasure (GaussMeasure n) := GaussIsProb n
  obtain ⟨hRadd, hRsmul⟩ := RieszTransformLinear (n := n)
  -- `ι` is additive and homogeneous
  have hT1c : ∀ v : Lp ℝ 2 (GaussMeasure n),
      ((ToL1 v : Lp ℝ 1 (GaussMeasure n)) : EuclideanSpace ℝ (Fin n) → ℝ)
        =ᵐ[GaussMeasure n] (v : EuclideanSpace ℝ (Fin n) → ℝ) := by
    intro v
    rw [ToL1]
    exact MemLp.coeFn_toLp _
  have hT1add : ∀ v w : Lp ℝ 2 (GaussMeasure n),
      ToL1 (v + w) = ToL1 v + ToL1 w := by
    intro v w
    refine Lp.ext ?_
    filter_upwards [hT1c (v + w), hT1c v, hT1c w, Lp.coeFn_add v w,
      Lp.coeFn_add (ToL1 v) (ToL1 w)] with x e1 e2 e3 e4 e5
    rw [e1, e5, Pi.add_apply, e2, e3, e4, Pi.add_apply]
  have hT1smul : ∀ (c : ℝ) (v : Lp ℝ 2 (GaussMeasure n)),
      ToL1 (c • v) = c • ToL1 v := by
    intro c v
    refine Lp.ext ?_
    filter_upwards [hT1c (c • v), hT1c v, Lp.coeFn_smul c v,
      Lp.coeFn_smul c (ToL1 v)] with x e1 e2 e3 e4
    rw [e1, e4, Pi.smul_apply, e2, e3, Pi.smul_apply]
  -- the limit and the canonical approximating sequence, for every `f`
  choose G V hVn hVc hVae hVuniv using
    fun f : Lp ℝ 1 (GaussMeasure n) => RieszL1Limit f
  -- additivity of `G`
  have hGadd : ∀ f h : Lp ℝ 1 (GaussMeasure n), G (f + h) = G f + G h := by
    intro f h
    refine AEEqFun.ext ?_
    have hw : Filter.Tendsto (fun k => ToL1 (V f k + V h k)) Filter.atTop (nhds (f + h)) := by
      refine ((hVc f).add (hVc h)).congr fun k => ?_
      rw [hT1add]
    have h1 := hVuniv (f + h) (fun k => V f k + V h k) hw
    have hcf : ∀ᵐ x ∂(GaussMeasure n), ∀ k : ℕ,
        (RieszTransform (V f k + V h k) : EuclideanSpace ℝ (Fin n)
            → EuclideanSpace ℝ (Fin n)) x
          = (RieszTransform (V f k) : EuclideanSpace ℝ (Fin n)
              → EuclideanSpace ℝ (Fin n)) x
            + (RieszTransform (V h k) : EuclideanSpace ℝ (Fin n)
              → EuclideanSpace ℝ (Fin n)) x := by
      refine ae_all_iff.mpr fun k => ?_
      rw [hRadd]
      filter_upwards [Lp.coeFn_add (RieszTransform (V f k))
        (RieszTransform (V h k))] with x hx
      rw [hx, Pi.add_apply]
    have hae : ∀ᵐ x ∂(GaussMeasure n), Filter.Tendsto
        (fun k => (RieszTransform (V f k + V h k) : EuclideanSpace ℝ (Fin n)
          → EuclideanSpace ℝ (Fin n)) x) Filter.atTop
        (nhds ((G f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) x
          + (G h : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) x)) := by
      filter_upwards [hVae f, hVae h, hcf] with x e1 e2 e3
      exact (e1.add e2).congr fun k => (e3 k).symm
    have h2 : TendstoInMeasure (GaussMeasure n)
        (fun k => (RieszTransform (V f k + V h k) : EuclideanSpace ℝ (Fin n)
          → EuclideanSpace ℝ (Fin n))) Filter.atTop
        (fun x => (G f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) x
          + (G h : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) x) :=
      tendstoInMeasure_of_tendsto_ae (fun k => Lp.aestronglyMeasurable _) hae
    filter_upwards [tendstoInMeasure_ae_unique h1 h2,
      AEEqFun.coeFn_add (G f) (G h)] with x e1 e2
    rw [e1, e2, Pi.add_apply]
  -- homogeneity of `G`
  have hGsmul : ∀ (c : ℝ) (f : Lp ℝ 1 (GaussMeasure n)), G (c • f) = c • G f := by
    intro c f
    refine AEEqFun.ext ?_
    have hw : Filter.Tendsto (fun k => ToL1 (c • V f k)) Filter.atTop (nhds (c • f)) := by
      refine ((hVc f).const_smul c).congr fun k => ?_
      rw [hT1smul]
    have h1 := hVuniv (c • f) (fun k => c • V f k) hw
    have hcf : ∀ᵐ x ∂(GaussMeasure n), ∀ k : ℕ,
        (RieszTransform (c • V f k) : EuclideanSpace ℝ (Fin n)
            → EuclideanSpace ℝ (Fin n)) x
          = c • (RieszTransform (V f k) : EuclideanSpace ℝ (Fin n)
              → EuclideanSpace ℝ (Fin n)) x := by
      refine ae_all_iff.mpr fun k => ?_
      rw [hRsmul]
      filter_upwards [Lp.coeFn_smul c (RieszTransform (V f k))] with x hx
      rw [hx, Pi.smul_apply]
    have hae : ∀ᵐ x ∂(GaussMeasure n), Filter.Tendsto
        (fun k => (RieszTransform (c • V f k) : EuclideanSpace ℝ (Fin n)
          → EuclideanSpace ℝ (Fin n)) x) Filter.atTop
        (nhds (c • (G f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) x)) := by
      filter_upwards [hVae f, hcf] with x e1 e3
      exact (e1.const_smul c).congr fun k => (e3 k).symm
    have h2 : TendstoInMeasure (GaussMeasure n)
        (fun k => (RieszTransform (c • V f k) : EuclideanSpace ℝ (Fin n)
          → EuclideanSpace ℝ (Fin n))) Filter.atTop
        (fun x => c • (G f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) x) :=
      tendstoInMeasure_of_tendsto_ae (fun k => Lp.aestronglyMeasurable _) hae
    filter_upwards [tendstoInMeasure_ae_unique h1 h2,
      AEEqFun.coeFn_smul c (G f)] with x e1 e2
    rw [e1, e2, Pi.smul_apply]
  refine ⟨{ toFun := G, map_add' := hGadd, map_smul' := hGsmul }, ?_, ?_⟩
  · -- agreement with `R_γ` on `L²`, by the constant approximating sequence
    intro v
    refine AEEqFun.ext ?_
    have h1 := hVuniv (ToL1 v) (fun _ => v) tendsto_const_nhds
    have h2 : TendstoInMeasure (GaussMeasure n)
        (fun _ : ℕ => (RieszTransform v : EuclideanSpace ℝ (Fin n)
          → EuclideanSpace ℝ (Fin n))) Filter.atTop
        ((RieszTransform v : Lp (EuclideanSpace ℝ (Fin n)) 2 (GaussMeasure n))
          : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) :=
      tendstoInMeasure_of_tendsto_ae (fun _ => Lp.aestronglyMeasurable _)
        (Filter.Eventually.of_forall fun x => tendsto_const_nhds)
    exact tendstoInMeasure_ae_unique h1 h2
  · -- the weak bound, by Fatou along the canonical sequence
    intro f t ht
    set S : Set (EuclideanSpace ℝ (Fin n)) :=
      {x | t < ‖(G f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) x‖} with hSdef
    set Sk : ℕ → Set (EuclideanSpace ℝ (Fin n)) := fun k =>
      {x | t < ‖(RieszTransform (V f k) : EuclideanSpace ℝ (Fin n)
        → EuclideanSpace ℝ (Fin n)) x‖} with hSkdef
    have hmeasS : MeasurableSet S :=
      measurableSet_lt measurable_const (AEEqFun.stronglyMeasurable (G f)).measurable.norm
    have hmeasSk : ∀ k, MeasurableSet (Sk k) := fun k =>
      measurableSet_lt measurable_const
        (Lp.stronglyMeasurable (RieszTransform (V f k))).measurable.norm
    have hind : ∀ᵐ x ∂(GaussMeasure n),
        S.indicator (fun _ => (1 : ENNReal)) x
          ≤ Filter.liminf (fun k => (Sk k).indicator (fun _ => (1 : ENNReal)) x)
              Filter.atTop := by
      filter_upwards [hVae f] with x hx
      by_cases hxS : x ∈ S
      · have hlt : t < ‖(G f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) x‖ := hxS
        have hev : ∀ᶠ k in Filter.atTop,
            (1 : ENNReal) ≤ (Sk k).indicator (fun _ => (1 : ENNReal)) x := by
          filter_upwards [hx.norm.eventually_const_lt hlt] with k hk
          rw [Set.indicator_of_mem (show x ∈ Sk k from hk)]
        rw [Set.indicator_of_mem hxS]
        exact Filter.le_liminf_of_le (by isBoundedDefault) hev
      · rw [Set.indicator_of_notMem hxS]
        exact zero_le
    have hfatou : GaussMeasure n S
        ≤ Filter.liminf (fun k => GaussMeasure n (Sk k)) Filter.atTop := by
      calc GaussMeasure n S
          = ∫⁻ x, S.indicator (fun _ => (1 : ENNReal)) x ∂(GaussMeasure n) := by
            rw [lintegral_indicator_const hmeasS, one_mul]
        _ ≤ ∫⁻ x, Filter.liminf
              (fun k => (Sk k).indicator (fun _ => (1 : ENNReal)) x) Filter.atTop
              ∂(GaussMeasure n) := lintegral_mono_ae hind
        _ ≤ Filter.liminf (fun k => ∫⁻ x,
              (Sk k).indicator (fun _ => (1 : ENNReal)) x ∂(GaussMeasure n))
              Filter.atTop :=
            lintegral_liminf_le (fun k => measurable_const.indicator (hmeasSk k))
        _ = Filter.liminf (fun k => GaussMeasure n (Sk k)) Filter.atTop := by
            refine congrArg (fun u => Filter.liminf u Filter.atTop) ?_
            funext k
            rw [lintegral_indicator_const (hmeasSk k), one_mul]
    have hne0 : ENNReal.ofReal t ≠ 0 := by
      simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]
      exact ht
    have hbd : ∀ k, GaussMeasure n (Sk k)
        ≤ ENNReal.ofReal (2 * ‖f‖) / ENNReal.ofReal t := by
      intro k
      refine (ENNReal.le_div_iff_mul_le (Or.inl hne0)
        (Or.inl ENNReal.ofReal_ne_top)).mpr ?_
      rw [mul_comm]
      refine le_trans (MainBound (V f k) t ht) (ENNReal.ofReal_le_ofReal ?_)
      linarith [hVn f k]
    have hSle : GaussMeasure n S ≤ ENNReal.ofReal (2 * ‖f‖) / ENNReal.ofReal t := by
      refine le_trans hfatou ?_
      have h := Filter.liminf_le_liminf
        (f := Filter.atTop)
        (v := fun k => GaussMeasure n (Sk k))
        (u := fun _ : ℕ => ENNReal.ofReal (2 * ‖f‖) / ENNReal.ofReal t)
        (Filter.Eventually.of_forall hbd)
      rwa [Filter.liminf_const] at h
    have hfinal := (ENNReal.le_div_iff_mul_le (Or.inl hne0)
      (Or.inl ENNReal.ofReal_ne_top)).mp hSle
    rwa [mul_comm] at hfinal
