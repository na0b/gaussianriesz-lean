import GaussianRiesz.OUSemigroupSpectral
import GaussianRiesz.GaussMixPushforward
import GaussianRiesz.HermiteL2
import GaussianRiesz.OUSelfAdjointContraction
import GaussianRiesz.HermiteFunReproduction
import GaussianRiesz.HermiteL2Complete
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
open MeasureTheory
theorem MehlerFormula {n : ℕ} (s : ℝ) (hs : 0 < s) (v : Lp ℝ 2 (GaussMeasure n)) :
    (∀ᵐ x ∂(GaussMeasure n), Integrable (fun y : EuclideanSpace ℝ (Fin n) =>
          (v : EuclideanSpace ℝ (Fin n) → ℝ)
            (Real.exp (-s) • x + Real.sqrt (1 - Real.exp (-2 * s)) • y))
          (GaussMeasure n))
      ∧ (∀ᵐ x ∂(GaussMeasure n), (OUSemigroup s v : EuclideanSpace ℝ (Fin n) → ℝ) x
        = ∫ y, (v : EuclideanSpace ℝ (Fin n) → ℝ)
            (Real.exp (-s) • x + Real.sqrt (1 - Real.exp (-2 * s)) • y) ∂(GaussMeasure n))
      ∧ (0 ≤ᵐ[GaussMeasure n] (v : EuclideanSpace ℝ (Fin n) → ℝ) →
          0 ≤ᵐ[GaussMeasure n] (OUSemigroup s v : EuclideanSpace ℝ (Fin n) → ℝ)) := by
  classical
  -- (0) the exponent-two seminorm as a plain lintegral of squares
  have hES : ∀ {α : Type} [MeasurableSpace α] (μ : Measure α) (f : α → ℝ),
      eLpNorm f 2 μ = (∫⁻ x, ‖f x‖ₑ ^ 2 ∂μ) ^ ((2:ℝ)⁻¹) := by
    intro α _ μ f
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)]
    norm_num
  -- the contraction factor `r = e^{-s}` and the spreading factor `τ = √(1 - r²)`
  set a := Real.exp (-s) with ha_def
  set b := Real.sqrt (1 - Real.exp (-2 * s)) with hb_def
  have ha0 : (0:ℝ) ≤ a := (Real.exp_pos _).le
  have ha1 : a ≤ 1 := by rw [ha_def, Real.exp_le_one_iff]; linarith
  have hasq : a ^ 2 = Real.exp (-2 * s) := by
    rw [ha_def, ← Real.exp_nat_mul]; ring_nf
  have hpow : ∀ k : ℕ, a ^ k = Real.exp (-s * k) := by
    intro k
    rw [ha_def, ← Real.exp_nat_mul]; ring_nf
  have hbdef2 : b = Real.sqrt (1 - a ^ 2) := by rw [hb_def, hasq]
  have hb0 : (0:ℝ) ≤ b := Real.sqrt_nonneg _
  have ha2le : a ^ 2 ≤ 1 := by nlinarith
  have hbsq : b ^ 2 = 1 - a ^ 2 := by rw [hbdef2, Real.sq_sqrt (by linarith)]
  have hab : a ^ 2 + b ^ 2 = 1 := by rw [hbsq]; ring
  clear_value a b
  -- (3) Cauchy-Schwarz against the constant function `1`
  have l2b : ∀ g : EuclideanSpace ℝ (Fin n) → ℝ,
      AEStronglyMeasurable g (GaussMeasure n) →
      ‖∫ y, g y ∂(GaussMeasure n)‖ₑ ^ 2 ≤ ∫⁻ y, ‖g y‖ₑ ^ 2 ∂(GaussMeasure n) := by
    intro g hg
    have h1 : ‖∫ y, g y ∂(GaussMeasure n)‖ₑ
        ≤ (∫⁻ y, ‖g y‖ₑ ^ 2 ∂(GaussMeasure n)) ^ ((2:ℝ)⁻¹) := by
      calc ‖∫ y, g y ∂(GaussMeasure n)‖ₑ
          ≤ ∫⁻ y, ‖g y‖ₑ ∂(GaussMeasure n) := enorm_integral_le_lintegral_enorm g
        _ = eLpNorm g 1 (GaussMeasure n) := eLpNorm_one_eq_lintegral_enorm.symm
        _ ≤ eLpNorm g 2 (GaussMeasure n) :=
            eLpNorm_le_eLpNorm_of_exponent_le (by norm_num) hg
        _ = (∫⁻ y, ‖g y‖ₑ ^ 2 ∂(GaussMeasure n)) ^ ((2:ℝ)⁻¹) := hES (GaussMeasure n) g
    calc ‖∫ y, g y ∂(GaussMeasure n)‖ₑ ^ 2
        ≤ ((∫⁻ y, ‖g y‖ₑ ^ 2 ∂(GaussMeasure n)) ^ ((2:ℝ)⁻¹)) ^ 2 := by gcongr
      _ = ∫⁻ y, ‖g y‖ₑ ^ 2 ∂(GaussMeasure n) := by
          rw [← ENNReal.rpow_natCast
            ((∫⁻ y, ‖g y‖ₑ ^ 2 ∂(GaussMeasure n)) ^ ((2:ℝ)⁻¹)) 2, ← ENNReal.rpow_mul]
          norm_num
  -- (5) the pullback along the affine map is an `L²` isometry onto its image
  have hmeasT : Measurable (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
      a • p.1 + b • p.2) := by fun_prop
  have hmp : MeasurePreserving
      (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) => a • p.1 + b • p.2)
      ((GaussMeasure n).prod (GaussMeasure n)) (GaussMeasure n) := ⟨hmeasT, GaussMixPushforward a b ha0 hb0 hab⟩
  have hqmp := hmp.quasiMeasurePreserving
  have hpull : ∀ w : Lp ℝ 2 (GaussMeasure n),
      MemLp (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
        (w : EuclideanSpace ℝ (Fin n) → ℝ) (a • p.1 + b • p.2)) 2
        ((GaussMeasure n).prod (GaussMeasure n)) :=
    fun w => (Lp.memLp w).comp_measurePreserving hmp
  -- (6) FIRST CONJUNCT: the inner integral converges absolutely for a.e. `x`
  have hint1 : ∀ w : Lp ℝ 2 (GaussMeasure n), ∀ᵐ x ∂(GaussMeasure n), Integrable
      (fun y : EuclideanSpace ℝ (Fin n) =>
        (w : EuclideanSpace ℝ (Fin n) → ℝ) (a • x + b • y)) (GaussMeasure n) :=
    fun w => ((hpull w).integrable (by norm_num)).prod_right_ae
  have hslice : ∀ w : Lp ℝ 2 (GaussMeasure n), ∀ᵐ x ∂(GaussMeasure n), AEStronglyMeasurable
      (fun y : EuclideanSpace ℝ (Fin n) =>
        (w : EuclideanSpace ℝ (Fin n) → ℝ) (a • x + b • y)) (GaussMeasure n) :=
    fun w => (hpull w).1.prodMk_left
  -- (7) the averaging operator is an `L²` contraction
  have hQnorm : ∀ w : Lp ℝ 2 (GaussMeasure n),
      eLpNorm (fun x : EuclideanSpace ℝ (Fin n) =>
          ∫ y, (w : EuclideanSpace ℝ (Fin n) → ℝ) (a • x + b • y) ∂(GaussMeasure n)) 2
          (GaussMeasure n)
        ≤ eLpNorm (w : EuclideanSpace ℝ (Fin n) → ℝ) 2 (GaussMeasure n) := by
    intro w
    rw [hES, ← eLpNorm_comp_measurePreserving (Lp.aestronglyMeasurable w) hmp, hES]
    refine ENNReal.rpow_le_rpow ?_ (by norm_num)
    calc ∫⁻ x, ‖∫ y, (w : EuclideanSpace ℝ (Fin n) → ℝ) (a • x + b • y)
            ∂(GaussMeasure n)‖ₑ ^ 2 ∂(GaussMeasure n)
        ≤ ∫⁻ x, (∫⁻ y, ‖(w : EuclideanSpace ℝ (Fin n) → ℝ) (a • x + b • y)‖ₑ ^ 2
            ∂(GaussMeasure n)) ∂(GaussMeasure n) :=
          lintegral_mono_ae ((hslice w).mono fun x hx => l2b _ hx)
      _ = ∫⁻ p, ‖(w : EuclideanSpace ℝ (Fin n) → ℝ) (a • p.1 + b • p.2)‖ₑ ^ 2
            ∂((GaussMeasure n).prod (GaussMeasure n)) :=
          lintegral_lintegral ((hpull w).1.enorm.pow_const 2)
  have hQmem : ∀ w : Lp ℝ 2 (GaussMeasure n),
      MemLp (fun x : EuclideanSpace ℝ (Fin n) =>
        ∫ y, (w : EuclideanSpace ℝ (Fin n) → ℝ) (a • x + b • y) ∂(GaussMeasure n)) 2
        (GaussMeasure n) :=
    fun w => ⟨(hpull w).1.integral_prod_right', lt_of_le_of_lt (hQnorm w) (Lp.memLp w).2⟩
  obtain ⟨Q, hQcoe, hQop⟩ : ∃ Q : Lp ℝ 2 (GaussMeasure n) → Lp ℝ 2 (GaussMeasure n),
      (∀ w, (Q w : EuclideanSpace ℝ (Fin n) → ℝ) =ᵐ[GaussMeasure n]
          fun x => ∫ y, (w : EuclideanSpace ℝ (Fin n) → ℝ) (a • x + b • y) ∂(GaussMeasure n))
        ∧ (∀ w, ‖Q w‖ ≤ ‖w‖) := by
    refine ⟨fun w => MemLp.toLp _ (hQmem w), fun w => MemLp.coeFn_toLp _, fun w => ?_⟩
    rw [Lp.norm_toLp, Lp.norm_def]
    exact ENNReal.toReal_mono (Lp.eLpNorm_ne_top w) (hQnorm w)
  -- (8) the averaging operator is linear
  have hQadd : ∀ w z : Lp ℝ 2 (GaussMeasure n), Q (w + z) = Q w + Q z := by
    intro w z
    refine Lp.ext_iff.mpr ?_
    have hsum := Measure.ae_ae_of_ae_prod (hqmp.ae (Lp.coeFn_add w z))
    filter_upwards [hQcoe (w + z), hQcoe w, hQcoe z, Lp.coeFn_add (Q w) (Q z), hsum,
      hint1 w, hint1 z] with x e1 e2 e3 e4 e5 e6 e7
    rw [e1, e4, Pi.add_apply, e2, e3, ← integral_add e6 e7]
    exact integral_congr_ae e5
  have hQsmul : ∀ (c : ℝ) (w : Lp ℝ 2 (GaussMeasure n)), Q (c • w) = c • Q w := by
    intro c w
    refine Lp.ext_iff.mpr ?_
    have hsum := Measure.ae_ae_of_ae_prod (hqmp.ae (Lp.coeFn_smul c w))
    filter_upwards [hQcoe (c • w), hQcoe w, Lp.coeFn_smul c (Q w), hsum] with x e1 e2 e3 e4
    rw [e1, e3, Pi.smul_apply, e2, smul_eq_mul, ← integral_const_mul]
    refine integral_congr_ae (e4.mono fun y hy => ?_)
    simpa using hy
  have hQ0 : Q 0 = 0 := by
    have h := hQsmul 0 0
    simpa using h
  have hQneg : ∀ w : Lp ℝ 2 (GaussMeasure n), Q (-w) = - Q w := by
    intro w
    have h := hQsmul (-1) w
    simpa using h
  have hQsub : ∀ w z : Lp ℝ 2 (GaussMeasure n), Q (w - z) = Q w - Q z := by
    intro w z
    rw [sub_eq_add_neg, hQadd, hQneg, ← sub_eq_add_neg]
  -- (9) the spectral semigroup is linear, and diagonal on the Hermite basis
  have hrepr_ext : ∀ x y : Lp ℝ 2 (GaussMeasure n),
      (∀ α, ((HermiteBasis n).repr x) α = ((HermiteBasis n).repr y) α) → x = y :=
    fun x y h => (HermiteBasis n).repr.injective (lp.ext (funext h))
  have hOUadd : ∀ w z : Lp ℝ 2 (GaussMeasure n),
      OUSemigroup s (w + z) = OUSemigroup s w + OUSemigroup s z := by
    intro w z
    refine hrepr_ext _ _ fun α => ?_
    rw [OUSemigroupSpectral s hs.le, map_add ((HermiteBasis n).repr) w z, lp.coeFn_add,
      Pi.add_apply, map_add ((HermiteBasis n).repr) (OUSemigroup s w) (OUSemigroup s z),
      lp.coeFn_add, Pi.add_apply, OUSemigroupSpectral s hs.le w α,
      OUSemigroupSpectral s hs.le z α]
    ring
  have hOUsmul : ∀ (c : ℝ) (w : Lp ℝ 2 (GaussMeasure n)),
      OUSemigroup s (c • w) = c • OUSemigroup s w := by
    intro c w
    refine hrepr_ext _ _ fun α => ?_
    rw [OUSemigroupSpectral s hs.le, map_smul ((HermiteBasis n).repr) c w, lp.coeFn_smul,
      Pi.smul_apply, map_smul ((HermiteBasis n).repr) c (OUSemigroup s w), lp.coeFn_smul,
      Pi.smul_apply, OUSemigroupSpectral s hs.le w α]
    simp only [smul_eq_mul]
    ring
  have hOU0 : OUSemigroup s (0 : Lp ℝ 2 (GaussMeasure n)) = 0 := by
    have h := hOUsmul 0 0
    simpa using h
  have hOUsub : ∀ w z : Lp ℝ 2 (GaussMeasure n),
      OUSemigroup s (w - z) = OUSemigroup s w - OUSemigroup s z := by
    intro w z
    have hneg : OUSemigroup s (-z) = - OUSemigroup s z := by
      have h := hOUsmul (-1) z
      simpa using h
    rw [sub_eq_add_neg, hOUadd, hneg, ← sub_eq_add_neg]
  have hrH : ∀ α β : Fin n → ℕ,
      ((HermiteBasis n).repr (HermiteL2 α)) β = if β = α then (1:ℝ) else 0 := by
    intro α β
    rw [show HermiteL2 α = (HermiteBasis n) α from by rw [HermiteBasis]; simp,
      HilbertBasis.repr_self]
    simp [lp.single_apply, Pi.single_apply]
  have hOUH : ∀ α : Fin n → ℕ,
      OUSemigroup s (HermiteL2 α) = Real.exp (-s * MultiIndexSum α) • HermiteL2 α := by
    intro α
    refine hrepr_ext _ _ fun β => ?_
    rw [OUSemigroupSpectral s hs.le, map_smul, lp.coeFn_smul, Pi.smul_apply, hrH, smul_eq_mul]
    by_cases h : β = α
    · rw [if_pos h, h]
    · rw [if_neg h]; ring
  have hHcoe : ∀ α : Fin n → ℕ,
      ((HermiteL2 α : Lp ℝ 2 (GaussMeasure n)) : EuclideanSpace ℝ (Fin n) → ℝ)
        =ᵐ[GaussMeasure n] HermiteFun α := by
    intro α
    rw [HermiteL2]
    exact MemLp.coeFn_toLp _
  -- (10) the two operators agree on every Hermite function, hence on their span
  have hQH : ∀ α : Fin n → ℕ, Q (HermiteL2 α) = OUSemigroup s (HermiteL2 α) := by
    intro α
    rw [hOUH α]
    refine Lp.ext_iff.mpr ?_
    have hsl := Measure.ae_ae_of_ae_prod (hqmp.ae (hHcoe α))
    filter_upwards [hQcoe (HermiteL2 α), hsl, Lp.coeFn_smul
      (Real.exp (-s * MultiIndexSum α)) (HermiteL2 α), hHcoe α] with x e1 e2 e3 e4
    rw [e1, e3, Pi.smul_apply, e4, smul_eq_mul, ← hpow]
    rw [integral_congr_ae e2]
    rw [hbdef2]; exact HermiteFunReproduction a ha0 ha1 α x
  have hspan : ∀ w ∈ Submodule.span ℝ (Set.range (HermiteL2 (n := n))),
      Q w = OUSemigroup s w := by
    intro w hw
    induction hw using Submodule.span_induction with
    | mem x hx => obtain ⟨α, rfl⟩ := hx; exact hQH α
    | zero => rw [hQ0, hOU0]
    | add x y _ _ ihx ihy => rw [hQadd, hOUadd, ihx, ihy]
    | smul c x _ ih => rw [hQsmul, hOUsmul, ih]
  -- (11) SECOND CONJUNCT: completeness of the Hermite family upgrades this to all of `L²`
  have hvcl : v ∈ closure ((Submodule.span ℝ (Set.range (HermiteL2 (n := n))) :
      Submodule ℝ (Lp ℝ 2 (GaussMeasure n))) : Set (Lp ℝ 2 (GaussMeasure n))) :=
    HermiteL2Complete n (Submodule.mem_top)
  have hfinal : Q v = OUSemigroup s v := by
    have key : ∀ ε > (0:ℝ), ‖Q v - OUSemigroup s v‖ ≤ 2 * ε := by
      intro ε hε
      obtain ⟨p, hp, hdist⟩ := Metric.mem_closure_iff.mp hvcl ε hε
      have hd : Q v - OUSemigroup s v = Q (v - p) - OUSemigroup s (v - p) := by
        rw [hQsub, hOUsub, hspan p hp]
        abel
      have h3 : ‖v - p‖ < ε := by rwa [dist_eq_norm] at hdist
      calc ‖Q v - OUSemigroup s v‖ = ‖Q (v - p) - OUSemigroup s (v - p)‖ := by rw [hd]
        _ ≤ ‖Q (v - p)‖ + ‖OUSemigroup s (v - p)‖ := norm_sub_le _ _
        _ ≤ ‖v - p‖ + ‖v - p‖ :=
            add_le_add (hQop _) (OUSelfAdjointContraction s hs.le (v - p) (v - p)).2
        _ ≤ 2 * ε := by linarith
    have hz : ‖Q v - OUSemigroup s v‖ = 0 := by
      by_contra hc
      have hpos : 0 < ‖Q v - OUSemigroup s v‖ :=
        lt_of_le_of_ne (norm_nonneg _) (Ne.symm hc)
      have := key (‖Q v - OUSemigroup s v‖ / 4) (by linarith)
      linarith
    rwa [norm_eq_zero, sub_eq_zero] at hz
  -- (12) THIRD CONJUNCT: positivity preservation, from the averaging formula
  refine ⟨hint1 v, ?_, ?_⟩
  · have h := hQcoe v
    rw [hfinal] at h
    exact h
  · intro hvpos
    have h := hQcoe v
    rw [hfinal] at h
    have hsl := Measure.ae_ae_of_ae_prod (hqmp.ae hvpos)
    filter_upwards [h, hsl] with x e1 e2
    rw [e1]
    exact integral_nonneg_of_ae e2
