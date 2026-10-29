module

public import GaussianRiesz.OUCoupling
public import GaussianRiesz.MehlerFormula
public import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
public import GaussianRiesz.GaussCharFun

@[expose] public section
open MeasureTheory
theorem OUCouplingKernel {n : ℕ} (s : ℝ) (hs : 0 < s) :
    IsProbabilityMeasure (OUCoupling n s)
      ∧ (OUCoupling n s).map Prod.swap = OUCoupling n s
      ∧ (OUCoupling n s).map Prod.fst = GaussMeasure n
      ∧ (OUCoupling n s).map Prod.snd = GaussMeasure n
      ∧ ∀ v w : Lp ℝ 2 (GaussMeasure n),
          Integrable (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
              (v : EuclideanSpace ℝ (Fin n) → ℝ) p.2
                * (w : EuclideanSpace ℝ (Fin n) → ℝ) p.1) (OUCoupling n s)
            ∧ inner ℝ (OUSemigroup s v) w
                = ∫ p, (v : EuclideanSpace ℝ (Fin n) → ℝ) p.2
                    * (w : EuclideanSpace ℝ (Fin n) → ℝ) p.1 ∂(OUCoupling n s) := by
  classical
  -- the rotation `S (x,y) = (a x + b y, b x - a y)` preserves `γ_n ⊗ γ_n`
  have spush : ∀ a b : ℝ, a ^ 2 + b ^ 2 = 1 →
      ((GaussMeasure n).prod (GaussMeasure n)).map
          (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
            (a • p.1 + b • p.2, b • p.1 - a • p.2))
        = (GaussMeasure n).prod (GaussMeasure n) := by
    intro a b hab
    have hmeas : Measurable (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
        (a • p.1 + b • p.2, b • p.1 - a • p.2)) := by fun_prop
    have : IsProbabilityMeasure (((GaussMeasure n).prod (GaussMeasure n)).map
        (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
          (a • p.1 + b • p.2, b • p.1 - a • p.2))) :=
      (Measure.isProbabilityMeasure_map_iff hmeas.aemeasurable).mpr inferInstance
    rw [← charFun_eq_prod_iff]
    intro t
    rw [Measure.map_map (by fun_prop) hmeas, charFun_apply,
      integral_map (by fun_prop) (by fun_prop)]
    simp only [Function.comp_apply]
    have hsplit : ∀ p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n),
        Complex.exp ((inner ℝ (WithLp.toLp 2 (a • p.1 + b • p.2, b • p.1 - a • p.2)) t : ℝ)
              * Complex.I)
          = Complex.exp ((inner ℝ p.1 (a • (WithLp.ofLp t).1 + b • (WithLp.ofLp t).2) : ℝ)
                * Complex.I)
            * Complex.exp ((inner ℝ p.2 (b • (WithLp.ofLp t).1 - a • (WithLp.ofLp t).2) : ℝ)
                * Complex.I) := by
      intro p
      rw [← Complex.exp_add]
      congr 1
      rw [WithLp.prod_inner_apply]
      rw [inner_add_left, inner_sub_left, real_inner_smul_left, real_inner_smul_left,
        real_inner_smul_left, real_inner_smul_left, inner_add_right, inner_sub_right,
        real_inner_smul_right, real_inner_smul_right, real_inner_smul_right,
        real_inner_smul_right]
      push_cast
      ring
    rw [integral_congr_ae (Filter.Eventually.of_forall hsplit),
      integral_prod_mul (μ := GaussMeasure n) (ν := GaussMeasure n)
        (fun x : EuclideanSpace ℝ (Fin n) =>
          Complex.exp ((inner ℝ x (a • (WithLp.ofLp t).1 + b • (WithLp.ofLp t).2) : ℝ) * Complex.I))
        (fun y : EuclideanSpace ℝ (Fin n) =>
          Complex.exp ((inner ℝ y (b • (WithLp.ofLp t).1 - a • (WithLp.ofLp t).2) : ℝ) * Complex.I))]
    rw [← charFun_apply, ← charFun_apply, GaussCharFun, GaussCharFun, GaussCharFun, GaussCharFun,
      ← Complex.exp_add, ← Complex.exp_add]
    congr 1
    simp only [← Complex.ofReal_pow]
    have hn1 : ‖a • (WithLp.ofLp t).1 + b • (WithLp.ofLp t).2‖ ^ 2
        = a ^ 2 * ‖(WithLp.ofLp t).1‖ ^ 2
          + 2 * (a * b) * (inner ℝ (WithLp.ofLp t).1 (WithLp.ofLp t).2 : ℝ)
          + b ^ 2 * ‖(WithLp.ofLp t).2‖ ^ 2 := by
      rw [norm_add_sq_real, norm_smul, norm_smul, real_inner_smul_left, real_inner_smul_right]
      simp only [Real.norm_eq_abs]
      rw [mul_pow, mul_pow, sq_abs, sq_abs]
      ring
    have hn2 : ‖b • (WithLp.ofLp t).1 - a • (WithLp.ofLp t).2‖ ^ 2
        = b ^ 2 * ‖(WithLp.ofLp t).1‖ ^ 2
          - 2 * (a * b) * (inner ℝ (WithLp.ofLp t).1 (WithLp.ofLp t).2 : ℝ)
          + a ^ 2 * ‖(WithLp.ofLp t).2‖ ^ 2 := by
      rw [norm_sub_sq_real, norm_smul, norm_smul, real_inner_smul_left, real_inner_smul_right]
      simp only [Real.norm_eq_abs]
      rw [mul_pow, mul_pow, sq_abs, sq_abs]
      ring
    rw [hn1, hn2]
    have hc : (a:ℂ) ^ 2 + (b:ℂ) ^ 2 = 1 := by
      rw [show ((a:ℂ))^2 + ((b:ℂ))^2 = ((a^2 + b^2 : ℝ) : ℂ) from by push_cast; ring, hab]
      norm_num
    push_cast
    field_simp
    ring_nf
    linear_combination (-(‖(WithLp.ofLp t).1‖:ℂ)^2 - (‖(WithLp.ofLp t).2‖:ℂ)^2) * hc
  -- scalar bookkeeping: `r = e^{-s}`, `τ = √(1 - e^{-2s})`, and `r² + τ² = 1`
  have hr0 : (0:ℝ) ≤ Real.exp (-s) := (Real.exp_pos _).le
  have hr1 : Real.exp (-s) ≤ 1 := by rw [Real.exp_le_one_iff]; linarith
  have hrsq : Real.exp (-s) ^ 2 = Real.exp (-2 * s) := by
    rw [← Real.exp_nat_mul]; ring_nf
  have hr2le : Real.exp (-s) ^ 2 ≤ 1 := by nlinarith
  have htausq : Real.sqrt (1 - Real.exp (-2 * s)) ^ 2 = 1 - Real.exp (-s) ^ 2 := by
    rw [Real.sq_sqrt (by rw [← hrsq]; linarith), hrsq]
  have hrt : Real.exp (-s) ^ 2 + Real.sqrt (1 - Real.exp (-2 * s)) ^ 2 = 1 := by
    rw [htausq]; ring
  -- the coupling map
  have hTmeas : Measurable (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
      (p.1, Real.exp (-s) • p.1 + Real.sqrt (1 - Real.exp (-2 * s)) • p.2)) := by fun_prop
  have hSmeas : Measurable (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
      (Real.exp (-s) • p.1 + Real.sqrt (1 - Real.exp (-2 * s)) • p.2,
        Real.sqrt (1 - Real.exp (-2 * s)) • p.1 - Real.exp (-s) • p.2)) := by fun_prop
  -- (1) a probability measure
  have hprob : IsProbabilityMeasure (OUCoupling n s) := by
    rw [OUCoupling]
    exact (Measure.isProbabilityMeasure_map_iff hTmeas.aemeasurable).mpr inferInstance
  -- (3) the first marginal
  have hfst : (OUCoupling n s).map Prod.fst = GaussMeasure n := by
    rw [OUCoupling, Measure.map_map measurable_fst hTmeas]
    exact Measure.fst_prod
  -- (4) the second marginal: a marginal of the rotation invariance
  have hsndcore : ((GaussMeasure n).prod (GaussMeasure n)).map
      (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
        Real.exp (-s) • p.1 + Real.sqrt (1 - Real.exp (-2 * s)) • p.2) = GaussMeasure n := by
    have h : (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
        Real.exp (-s) • p.1 + Real.sqrt (1 - Real.exp (-2 * s)) • p.2)
        = Prod.fst ∘ (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
          (Real.exp (-s) • p.1 + Real.sqrt (1 - Real.exp (-2 * s)) • p.2,
            Real.sqrt (1 - Real.exp (-2 * s)) • p.1 - Real.exp (-s) • p.2)) := rfl
    rw [h, ← Measure.map_map measurable_fst hSmeas, spush _ _ hrt]
    exact Measure.fst_prod
  have hsnd : (OUCoupling n s).map Prod.snd = GaussMeasure n := by
    rw [OUCoupling, Measure.map_map measurable_snd hTmeas]
    exact hsndcore
  -- (2) swap symmetry, from `swap ∘ T = T ∘ S`
  have hswap : (OUCoupling n s).map Prod.swap = OUCoupling n s := by
    rw [OUCoupling, Measure.map_map measurable_swap hTmeas]
    have h : (Prod.swap ∘ fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
          (p.1, Real.exp (-s) • p.1 + Real.sqrt (1 - Real.exp (-2 * s)) • p.2))
        = (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
            (p.1, Real.exp (-s) • p.1 + Real.sqrt (1 - Real.exp (-2 * s)) • p.2))
          ∘ (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
            (Real.exp (-s) • p.1 + Real.sqrt (1 - Real.exp (-2 * s)) • p.2,
              Real.sqrt (1 - Real.exp (-2 * s)) • p.1 - Real.exp (-s) • p.2)) := by
      funext p
      simp only [Function.comp_apply, Prod.swap_prod_mk, Prod.mk.injEq]
      refine ⟨trivial, ?_⟩
      rw [smul_add, smul_sub, smul_smul, smul_smul, smul_smul, smul_smul]
      rw [show Real.exp (-s) * Real.sqrt (1 - Real.exp (-2 * s))
          = Real.sqrt (1 - Real.exp (-2 * s)) * Real.exp (-s) from by ring]
      have e1 : (Real.exp (-s) * Real.exp (-s)) • p.1
            + (Real.sqrt (1 - Real.exp (-2 * s)) * Real.exp (-s)) • p.2
            + ((Real.sqrt (1 - Real.exp (-2 * s)) * Real.sqrt (1 - Real.exp (-2 * s))) • p.1
              - (Real.sqrt (1 - Real.exp (-2 * s)) * Real.exp (-s)) • p.2)
          = (Real.exp (-s) * Real.exp (-s)
              + Real.sqrt (1 - Real.exp (-2 * s)) * Real.sqrt (1 - Real.exp (-2 * s))) • p.1 := by
        rw [add_smul]; abel
      rw [e1, show Real.exp (-s) * Real.exp (-s)
          + Real.sqrt (1 - Real.exp (-2 * s)) * Real.sqrt (1 - Real.exp (-2 * s)) = 1 from by
            rw [← pow_two, ← pow_two]; exact hrt, one_smul]
    rw [h, ← Measure.map_map hTmeas hSmeas, spush _ _ hrt]
  refine ⟨hprob, hswap, hfst, hsnd, ?_⟩
  intro v w
  have hmpfst : MeasurePreserving (Prod.fst :
      EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
      (OUCoupling n s) (GaussMeasure n) := ⟨measurable_fst, hfst⟩
  have hmpsnd : MeasurePreserving (Prod.snd :
      EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
      (OUCoupling n s) (GaussMeasure n) := ⟨measurable_snd, hsnd⟩
  have hvν : MemLp (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
      (v : EuclideanSpace ℝ (Fin n) → ℝ) p.2) 2 (OUCoupling n s) :=
    (Lp.memLp v).comp_measurePreserving hmpsnd
  have hwν : MemLp (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
      (w : EuclideanSpace ℝ (Fin n) → ℝ) p.1) 2 (OUCoupling n s) :=
    (Lp.memLp w).comp_measurePreserving hmpfst
  have hintν : Integrable (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
      (v : EuclideanSpace ℝ (Fin n) → ℝ) p.2
        * (w : EuclideanSpace ℝ (Fin n) → ℝ) p.1) (OUCoupling n s) :=
    (hvν.integrable_mul hwν).congr (Filter.Eventually.of_forall fun p => rfl)
  refine ⟨hintν, ?_⟩
  have hmul : ∀ a b : ℝ, (inner ℝ a b : ℝ) = a * b := by
    intro a b; simp [RCLike.inner_apply, mul_comm]
  -- pull the right-hand side back to `γ ⊗ γ`
  have hRHS : (∫ p, (v : EuclideanSpace ℝ (Fin n) → ℝ) p.2
        * (w : EuclideanSpace ℝ (Fin n) → ℝ) p.1 ∂(OUCoupling n s))
      = ∫ q, (v : EuclideanSpace ℝ (Fin n) → ℝ)
            (Real.exp (-s) • q.1 + Real.sqrt (1 - Real.exp (-2 * s)) • q.2)
          * (w : EuclideanSpace ℝ (Fin n) → ℝ) q.1
          ∂((GaussMeasure n).prod (GaussMeasure n)) := by
    have hm : AEStronglyMeasurable
        (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
          (v : EuclideanSpace ℝ (Fin n) → ℝ) p.2 * (w : EuclideanSpace ℝ (Fin n) → ℝ) p.1)
        (((GaussMeasure n).prod (GaussMeasure n)).map
          (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
            (p.1, Real.exp (-s) • p.1 + Real.sqrt (1 - Real.exp (-2 * s)) • p.2))) := by
      rw [← OUCoupling]
      exact (hvν.aestronglyMeasurable.mul hwν.aestronglyMeasurable).congr (Filter.Eventually.of_forall fun p => rfl)
    rw [OUCoupling, integral_map hTmeas.aemeasurable hm]
  -- the integrand is integrable on the product
  have hmp2 : MeasurePreserving
      (fun q : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
        Real.exp (-s) • q.1 + Real.sqrt (1 - Real.exp (-2 * s)) • q.2)
      ((GaussMeasure n).prod (GaussMeasure n)) (GaussMeasure n) := ⟨by fun_prop, hsndcore⟩
  have hmpf2 : MeasurePreserving (Prod.fst :
      EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
      ((GaussMeasure n).prod (GaussMeasure n)) (GaussMeasure n) :=
    ⟨measurable_fst, Measure.fst_prod⟩
  have hintp : Integrable (fun q : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
      (v : EuclideanSpace ℝ (Fin n) → ℝ)
          (Real.exp (-s) • q.1 + Real.sqrt (1 - Real.exp (-2 * s)) • q.2)
        * (w : EuclideanSpace ℝ (Fin n) → ℝ) q.1)
      ((GaussMeasure n).prod (GaussMeasure n)) :=
    (((Lp.memLp v).comp_measurePreserving hmp2).integrable_mul
      ((Lp.memLp w).comp_measurePreserving hmpf2)).congr
      (Filter.Eventually.of_forall fun q => rfl)
  -- Mehler turns the inner product into the iterated integral
  have hLHS : (inner ℝ (OUSemigroup s v) w : ℝ)
      = ∫ x, (∫ y, (v : EuclideanSpace ℝ (Fin n) → ℝ)
          (Real.exp (-s) • x + Real.sqrt (1 - Real.exp (-2 * s)) • y) ∂(GaussMeasure n))
          * (w : EuclideanSpace ℝ (Fin n) → ℝ) x ∂(GaussMeasure n) := by
    rw [L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [(MehlerFormula s hs v).2.1] with x hx
    rw [hmul, hx]
  rw [hLHS, hRHS,
    integral_congr_ae (Filter.Eventually.of_forall fun x : EuclideanSpace ℝ (Fin n) =>
      (integral_mul_const ((w : EuclideanSpace ℝ (Fin n) → ℝ) x)
        (fun y : EuclideanSpace ℝ (Fin n) => (v : EuclideanSpace ℝ (Fin n) → ℝ)
          (Real.exp (-s) • x + Real.sqrt (1 - Real.exp (-2 * s)) • y))).symm)]
  exact integral_integral (f := fun (x y : EuclideanSpace ℝ (Fin n)) =>
    (v : EuclideanSpace ℝ (Fin n) → ℝ)
        (Real.exp (-s) • x + Real.sqrt (1 - Real.exp (-2 * s)) • y)
      * (w : EuclideanSpace ℝ (Fin n) → ℝ) x) hintp
