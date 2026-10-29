module

public import GaussianRiesz.HermiteL2
public import GaussianRiesz.L2IntoL1
public import GaussianRiesz.Hermite1Zero
public import GaussianRiesz.HermiteDerivative
public import Mathlib.Analysis.InnerProductSpace.l2Space
public import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
public import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform

@[expose] public section
open MeasureTheory
theorem HermiteL2Complete (n : ℕ) :
    ⊤ ≤ (Submodule.span ℝ (Set.range (HermiteL2 (n := n)))).topologicalClosure := by
  classical
  -- (0) Gaussian integrability with the half exponent, used for the exponential moments
  have gaussInt : Integrable
      (fun x : EuclideanSpace ℝ (Fin n) => Real.exp (-‖x‖ ^ 2 / 2)) volume := by
    have h := (GaussianFourier.integrable_cexp_neg_mul_sq_norm_add
        (V := EuclideanSpace ℝ (Fin n)) (b := ((1:ℂ)/2)) (by norm_num) 0 0).re
    refine h.congr ?_
    filter_upwards with v
    simp only [zero_mul, add_zero]
    rw [show (-((1:ℂ)/2) * ((‖v‖ : ℝ) : ℂ) ^ 2) = (((-‖v‖ ^ 2 / 2 : ℝ)) : ℂ) by push_cast; ring]
    exact Complex.exp_ofReal_re _
  -- (1) every exponential `exp (c ‖x‖)` is square integrable for the Gaussian measure
  have expMemLp : ∀ c : ℝ,
      MemLp (fun x : EuclideanSpace ℝ (Fin n) => Real.exp (c * ‖x‖)) 2 (GaussMeasure n) := by
    intro c
    have hcont : Continuous (fun x : EuclideanSpace ℝ (Fin n) => Real.exp (c * ‖x‖)) :=
      Real.continuous_exp.comp (continuous_const.mul continuous_norm)
    rw [memLp_two_iff_integrable_sq hcont.aestronglyMeasurable]
    have hdm : Measurable (fun x : EuclideanSpace ℝ (Fin n) =>
        ENNReal.ofReal (Real.pi ^ (-(n : ℝ) / 2) * Real.exp (-‖x‖ ^ 2))) := by
      fun_prop
    have hfin : ∀ᵐ x : EuclideanSpace ℝ (Fin n) ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
        ENNReal.ofReal (Real.pi ^ (-(n : ℝ) / 2) * Real.exp (-‖x‖ ^ 2)) < ⊤ := by
      filter_upwards with x
      exact ENNReal.ofReal_lt_top
    rw [GaussMeasure, integrable_withDensity_iff hdm hfin]
    have hpi : (0:ℝ) < Real.pi ^ (-(n : ℝ) / 2) := Real.rpow_pos_of_pos Real.pi_pos _
    refine Integrable.mono'
      ((gaussInt.const_mul (Real.pi ^ (-(n : ℝ) / 2) * Real.exp (2 * c ^ 2)))) ?_ ?_
    · exact ((hcont.pow 2).aestronglyMeasurable).mul
        (hdm.ennreal_toReal).aestronglyMeasurable
    · filter_upwards with x
      have hx : (0:ℝ) ≤ ‖x‖ := norm_nonneg x
      have hb : 2 * c * ‖x‖ + -‖x‖ ^ 2 ≤ 2 * c ^ 2 + -‖x‖ ^ 2 / 2 := by
        nlinarith [sq_nonneg (‖x‖ - 2 * c)]
      rw [ENNReal.toReal_ofReal (by positivity)]
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      have hL : Real.exp (c * ‖x‖) ^ 2 * (Real.pi ^ (-(n : ℝ) / 2) * Real.exp (-‖x‖ ^ 2))
          = Real.pi ^ (-(n : ℝ) / 2) * Real.exp (2 * c * ‖x‖ + -‖x‖ ^ 2) := by
        rw [Real.exp_add, ← Real.exp_nat_mul]
        push_cast
        rw [show (2:ℝ) * (c * ‖x‖) = 2 * c * ‖x‖ by ring]
        ring
      have hR : Real.pi ^ (-(n : ℝ) / 2) * Real.exp (2 * c ^ 2) * Real.exp (-‖x‖ ^ 2 / 2)
          = Real.pi ^ (-(n : ℝ) / 2) * Real.exp (2 * c ^ 2 + -‖x‖ ^ 2 / 2) := by
        rw [Real.exp_add]; ring
      rw [hL, hR]
      exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hb) hpi.le
  -- (2) the one-variable three-term recurrence `√2 x h_k = √(k+1) h_{k+1} + √k h_{k-1}`
  have hrec1 : ∀ (k : ℕ) (x : ℝ),
      Real.sqrt 2 * x * Hermite1 k x
        = Real.sqrt (k + 1) * Hermite1 (k + 1) x + Real.sqrt k * Hermite1 (k - 1) x := by
    intro k x
    cases k with
    | zero =>
        simp [Hermite1, Polynomial.hermite_zero]
    | succ m =>
        have hd := HermiteDerivative m
        have h2 : (Real.sqrt 2 * x) *
              Polynomial.aeval (Real.sqrt 2 * x) (Polynomial.hermite (m+1))
            = Polynomial.aeval (Real.sqrt 2 * x) (Polynomial.hermite (m+2))
              + ((m : ℝ)+1) * Polynomial.aeval (Real.sqrt 2 * x) (Polynomial.hermite m) := by
          have hX : Polynomial.X * Polynomial.hermite (m+1)
              = Polynomial.hermite (m+2) + Polynomial.derivative (Polynomial.hermite (m+1)) := by
            rw [Polynomial.hermite_succ (m+1)]
            ring
          have h3 : Polynomial.aeval (Real.sqrt 2 * x)
                (Polynomial.X * Polynomial.hermite (m+1))
              = Polynomial.aeval (Real.sqrt 2 * x)
                (Polynomial.hermite (m+2)
                  + Polynomial.derivative (Polynomial.hermite (m+1))) := by
            rw [hX]
          rw [hd] at h3
          simp only [map_mul, map_add, Polynomial.aeval_X, nsmul_eq_mul, map_natCast] at h3
          push_cast at h3
          linarith [h3]
        simp only [Hermite1, Nat.add_sub_cancel]
        push_cast
        set A0 := Polynomial.aeval (Real.sqrt 2 * x) (Polynomial.hermite m) with hA0
        set A1 := Polynomial.aeval (Real.sqrt 2 * x) (Polynomial.hermite (m+1)) with hA1
        set A2 := Polynomial.aeval (Real.sqrt 2 * x) (Polynomial.hermite (m+1+1)) with hA2
        have hs : Real.sqrt ((m:ℝ)+1) * Real.sqrt ((m:ℝ)+1) = (m:ℝ)+1 :=
          Real.mul_self_sqrt (by positivity)
        have hs0 : Real.sqrt ((m:ℝ)+1) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by positivity))
        have ht0 : Real.sqrt ((m:ℝ)+1+1) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by positivity))
        have hG0 : Real.sqrt ((Nat.factorial m : ℝ)) ≠ 0 :=
          ne_of_gt (Real.sqrt_pos.mpr (by exact_mod_cast Nat.factorial_pos m))
        have e2 : Real.sqrt ((Nat.factorial (m+1) : ℝ))
            = Real.sqrt ((m:ℝ)+1) * Real.sqrt ((Nat.factorial m : ℝ)) := by
          rw [← Real.sqrt_mul (by positivity)]
          congr 1
          rw [Nat.factorial_succ m]
          push_cast
          ring
        have e1 : Real.sqrt ((Nat.factorial (m+1+1) : ℝ))
            = Real.sqrt ((m:ℝ)+1+1) * Real.sqrt ((Nat.factorial (m+1) : ℝ)) := by
          rw [← Real.sqrt_mul (by positivity)]
          congr 1
          rw [Nat.factorial_succ (m+1)]
          push_cast
          ring
        rw [e1, e2]
        have r1 : Real.sqrt ((m:ℝ)+1+1) *
              (A2 / (Real.sqrt ((m:ℝ)+1+1) *
                (Real.sqrt ((m:ℝ)+1) * Real.sqrt ((Nat.factorial m : ℝ)))))
            = A2 / (Real.sqrt ((m:ℝ)+1) * Real.sqrt ((Nat.factorial m : ℝ))) := by
          field_simp
        have r2 : Real.sqrt ((m:ℝ)+1) * (A0 / Real.sqrt ((Nat.factorial m : ℝ)))
            = ((m:ℝ)+1) * A0
              / (Real.sqrt ((m:ℝ)+1) * Real.sqrt ((Nat.factorial m : ℝ))) := by
          have hx : ((m:ℝ)+1) * A0
                / (Real.sqrt ((m:ℝ)+1) * Real.sqrt ((Nat.factorial m : ℝ)))
              = (Real.sqrt ((m:ℝ)+1) * Real.sqrt ((m:ℝ)+1)) * A0
                / (Real.sqrt ((m:ℝ)+1) * Real.sqrt ((Nat.factorial m : ℝ))) := by
            rw [hs]
          rw [hx]
          field_simp
        rw [r1, r2, ← add_div, ← h2]
        ring
  -- (3) the same recurrence in the `j`-th coordinate of the `n`-variable Hermite functions
  have hrecN : ∀ (j : Fin n) (α : Fin n → ℕ) (x : EuclideanSpace ℝ (Fin n)),
      Real.sqrt 2 * (x j * HermiteFun α x)
        = Real.sqrt (α j + 1) * HermiteFun (Function.update α j (α j + 1)) x
          + Real.sqrt (α j) * HermiteFun (Function.update α j (α j - 1)) x := by
    intro j α x
    have hsplit : ∀ β : Fin n → ℕ, HermiteFun β x
        = Hermite1 (β j) (x j) * ∏ i ∈ Finset.univ.erase j, Hermite1 (β i) (x i) := by
      intro β
      rw [HermiteFun]
      exact (Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ j)).symm
    have hR : ∀ (v : ℕ),
        (∏ i ∈ Finset.univ.erase j, Hermite1 ((Function.update α j v) i) (x i))
        = ∏ i ∈ Finset.univ.erase j, Hermite1 (α i) (x i) := by
      intro v
      refine Finset.prod_congr rfl ?_
      intro i hi
      rw [Function.update_of_ne (Finset.ne_of_mem_erase hi)]
    rw [hsplit α, hsplit (Function.update α j (α j + 1)),
      hsplit (Function.update α j (α j - 1)), hR, hR,
      Function.update_self, Function.update_self]
    have hh := hrec1 (α j) (x j)
    push_cast at hh ⊢
    linear_combination (∏ i ∈ Finset.univ.erase j, Hermite1 (α i) (x i)) * hh
  -- (4) the span of the Hermite functions is stable under multiplication by a coordinate
  have spanmul : ∀ (j : Fin n) (g : EuclideanSpace ℝ (Fin n) → ℝ),
      g ∈ Submodule.span ℝ (Set.range (HermiteFun (n := n))) →
      (fun x => x j * g x) ∈ Submodule.span ℝ (Set.range (HermiteFun (n := n))) := by
    intro j g hg
    induction hg using Submodule.span_induction with
    | mem y hy =>
        obtain ⟨α, rfl⟩ := hy
        have hs2 : (0:ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
        have hid : (fun x : EuclideanSpace ℝ (Fin n) => x j * HermiteFun α x)
            = (Real.sqrt 2)⁻¹ • (Real.sqrt (α j + 1) • HermiteFun (Function.update α j (α j+1))
                + Real.sqrt (α j) • HermiteFun (Function.update α j (α j-1))) := by
          funext x
          have h := hrecN j α x
          simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul]
          field_simp
          linarith [h]
        rw [hid]
        exact Submodule.smul_mem _ _ (Submodule.add_mem _
          (Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩))
          (Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)))
    | zero =>
        have h0 : (fun x : EuclideanSpace ℝ (Fin n) =>
            x j * (0 : EuclideanSpace ℝ (Fin n) → ℝ) x) = 0 := by
          funext x; simp
        rw [h0]
        exact Submodule.zero_mem _
    | add y z _ _ hy hz =>
        have h1 : (fun x : EuclideanSpace ℝ (Fin n) => x j * (y + z) x)
            = (fun x => x j * y x) + (fun x => x j * z x) := by
          funext x; simp [mul_add]
        rw [h1]
        exact Submodule.add_mem _ hy hz
    | smul c y _ hy =>
        have h1 : (fun x : EuclideanSpace ℝ (Fin n) => x j * (c • y) x)
            = c • (fun x => x j * y x) := by
          funext x; simp only [Pi.smul_apply, smul_eq_mul]; ring
        rw [h1]
        exact Submodule.smul_mem _ _ hy
  -- (5) hence every power of a linear functional lies in that span
  have spanpow : ∀ (ξ : EuclideanSpace ℝ (Fin n)) (m : ℕ),
      (fun x : EuclideanSpace ℝ (Fin n) => (inner ℝ ξ x : ℝ) ^ m)
        ∈ Submodule.span ℝ (Set.range (HermiteFun (n := n))) := by
    intro ξ m
    have hinner : ∀ x : EuclideanSpace ℝ (Fin n), (inner ℝ ξ x : ℝ) = ∑ i, ξ i * x i := by
      intro x
      rw [PiLp.inner_apply]
      simp [RCLike.inner_apply, mul_comm]
    induction m with
    | zero =>
        have h1 : (fun x : EuclideanSpace ℝ (Fin n) => (inner ℝ ξ x : ℝ) ^ 0)
            = HermiteFun (fun _ => 0) := by
          funext x
          simp [HermiteFun, Hermite1Zero]
        rw [h1]
        exact Submodule.subset_span ⟨_, rfl⟩
    | succ m ih =>
        have h1 : (fun x : EuclideanSpace ℝ (Fin n) => (inner ℝ ξ x : ℝ) ^ (m+1))
            = ∑ i : Fin n, ξ i • (fun x : EuclideanSpace ℝ (Fin n) =>
                x i * (inner ℝ ξ x : ℝ) ^ m) := by
          funext x
          rw [Finset.sum_apply]
          simp only [Pi.smul_apply, smul_eq_mul]
          rw [pow_succ, hinner x, Finset.mul_sum]
          refine Finset.sum_congr rfl ?_
          intro i _
          ring
        rw [h1]
        exact Submodule.sum_mem _ (fun i _ => Submodule.smul_mem _ _ (spanmul i _ ih))
  -- (6) the orthogonal complement of the span is trivial
  have horth : (Submodule.span ℝ (Set.range (HermiteL2 (n := n))))ᗮ = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro f hf
    have h0 : ∀ α : Fin n → ℕ, inner ℝ (HermiteL2 (n := n) α) f = (0:ℝ) := fun α =>
      (Submodule.mem_orthogonal _ _).1 hf _ (Submodule.subset_span ⟨α, rfl⟩)
    obtain ⟨F, hFsm, hFae⟩ := Lp.aestronglyMeasurable f
    have hFLp : MemLp F 2 (GaussMeasure n) := MemLp.ae_eq hFae (Lp.memLp f)
    have hFint : Integrable F (GaussMeasure n) := hFLp.integrable (by norm_num)
    -- (6a) `F` integrates to zero against every element of the Hermite span
    have hspan : ∀ g ∈ Submodule.span ℝ (Set.range (HermiteFun (n := n))),
        Integrable (fun x => g x * F x) (GaussMeasure n)
          ∧ ∫ x, g x * F x ∂(GaussMeasure n) = 0 := by
      intro g hg
      induction hg using Submodule.span_induction with
      | mem y hy =>
          obtain ⟨α, rfl⟩ := hy
          have hint : Integrable (fun x => HermiteFun α x * F x) (GaussMeasure n) :=
            ((HermiteFunMemLp α).integrable_mul hFLp).congr
              (Filter.Eventually.of_forall fun x => rfl)
          refine ⟨hint, ?_⟩
          have hconv : inner ℝ (HermiteL2 (n := n) α) f
              = ∫ x, HermiteFun α x * F x ∂(GaussMeasure n) := by
            rw [L2.inner_def]
            refine integral_congr_ae ?_
            filter_upwards [MemLp.coeFn_toLp (HermiteFunMemLp α), hFae] with x hx hy
            rw [show ((HermiteL2 (n := n) α : Lp ℝ 2 (GaussMeasure n)) :
                EuclideanSpace ℝ (Fin n) → ℝ) x = HermiteFun α x from hx,
              show ((f : Lp ℝ 2 (GaussMeasure n)) :
                EuclideanSpace ℝ (Fin n) → ℝ) x = F x from hy]
            simp only [RCLike.inner_apply, conj_trivial]
            ring
          rw [← hconv, h0 α]
      | zero =>
          refine ⟨?_, ?_⟩
          · simp
          · simp
      | add y z _ _ hy hz =>
          have hpt : (fun x => (y + z) x * F x)
              = fun x => y x * F x + z x * F x := by
            funext x; simp [add_mul]
          rw [hpt]
          exact ⟨hy.1.add hz.1, by rw [integral_add hy.1 hz.1, hy.2, hz.2, add_zero]⟩
      | smul c y _ hy =>
          have hpt : (fun x => (c • y) x * F x) = fun x => c * (y x * F x) := by
            funext x; simp only [Pi.smul_apply, smul_eq_mul]; ring
          rw [hpt]
          exact ⟨hy.1.const_mul c, by rw [integral_const_mul, hy.2, mul_zero]⟩
    have hpow : ∀ (ξ : EuclideanSpace ℝ (Fin n)) (m : ℕ),
        Integrable (fun x => (inner ℝ ξ x : ℝ) ^ m * F x) (GaussMeasure n)
          ∧ ∫ x, (inner ℝ ξ x : ℝ) ^ m * F x ∂(GaussMeasure n) = 0 :=
      fun ξ m => hspan _ (spanpow ξ m)
    have hdom : ∀ c : ℝ,
        Integrable (fun x => Real.exp (c * ‖x‖) * |F x|) (GaussMeasure n) := by
      intro c
      exact ((expMemLp c).integrable_mul hFLp.abs).congr
        (Filter.Eventually.of_forall fun x => rfl)
    -- (6b) the Fourier integral of `F dγ` vanishes, by termwise expansion of the exponential
    have hchar : ∀ ξ : EuclideanSpace ℝ (Fin n),
        ∫ x, Complex.exp (((inner ℝ ξ x : ℝ) : ℂ) * Complex.I) * (F x : ℂ)
          ∂(GaussMeasure n) = 0 := by
      intro ξ
      set G : ℕ → EuclideanSpace ℝ (Fin n) → ℂ := fun m x =>
        (((inner ℝ ξ x : ℝ) : ℂ) * Complex.I) ^ m / (Nat.factorial m : ℂ) * (F x : ℂ)
        with hGdef
      have hGalt : ∀ (m : ℕ) (x : EuclideanSpace ℝ (Fin n)),
          G m x = (Complex.I ^ m / (Nat.factorial m : ℂ))
            * ((((inner ℝ ξ x : ℝ) ^ m * F x : ℝ)) : ℂ) := by
        intro m x
        simp only [hGdef]
        push_cast
        ring
      have hGint : ∀ m, Integrable (G m) (GaussMeasure n) := by
        intro m
        refine (((hpow ξ m).1.ofReal (𝕜 := ℂ)).const_mul
          (Complex.I ^ m / (Nat.factorial m : ℂ))).congr ?_
        filter_upwards with x
        exact (hGalt m x).symm
      have hGnorm : ∀ (m : ℕ) (x : EuclideanSpace ℝ (Fin n)),
          ‖G m x‖ = |(inner ℝ ξ x : ℝ)| ^ m / (Nat.factorial m : ℝ) * |F x| := by
        intro m x
        simp only [hGdef, norm_mul, norm_div, norm_pow, Complex.norm_I, mul_one,
          Complex.norm_real, Complex.norm_natCast, Real.norm_eq_abs]
      have hGzero : ∀ m, ∫ x, G m x ∂(GaussMeasure n) = 0 := by
        intro m
        have h1 : ∫ x, G m x ∂(GaussMeasure n)
            = (Complex.I ^ m / (Nat.factorial m : ℂ))
              * ∫ x, ((((inner ℝ ξ x : ℝ) ^ m * F x : ℝ)) : ℂ) ∂(GaussMeasure n) := by
          rw [← integral_const_mul]
          exact integral_congr_ae (Filter.Eventually.of_forall fun x => hGalt m x)
        rw [h1, integral_complex_ofReal, (hpow ξ m).2]
        simp
      have hGsum : Summable (fun m => ∫ x, ‖G m x‖ ∂(GaussMeasure n)) := by
        refine summable_of_sum_le
          (c := ∫ x, Real.exp (‖ξ‖ * ‖x‖) * |F x| ∂(GaussMeasure n))
          (fun m => integral_nonneg (fun x => norm_nonneg _)) ?_
        intro s
        obtain ⟨N, hN⟩ := s.exists_nat_subset_range
        have hintnorm : ∀ m, Integrable (fun x => ‖G m x‖) (GaussMeasure n) :=
          fun m => (hGint m).norm
        rw [← integral_finsetSum s (fun m _ => hintnorm m)]
        refine integral_mono (integrable_finsetSum s (fun m _ => hintnorm m)) (hdom ‖ξ‖) ?_
        intro x
        dsimp only
        have habs : |(inner ℝ ξ x : ℝ)| ≤ ‖ξ‖ * ‖x‖ := abs_real_inner_le_norm ξ x
        have hstep : ∑ m ∈ s, ‖G m x‖
            = (∑ m ∈ s, |(inner ℝ ξ x : ℝ)| ^ m / (Nat.factorial m : ℝ)) * |F x| := by
          rw [Finset.sum_mul]
          exact Finset.sum_congr rfl fun m _ => hGnorm m x
        rw [hstep]
        have hpart : (∑ m ∈ s, |(inner ℝ ξ x : ℝ)| ^ m / (Nat.factorial m : ℝ))
            ≤ Real.exp (‖ξ‖ * ‖x‖) := by
          calc (∑ m ∈ s, |(inner ℝ ξ x : ℝ)| ^ m / (Nat.factorial m : ℝ))
              ≤ ∑ m ∈ Finset.range N, |(inner ℝ ξ x : ℝ)| ^ m / (Nat.factorial m : ℝ) :=
                Finset.sum_le_sum_of_subset_of_nonneg hN (fun m _ _ => by positivity)
            _ ≤ Real.exp |(inner ℝ ξ x : ℝ)| := Real.sum_le_exp_of_nonneg (abs_nonneg _) N
            _ ≤ Real.exp (‖ξ‖ * ‖x‖) := Real.exp_le_exp.mpr habs
        exact mul_le_mul_of_nonneg_right hpart (abs_nonneg _)
      have hHS := hasSum_integral_of_summable_integral_norm hGint hGsum
      rw [funext hGzero] at hHS
      have hval : ∫ x, ∑' m, G m x ∂(GaussMeasure n) = 0 := (hasSum_zero.unique hHS).symm
      rw [← hval]
      refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      dsimp only
      rw [show (∑' m, G m x)
          = (∑' m, (((inner ℝ ξ x : ℝ) : ℂ) * Complex.I) ^ m / (Nat.factorial m : ℂ))
            * (F x : ℂ) from tsum_mul_right]
      congr 1
      rw [Complex.exp_eq_exp_ℂ, NormedSpace.exp_eq_tsum_div]
    -- (6c) uniqueness of characteristic functions forces `F = 0` almost everywhere
    have hmp : Measurable (fun x => ENNReal.ofReal (F x)) := hFsm.measurable.ennreal_ofReal
    have hmm : Measurable (fun x => ENNReal.ofReal (-F x)) :=
      (hFsm.measurable.neg).ennreal_ofReal
    have hfp : IsFiniteMeasure ((GaussMeasure n).withDensity fun x => ENNReal.ofReal (F x)) :=
      isFiniteMeasure_withDensity_ofReal hFint.hasFiniteIntegral
    have hfm : IsFiniteMeasure ((GaussMeasure n).withDensity fun x => ENNReal.ofReal (-F x)) :=
      isFiniteMeasure_withDensity_ofReal hFint.neg.hasFiniteIntegral
    have hltp : ∀ᵐ x ∂(GaussMeasure n), ENNReal.ofReal (F x) < ⊤ := by
      filter_upwards with x; exact ENNReal.ofReal_lt_top
    have hltm : ∀ᵐ x ∂(GaussMeasure n), ENNReal.ofReal (-F x) < ⊤ := by
      filter_upwards with x; exact ENNReal.ofReal_lt_top
    have hIntPart : ∀ G : EuclideanSpace ℝ (Fin n) → ℝ, Measurable G →
        Integrable G (GaussMeasure n) →
        Integrable (fun x => (ENNReal.ofReal (G x)).toReal) (GaussMeasure n) := by
      intro G hGm hGi
      refine Integrable.mono' hGi.abs
        (hGm.ennreal_ofReal.ennreal_toReal).aestronglyMeasurable ?_
      filter_upwards with x
      rw [ENNReal.toReal_ofReal', Real.norm_eq_abs]
      rcases le_or_gt 0 (G x) with h | h
      · rw [max_eq_left h, abs_of_nonneg h]
      · rw [max_eq_right h.le]
        simp [abs_nonneg]
    have hdiff : ∀ x, (ENNReal.ofReal (F x)).toReal - (ENNReal.ofReal (-F x)).toReal = F x := by
      intro x
      rw [ENNReal.toReal_ofReal', ENNReal.toReal_ofReal']
      rcases le_or_gt 0 (F x) with h | h
      · rw [max_eq_left h, max_eq_right (by linarith)]; ring
      · rw [max_eq_right h.le, max_eq_left (by linarith)]; ring
    have hcf : charFun ((GaussMeasure n).withDensity fun x => ENNReal.ofReal (F x))
        = charFun ((GaussMeasure n).withDensity fun x => ENNReal.ofReal (-F x)) := by
      funext ξ
      rw [charFun_apply, charFun_apply,
        integral_withDensity_eq_integral_toReal_smul₀ hmp.aemeasurable hltp,
        integral_withDensity_eq_integral_toReal_smul₀ hmm.aemeasurable hltm]
      have hecont : Continuous (fun x : EuclideanSpace ℝ (Fin n) =>
          Complex.exp (((inner ℝ x ξ : ℝ) : ℂ) * Complex.I)) := by fun_prop
      have hIsm : ∀ G : EuclideanSpace ℝ (Fin n) → ℝ, Measurable G →
          AEStronglyMeasurable (fun x => (ENNReal.ofReal (G x)).toReal •
            Complex.exp (((inner ℝ x ξ : ℝ) : ℂ) * Complex.I)) (GaussMeasure n) := by
        intro G hGm
        exact (hGm.ennreal_ofReal.ennreal_toReal).aestronglyMeasurable.smul
          hecont.aestronglyMeasurable
      have hI : ∀ G : EuclideanSpace ℝ (Fin n) → ℝ, Measurable G →
          Integrable G (GaussMeasure n) →
          Integrable (fun x => (ENNReal.ofReal (G x)).toReal •
            Complex.exp (((inner ℝ x ξ : ℝ) : ℂ) * Complex.I)) (GaussMeasure n) := by
        intro G hGm hGi
        refine Integrable.mono' (hIntPart G hGm hGi).abs (hIsm G hGm) ?_
        filter_upwards with x
        rw [norm_smul, Complex.norm_exp_ofReal_mul_I, mul_one, Real.norm_eq_abs]
      rw [← sub_eq_zero, ← integral_sub (hI F hFsm.measurable hFint)
        (hI (fun x => -F x) hFsm.measurable.neg hFint.neg)]
      have hpt : ∀ x : EuclideanSpace ℝ (Fin n),
          (ENNReal.ofReal (F x)).toReal • Complex.exp (((inner ℝ x ξ : ℝ) : ℂ) * Complex.I)
            - (ENNReal.ofReal (-F x)).toReal
              • Complex.exp (((inner ℝ x ξ : ℝ) : ℂ) * Complex.I)
            = Complex.exp (((inner ℝ ξ x : ℝ) : ℂ) * Complex.I) * (F x : ℂ) := by
        intro x
        rw [← sub_smul, hdiff x, real_inner_comm ξ x, Complex.real_smul]
        ring
      rw [integral_congr_ae (Filter.Eventually.of_forall hpt)]
      exact hchar ξ
    have hmu : ((GaussMeasure n).withDensity fun x => ENNReal.ofReal (F x))
        = ((GaussMeasure n).withDensity fun x => ENNReal.ofReal (-F x)) :=
      Measure.ext_of_charFun hcf
    have hlint : ∫⁻ x, ENNReal.ofReal (F x) ∂(GaussMeasure n) ≠ ⊤ := by
      have h1 : ∀ x, ENNReal.ofReal (F x) ≤ ‖F x‖ₑ := by
        intro x
        rw [Real.enorm_eq_ofReal_abs]
        exact ENNReal.ofReal_le_ofReal (le_abs_self _)
      exact ne_of_lt (lt_of_le_of_lt (lintegral_mono h1) hFint.hasFiniteIntegral)
    have hae := (withDensity_eq_iff hmp.aemeasurable hmm.aemeasurable hlint).1 hmu
    have hF0 : F =ᵐ[GaussMeasure n] 0 := by
      filter_upwards [hae] with x hx
      simp only [Pi.zero_apply]
      rcases lt_trichotomy (F x) 0 with h | h | h
      · rw [ENNReal.ofReal_eq_zero.2 h.le] at hx
        exact absurd hx.symm (ne_of_gt (ENNReal.ofReal_pos.2 (by linarith)))
      · exact h
      · rw [ENNReal.ofReal_eq_zero.2 (by linarith : -F x ≤ 0)] at hx
        exact absurd hx (ne_of_gt (ENNReal.ofReal_pos.2 h))
    exact Lp.eq_zero_iff_ae_eq_zero.2 (hFae.trans hF0)
  rw [← Submodule.orthogonal_orthogonal_eq_closure, ← eq_top_iff,
    Submodule.orthogonal_eq_top_iff, horth]
