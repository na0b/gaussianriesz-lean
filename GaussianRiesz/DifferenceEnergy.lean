import GaussianRiesz.SemigroupEnergy
import GaussianRiesz.OUCouplingKernel
open MeasureTheory Set
theorem DifferenceEnergy {n : ℕ} (v : Lp ℝ 2 (GaussMeasure n)) :
    (∀ s : ℝ, 0 < s →
        Integrable (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
          ((v : EuclideanSpace ℝ (Fin n) → ℝ) p.1
            - (v : EuclideanSpace ℝ (Fin n) → ℝ) p.2) ^ 2) (OUCoupling n s))
      ∧ (∀ s : ℝ, 0 < s →
          (∫ p, ((v : EuclideanSpace ℝ (Fin n) → ℝ) p.1
            - (v : EuclideanSpace ℝ (Fin n) → ℝ) p.2) ^ 2 ∂(OUCoupling n s))
              ≤ 4 * ‖v‖ ^ 2)
      ∧ Energy v = ENNReal.ofReal (1 / (4 * Real.sqrt Real.pi))
          * ∫⁻ s in Set.Ioi (0 : ℝ),
              ENNReal.ofReal ((∫ p, ((v : EuclideanSpace ℝ (Fin n) → ℝ) p.1
                - (v : EuclideanSpace ℝ (Fin n) → ℝ) p.2) ^ 2 ∂(OUCoupling n s))
                  / s ^ ((3 : ℝ) / 2)) := by
  classical
  have hmul : ∀ a b : ℝ, (inner ℝ a b : ℝ) = a * b := by
    intro a b; simp [RCLike.inner_apply, mul_comm]
  -- the squared norm as a Gaussian integral
  have hnormsq : ∫ x, ((v : EuclideanSpace ℝ (Fin n) → ℝ) x) ^ 2 ∂(GaussMeasure n)
      = ‖v‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, L2.inner_def]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [hmul]
    ring
  have hvsq : AEStronglyMeasurable
      (fun x : EuclideanSpace ℝ (Fin n) => ((v : EuclideanSpace ℝ (Fin n) → ℝ) x) ^ 2)
      (GaussMeasure n) := (Lp.aestronglyMeasurable v).pow 2
  -- per-`s` package
  have key : ∀ s : ℝ, 0 < s →
      Integrable (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
          ((v : EuclideanSpace ℝ (Fin n) → ℝ) p.1
            - (v : EuclideanSpace ℝ (Fin n) → ℝ) p.2) ^ 2) (OUCoupling n s)
        ∧ (∫ p, ((v : EuclideanSpace ℝ (Fin n) → ℝ) p.1
              - (v : EuclideanSpace ℝ (Fin n) → ℝ) p.2) ^ 2 ∂(OUCoupling n s)) ≤ 4 * ‖v‖ ^ 2
        ∧ (∫ p, ((v : EuclideanSpace ℝ (Fin n) → ℝ) p.1
              - (v : EuclideanSpace ℝ (Fin n) → ℝ) p.2) ^ 2 ∂(OUCoupling n s))
            = 2 * (inner ℝ (v - OUSemigroup s v) v : ℝ) := by
    intro s hs
    obtain ⟨hprob, hswap, hfst, hsnd, hrep⟩ := OUCouplingKernel s hs
    -- pull integrals back along the two marginals
    have hpullf : ∀ g : EuclideanSpace ℝ (Fin n) → ℝ,
        AEStronglyMeasurable g (GaussMeasure n) →
        ∫ p, g p.1 ∂(OUCoupling n s) = ∫ x, g x ∂(GaussMeasure n) := by
      intro g hg
      have h := integral_map (μ := OUCoupling n s)
        (φ := (Prod.fst : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) → _))
        measurable_fst.aemeasurable (f := g) (by rw [hfst]; exact hg)
      rw [hfst] at h
      exact h.symm
    have hpulls : ∀ g : EuclideanSpace ℝ (Fin n) → ℝ,
        AEStronglyMeasurable g (GaussMeasure n) →
        ∫ p, g p.2 ∂(OUCoupling n s) = ∫ x, g x ∂(GaussMeasure n) := by
      intro g hg
      have h := integral_map (μ := OUCoupling n s)
        (φ := (Prod.snd : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) → _))
        measurable_snd.aemeasurable (f := g) (by rw [hsnd]; exact hg)
      rw [hsnd] at h
      exact h.symm
    -- the two coordinate pullbacks are in `L²(ν_s)`
    have hmpf : MeasurePreserving (Prod.fst :
        EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
        (OUCoupling n s) (GaussMeasure n) := ⟨measurable_fst, hfst⟩
    have hmps : MeasurePreserving (Prod.snd :
        EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
        (OUCoupling n s) (GaussMeasure n) := ⟨measurable_snd, hsnd⟩
    have hL1 : MemLp (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
        (v : EuclideanSpace ℝ (Fin n) → ℝ) p.1) 2 (OUCoupling n s) :=
      (Lp.memLp v).comp_measurePreserving hmpf
    have hL2 : MemLp (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
        (v : EuclideanSpace ℝ (Fin n) → ℝ) p.2) 2 (OUCoupling n s) :=
      (Lp.memLp v).comp_measurePreserving hmps
    -- (1) integrability of the difference square
    have hdiff : MemLp (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
        (v : EuclideanSpace ℝ (Fin n) → ℝ) p.1
          - (v : EuclideanSpace ℝ (Fin n) → ℝ) p.2) 2 (OUCoupling n s) := hL1.sub hL2
    have hint : Integrable (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
        ((v : EuclideanSpace ℝ (Fin n) → ℝ) p.1
          - (v : EuclideanSpace ℝ (Fin n) → ℝ) p.2) ^ 2) (OUCoupling n s) :=
      (memLp_two_iff_integrable_sq hdiff.1).mp hdiff
    -- the two square integrals
    have hsq1 : Integrable (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
        ((v : EuclideanSpace ℝ (Fin n) → ℝ) p.1) ^ 2) (OUCoupling n s) :=
      (memLp_two_iff_integrable_sq hL1.1).mp hL1
    have hsq2 : Integrable (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
        ((v : EuclideanSpace ℝ (Fin n) → ℝ) p.2) ^ 2) (OUCoupling n s) :=
      (memLp_two_iff_integrable_sq hL2.1).mp hL2
    have hv1 : ∫ p, ((v : EuclideanSpace ℝ (Fin n) → ℝ) p.1) ^ 2 ∂(OUCoupling n s)
        = ‖v‖ ^ 2 := by rw [hpullf _ hvsq, hnormsq]
    have hv2 : ∫ p, ((v : EuclideanSpace ℝ (Fin n) → ℝ) p.2) ^ 2 ∂(OUCoupling n s)
        = ‖v‖ ^ 2 := by rw [hpulls _ hvsq, hnormsq]
    refine ⟨hint, ?_, ?_⟩
    · -- (2) the bound
      have hdom : Integrable (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
          2 * (((v : EuclideanSpace ℝ (Fin n) → ℝ) p.1) ^ 2
            + ((v : EuclideanSpace ℝ (Fin n) → ℝ) p.2) ^ 2)) (OUCoupling n s) :=
        ((hsq1.add hsq2).const_mul 2).congr (Filter.Eventually.of_forall fun p => rfl)
      have hptwise : ∀ p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n),
          ((v : EuclideanSpace ℝ (Fin n) → ℝ) p.1
            - (v : EuclideanSpace ℝ (Fin n) → ℝ) p.2) ^ 2
            ≤ 2 * (((v : EuclideanSpace ℝ (Fin n) → ℝ) p.1) ^ 2
              + ((v : EuclideanSpace ℝ (Fin n) → ℝ) p.2) ^ 2) := by
        intro p
        nlinarith [sq_nonneg ((v : EuclideanSpace ℝ (Fin n) → ℝ) p.1
          + (v : EuclideanSpace ℝ (Fin n) → ℝ) p.2)]
      have hle := integral_mono hint hdom hptwise
      rw [integral_const_mul, integral_add hsq1 hsq2, hv1, hv2] at hle
      linarith
    · -- (3) the expansion
      have hmix := (hrep v v).2
      have hmixint := (hrep v v).1
      have hexp : ∫ p, ((v : EuclideanSpace ℝ (Fin n) → ℝ) p.1
            - (v : EuclideanSpace ℝ (Fin n) → ℝ) p.2) ^ 2 ∂(OUCoupling n s)
          = (∫ p, ((v : EuclideanSpace ℝ (Fin n) → ℝ) p.1) ^ 2 ∂(OUCoupling n s))
            + (∫ p, ((v : EuclideanSpace ℝ (Fin n) → ℝ) p.2) ^ 2 ∂(OUCoupling n s))
            - 2 * ∫ p, (v : EuclideanSpace ℝ (Fin n) → ℝ) p.2
                * (v : EuclideanSpace ℝ (Fin n) → ℝ) p.1 ∂(OUCoupling n s) := by
        have e1 : ∫ p, ((v : EuclideanSpace ℝ (Fin n) → ℝ) p.1
                - (v : EuclideanSpace ℝ (Fin n) → ℝ) p.2) ^ 2 ∂(OUCoupling n s)
            = ∫ p, (((v : EuclideanSpace ℝ (Fin n) → ℝ) p.1) ^ 2
                + ((v : EuclideanSpace ℝ (Fin n) → ℝ) p.2) ^ 2
                - 2 * ((v : EuclideanSpace ℝ (Fin n) → ℝ) p.2
                  * (v : EuclideanSpace ℝ (Fin n) → ℝ) p.1)) ∂(OUCoupling n s) :=
          integral_congr_ae (Filter.Eventually.of_forall fun p => by ring)
        have hsum12 : Integrable (fun p : EuclideanSpace ℝ (Fin n)
                × EuclideanSpace ℝ (Fin n) =>
              ((v : EuclideanSpace ℝ (Fin n) → ℝ) p.1) ^ 2
                + ((v : EuclideanSpace ℝ (Fin n) → ℝ) p.2) ^ 2) (OUCoupling n s) :=
          (hsq1.add hsq2).congr (Filter.Eventually.of_forall fun p => rfl)
        rw [e1, integral_sub hsum12 (hmixint.const_mul 2),
          integral_add hsq1 hsq2, integral_const_mul]
      rw [hexp, hv1, hv2, ← hmix]
      have : (inner ℝ (v - OUSemigroup s v) v : ℝ)
          = (inner ℝ v v : ℝ) - (inner ℝ (OUSemigroup s v) v : ℝ) := by
        rw [inner_sub_left]
      rw [this, real_inner_self_eq_norm_sq]
      ring
  refine ⟨fun s hs => (key s hs).1, fun s hs => (key s hs).2.1, ?_⟩
  -- substitute the difference integral into `SemigroupEnergy`
  rw [SemigroupEnergy v]
  have hY : ∫⁻ s in Ioi (0:ℝ), ENNReal.ofReal
        ((∫ p, ((v : EuclideanSpace ℝ (Fin n) → ℝ) p.1
          - (v : EuclideanSpace ℝ (Fin n) → ℝ) p.2) ^ 2 ∂(OUCoupling n s))
            / s ^ ((3:ℝ)/2))
      = ENNReal.ofReal 2 * ∫⁻ s in Ioi (0:ℝ), ENNReal.ofReal
          ((inner ℝ (v - OUSemigroup s v) v : ℝ) / s ^ ((3:ℝ)/2)) := by
    rw [← lintegral_const_mul' (ENNReal.ofReal 2) _ (by simp)]
    refine lintegral_congr_ae ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    have hs0 : (0:ℝ) < s := hs
    rw [(key s hs0).2.2, ← ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2)]
    congr 1
    ring
  rw [hY, ← mul_assoc,
    ← ENNReal.ofReal_mul (show (0:ℝ) ≤ 1 / (4 * Real.sqrt Real.pi) by positivity),
    show 1 / (4 * Real.sqrt Real.pi) * 2 = 1 / (2 * Real.sqrt Real.pi) from by
      have hpi : Real.sqrt Real.pi ≠ 0 := by positivity
      field_simp
      norm_num]
