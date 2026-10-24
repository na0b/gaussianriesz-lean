import GaussianRiesz.DifferenceEnergy
open MeasureTheory
-- binder retained for statement fidelity to the paper; intentionally unused in the proof
set_option linter.unusedVariables false
theorem LatticeContraction {n : ℕ} (Φ : ℝ → ℝ) (hL : LipschitzWith 1 Φ) (hΦ : Φ 0 = 0)
    (v w : Lp ℝ 2 (GaussMeasure n)) (hv : Energy v ≠ ⊤)
    (hw : (w : EuclideanSpace ℝ (Fin n) → ℝ)
      =ᵐ[GaussMeasure n] fun x => Φ ((v : EuclideanSpace ℝ (Fin n) → ℝ) x)) :
    Energy w ≠ ⊤ ∧ Energy w ≤ Energy v := by
  classical
  -- the Lipschitz bound, in the form the pointwise estimate consumes
  have hlip : ∀ a b : ℝ, |Φ a - Φ b| ≤ |a - b| := by
    intro a b
    have h := hL.dist_le_mul a b
    simpa [Real.dist_eq] using h
  obtain ⟨hwint, -, hweq⟩ := DifferenceEnergy w
  obtain ⟨hvint, -, hveq⟩ := DifferenceEnergy v
  -- per-`s` monotonicity of the difference integral
  have hmono : ∀ s : ℝ, 0 < s →
      (∫ p, ((w : EuclideanSpace ℝ (Fin n) → ℝ) p.1
          - (w : EuclideanSpace ℝ (Fin n) → ℝ) p.2) ^ 2 ∂(OUCoupling n s))
        ≤ ∫ p, ((v : EuclideanSpace ℝ (Fin n) → ℝ) p.1
          - (v : EuclideanSpace ℝ (Fin n) → ℝ) p.2) ^ 2 ∂(OUCoupling n s) := by
    intro s hs
    obtain ⟨-, -, hfst, hsnd, -⟩ := OUCouplingKernel s hs
    have hmpf : MeasurePreserving (Prod.fst :
        EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
        (OUCoupling n s) (GaussMeasure n) := ⟨measurable_fst, hfst⟩
    have hmps : MeasurePreserving (Prod.snd :
        EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
        (OUCoupling n s) (GaussMeasure n) := ⟨measurable_snd, hsnd⟩
    have h1 := hmpf.quasiMeasurePreserving.ae hw
    have h2 := hmps.quasiMeasurePreserving.ae hw
    refine integral_mono_ae (hwint s hs) (hvint s hs) ?_
    filter_upwards [h1, h2] with p hp1 hp2
    rw [hp1, hp2, ← sq_abs (Φ ((v : EuclideanSpace ℝ (Fin n) → ℝ) p.1)
        - Φ ((v : EuclideanSpace ℝ (Fin n) → ℝ) p.2)),
      ← sq_abs ((v : EuclideanSpace ℝ (Fin n) → ℝ) p.1
        - (v : EuclideanSpace ℝ (Fin n) → ℝ) p.2)]
    exact pow_le_pow_left₀ (abs_nonneg _) (hlip _ _) 2
  -- transport through the difference-energy representation
  have hle : Energy w ≤ Energy v := by
    have hli : (∫⁻ s in Set.Ioi (0 : ℝ),
          ENNReal.ofReal ((∫ p, ((w : EuclideanSpace ℝ (Fin n) → ℝ) p.1
            - (w : EuclideanSpace ℝ (Fin n) → ℝ) p.2) ^ 2 ∂(OUCoupling n s))
              / s ^ ((3 : ℝ) / 2)))
        ≤ ∫⁻ s in Set.Ioi (0 : ℝ),
          ENNReal.ofReal ((∫ p, ((v : EuclideanSpace ℝ (Fin n) → ℝ) p.1
            - (v : EuclideanSpace ℝ (Fin n) → ℝ) p.2) ^ 2 ∂(OUCoupling n s))
              / s ^ ((3 : ℝ) / 2)) := by
      refine lintegral_mono_ae ((ae_restrict_iff' measurableSet_Ioi).mpr
        (Filter.Eventually.of_forall fun s hs => ?_))
      have hs' : (0 : ℝ) < s := hs
      have hsp : (0 : ℝ) ≤ (s ^ ((3 : ℝ) / 2))⁻¹ :=
        inv_nonneg.mpr (Real.rpow_nonneg hs'.le _)
      refine ENNReal.ofReal_le_ofReal ?_
      simp only [div_eq_mul_inv]
      exact mul_le_mul_of_nonneg_right (hmono s hs') hsp
    rw [hweq, hveq]
    exact mul_le_mul_of_nonneg_left hli zero_le
  exact ⟨ne_top_of_le_ne_top hv hle, hle⟩
