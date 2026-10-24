import GaussianRiesz.GaussLebesgueBallComparison
open MeasureTheory
theorem GaussLebesgueL1DensityTransfer {n : ℕ} (v : Lp ℝ 1 (GaussMeasure n)) :
    Integrable (fun y => Real.exp (-‖y‖ ^ 2) * |(v : EuclideanSpace ℝ (Fin n) → ℝ) y|)
        (volume : Measure (EuclideanSpace ℝ (Fin n)))
      ∧ (∫ y, Real.exp (-‖y‖ ^ 2) * |(v : EuclideanSpace ℝ (Fin n) → ℝ) y|)
          ≤ Real.pi ^ ((n : ℝ) / 2)
            * ∫ y, |(v : EuclideanSpace ℝ (Fin n) → ℝ) y| ∂(GaussMeasure n) := by
  classical
  set F : EuclideanSpace ℝ (Fin n) → ℝ := (v : EuclideanSpace ℝ (Fin n) → ℝ) with hFdef
  obtain ⟨q, hq0, hqdef⟩ : ∃ q : ℝ, 0 < q ∧ q = Real.pi ^ ((n : ℝ) / 2) :=
    ⟨_, Real.rpow_pos_of_pos Real.pi_pos _, rfl⟩
  have hFm : AEStronglyMeasurable F (GaussMeasure n) := Lp.aestronglyMeasurable v
  have hacv : (volume : Measure (EuclideanSpace ℝ (Fin n))) ≪ GaussMeasure n := by
    have h4 := (GaussLebesgueBallComparison (n := n)).2.2.2
    exact Measure.AbsolutelyContinuous.mk fun s _ hs0 => (h4 s).1 hs0
  have hFmv : AEStronglyMeasurable F (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
    obtain ⟨g, hg, hgae⟩ := hFm
    exact ⟨g, hg, hacv.ae_eq hgae⟩
  have hdens : AEMeasurable (fun y : EuclideanSpace ℝ (Fin n) =>
      ENNReal.ofReal (Real.pi ^ (-(n : ℝ) / 2) * Real.exp (-‖y‖ ^ 2))) volume := by
    fun_prop
  have hFmem : MemLp F 1 (GaussMeasure n) := Lp.memLp v
  have hlin : ∫⁻ y, ‖Real.exp (-‖y‖ ^ 2) * F y‖ₑ ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))
      = ENNReal.ofReal q * ∫⁻ y, ‖F y‖ₑ ∂(GaussMeasure n) := by
    rw [hqdef, GaussMeasure, lintegral_withDensity_eq_lintegral_mul₀ hdens hFmv.enorm,
      ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine lintegral_congr fun y => ?_
    have hpy : Real.pi ^ (-(n : ℝ) / 2) * Real.exp (-‖y‖ ^ 2)
        = (Real.pi ^ ((n:ℝ)/2))⁻¹ * Real.exp (-‖y‖ ^ 2) := by
      rw [show (-(n : ℝ) / 2) = -((n:ℝ)/2) from by ring, Real.rpow_neg Real.pi_pos.le]
    have hpipos : (0:ℝ) < Real.pi ^ ((n:ℝ)/2) := Real.rpow_pos_of_pos Real.pi_pos _
    simp only [Pi.mul_apply, hpy]
    have hrhs : ENNReal.ofReal (Real.pi ^ ((n:ℝ)/2))
          * (ENNReal.ofReal ((Real.pi ^ ((n:ℝ)/2))⁻¹ * Real.exp (-‖y‖ ^ 2)) * ‖F y‖ₑ)
        = ENNReal.ofReal (Real.exp (-‖y‖ ^ 2) * |F y|) := by
      rw [Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_mul (by positivity),
        ← ENNReal.ofReal_mul (by positivity)]
      congr 1
      field_simp
    rw [Real.enorm_eq_ofReal_abs, abs_mul, abs_of_pos (Real.exp_pos _), hrhs]
  have hFint : Integrable F (GaussMeasure n) := memLp_one_iff_integrable.1 hFmem
  have hfin : ∫⁻ y, ‖Real.exp (-‖y‖ ^ 2) * F y‖ₑ
      ∂(volume : Measure (EuclideanSpace ℝ (Fin n))) ≠ ⊤ := by
    rw [hlin, show ∫⁻ y, ‖F y‖ₑ ∂(GaussMeasure n) = eLpNorm F 1 (GaussMeasure n) from by
      rw [eLpNorm_one_eq_lintegral_enorm]]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hFmem.2.ne
  have hint0 : Integrable (fun y => Real.exp (-‖y‖ ^ 2) * F y)
      (volume : Measure (EuclideanSpace ℝ (Fin n))) :=
    ⟨(Real.continuous_exp.comp ((continuous_id.norm.pow 2).neg)).aestronglyMeasurable.mul hFmv,
      lt_of_le_of_ne le_top hfin⟩
  have habs : ∀ y : EuclideanSpace ℝ (Fin n),
      Real.exp (-‖y‖ ^ 2) * |F y| = |Real.exp (-‖y‖ ^ 2) * F y| := fun y => by
    rw [abs_mul, abs_of_pos (Real.exp_pos _)]
  have hexpF : Integrable (fun y => Real.exp (-‖y‖ ^ 2) * |F y|)
      (volume : Measure (EuclideanSpace ℝ (Fin n))) :=
    hint0.abs.congr (Filter.Eventually.of_forall fun y => (habs y).symm)
  have hN0 : (0:ℝ) ≤ ∫ y, |F y| ∂(GaussMeasure n) := integral_nonneg fun y => abs_nonneg _
  have hexpbd : (∫ y, Real.exp (-‖y‖ ^ 2) * |F y|) ≤ q * ∫ y, |F y| ∂(GaussMeasure n) := by
    refine le_of_eq ?_
    have hcomb : ENNReal.ofReal (∫ y, ‖Real.exp (-‖y‖ ^ 2) * F y‖
          ∂(volume : Measure (EuclideanSpace ℝ (Fin n))))
        = ENNReal.ofReal (q * ∫ y, ‖F y‖ ∂(GaussMeasure n)) := by
      rw [ofReal_integral_norm_eq_lintegral_enorm hint0, hlin,
        ← ofReal_integral_norm_eq_lintegral_enorm hFint, ← ENNReal.ofReal_mul hq0.le]
    have heq := (ENNReal.ofReal_eq_ofReal_iff (integral_nonneg fun y => norm_nonneg _)
      (by positivity)).1 hcomb
    calc (∫ y, Real.exp (-‖y‖ ^ 2) * |F y|)
        = ∫ y, ‖Real.exp (-‖y‖ ^ 2) * F y‖ := by
          refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
          show Real.exp (-‖y‖ ^ 2) * |F y| = ‖Real.exp (-‖y‖ ^ 2) * F y‖
          rw [Real.norm_eq_abs, habs y]
      _ = q * ∫ y, ‖F y‖ ∂(GaussMeasure n) := heq
      _ = q * ∫ y, |F y| ∂(GaussMeasure n) := by simp [Real.norm_eq_abs]
  rw [hqdef] at hexpbd
  exact ⟨hexpF, hexpbd⟩
