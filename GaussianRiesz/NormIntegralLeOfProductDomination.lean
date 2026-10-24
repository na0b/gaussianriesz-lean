import GaussianRiesz.Preamble
open MeasureTheory
open scoped ENNReal
theorem NormIntegralLeOfProductDomination {n : ℕ} (K : Set (EuclideanSpace ℝ (Fin n)))
    (h a b : EuclideanSpace ℝ (Fin n) → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (ha : MemLp a 2 (volume.restrict K)) (hb : MemLp b 2 (volume.restrict K))
    (hbound : ∀ x, |h x| ≤ C * (|a x| * |b x|)) :
    ‖∫ x in K, h x‖ ≤ C * ((eLpNorm a 2 (volume.restrict K)).toReal
      * (eLpNorm b 2 (volume.restrict K)).toReal) := by
  -- Cauchy–Schwarz on a compact set for Lebesgue measure.
  have holderK : ∀ (K : Set (EuclideanSpace ℝ (Fin n)))
      (a b : EuclideanSpace ℝ (Fin n) → ℝ),
      MemLp a 2 (volume.restrict K) → MemLp b 2 (volume.restrict K) →
      ∫ x in K, |a x| * |b x| ≤ (eLpNorm a 2 (volume.restrict K)).toReal
        * (eLpNorm b 2 (volume.restrict K)).toReal := by
    intro K a b ha hb
    have hab : MemLp (fun x => a x * b x) 1 (volume.restrict K) := hb.mul' ha
    have hint : Integrable (fun x => a x * b x) (volume.restrict K) :=
      memLp_one_iff_integrable.1 hab
    have hnorm : ∀ x, ‖a x * b x‖ = |a x| * |b x| := by
      intro x; rw [Real.norm_eq_abs, abs_mul]
    have h1 : ENNReal.ofReal (∫ x in K, |a x| * |b x|)
        = eLpNorm (fun x => a x * b x) 1 (volume.restrict K) := by
      rw [eLpNorm_one_eq_lintegral_enorm]
      rw [show (∫ x in K, |a x| * |b x|) = ∫ x in K, ‖a x * b x‖ from
        integral_congr_ae (Filter.Eventually.of_forall fun x => (hnorm x).symm)]
      exact ofReal_integral_norm_eq_lintegral_enorm hint
    have h2 : eLpNorm (fun x => a x * b x) 1 (volume.restrict K)
        ≤ eLpNorm a 2 (volume.restrict K) * eLpNorm b 2 (volume.restrict K) := by
      have hraw := eLpNorm_smul_le_mul_eLpNorm (p := (2:ℝ≥0∞)) (q := (2:ℝ≥0∞)) (r := (1:ℝ≥0∞))
        (μ := volume.restrict K) hb.1 ha.1
      have hcong : eLpNorm (fun x => a x * b x) 1 (volume.restrict K)
          = eLpNorm (a • b) 1 (volume.restrict K) :=
        eLpNorm_congr_ae (Filter.Eventually.of_forall fun x => rfl)
      rw [hcong]
      exact hraw
    have hfin : eLpNorm a 2 (volume.restrict K) * eLpNorm b 2 (volume.restrict K) ≠ ⊤ :=
      ENNReal.mul_ne_top ha.eLpNorm_ne_top hb.eLpNorm_ne_top
    have h3 : ∫ x in K, |a x| * |b x|
        = (eLpNorm (fun x => a x * b x) 1 (volume.restrict K)).toReal := by
      rw [← h1, ENNReal.toReal_ofReal]
      exact integral_nonneg fun x => by positivity
    rw [h3, ← ENNReal.toReal_mul]
    exact ENNReal.toReal_mono hfin h2
  have hab : MemLp (fun x => a x * b x) 1 (volume.restrict K) := hb.mul' ha
  have habint : Integrable (fun x => a x * b x) (volume.restrict K) :=
    memLp_one_iff_integrable.1 hab
  have habs : Integrable (fun x => |a x| * |b x|) (volume.restrict K) := by
    refine (habint.abs).congr (Filter.Eventually.of_forall fun x => ?_)
    show |a x * b x| = |a x| * |b x|
    rw [abs_mul]
  refine le_trans (norm_integral_le_integral_norm _) ?_
  refine le_trans (integral_mono_of_nonneg
    (Filter.Eventually.of_forall fun x => norm_nonneg _)
    (habs.const_mul C)
    (Filter.Eventually.of_forall fun x => ?_)) ?_
  · show ‖h x‖ ≤ C * (|a x| * |b x|)
    rw [Real.norm_eq_abs]
    exact hbound x
  · rw [integral_const_mul]
    exact mul_le_mul_of_nonneg_left (holderK K a b ha hb) hC
