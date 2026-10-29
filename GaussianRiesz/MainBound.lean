module

public import GaussianRiesz.SignedDecomposition
public import GaussianRiesz.TransformedLocalization
public import GaussianRiesz.RieszL2Identity
public import GaussianRiesz.SmallLevelBound

@[expose] public section
open MeasureTheory
theorem MainBound {n : ℕ} (f : Lp ℝ 2 (GaussMeasure n)) (t : ℝ) (ht : 0 < t) :
    ENNReal.ofReal t * GaussMeasure n
        {x | t < ‖(RieszTransform f : EuclideanSpace ℝ (Fin n)
          → EuclideanSpace ℝ (Fin n)) x‖}
      ≤ ENNReal.ofReal (2 * ‖ToL1 f‖) := by
  have hM0 : (0 : ℝ) ≤ ‖ToL1 f‖ := norm_nonneg _
  rcases le_or_gt t ‖ToL1 f‖ with hle | hgt
  · -- small levels: the trivial bound already beats `2M`
    exact (SmallLevelBound _ t ‖ToL1 f‖ ht hle).trans
      (ENNReal.ofReal_le_ofReal (by linarith))
  · -- large levels: decompose, localize, and apply Chebyshev to the good part
    obtain ⟨u, hu, g, Ω, -, hdec, hΩbd, hgsup, hgL1, hgL2, hloc⟩ :=
      SignedDecomposition f t hgt
    obtain ⟨-, hmeas⟩ := TransformedLocalization f g u hu hdec t Ω hloc
    have hR2 : ‖RieszTransform g‖ ^ 2 ≤ t * ‖ToL1 f‖ := by
      have h1 := (RieszL2Identity g).2
      nlinarith [norm_nonneg (RieszTransform g), norm_nonneg g, hgL2]
    have ht0 : ENNReal.ofReal t ≠ 0 := (ENNReal.ofReal_pos.mpr ht).ne'
    have hcheb : ENNReal.ofReal t
        * GaussMeasure n {x | t < ‖(RieszTransform g : EuclideanSpace ℝ (Fin n)
            → EuclideanSpace ℝ (Fin n)) x‖}
        ≤ ENNReal.ofReal ‖ToL1 f‖ := by
      have hch := mul_meas_ge_le_pow_eLpNorm' (GaussMeasure n) (p := 2)
        (by norm_num) (by norm_num)
        (f := (RieszTransform g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)))
        (ENNReal.ofReal t)
      rw [show ((2 : ENNReal)).toReal = (2 : ℝ) from by norm_num] at hch
      have heL : eLpNorm ((RieszTransform g : EuclideanSpace ℝ (Fin n)
          → EuclideanSpace ℝ (Fin n))) 2 (GaussMeasure n)
          = ENNReal.ofReal ‖RieszTransform g‖ := by
        rw [Lp.norm_def, ENNReal.ofReal_toReal (Lp.eLpNorm_ne_top _)]
      rw [heL, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) (by norm_num),
        ENNReal.ofReal_rpow_of_nonneg ht.le (by norm_num)] at hch
      have hsub : GaussMeasure n {x | t < ‖(RieszTransform g : EuclideanSpace ℝ (Fin n)
            → EuclideanSpace ℝ (Fin n)) x‖}
          ≤ GaussMeasure n {x | ENNReal.ofReal t
            ≤ ‖(RieszTransform g : EuclideanSpace ℝ (Fin n)
              → EuclideanSpace ℝ (Fin n)) x‖ₑ} := by
        refine measure_mono fun x hx => ?_
        have hx' : t < ‖(RieszTransform g : EuclideanSpace ℝ (Fin n)
            → EuclideanSpace ℝ (Fin n)) x‖ := hx
        show ENNReal.ofReal t ≤ _
        rw [← ofReal_norm]
        exact ENNReal.ofReal_le_ofReal hx'.le
      refine (ENNReal.mul_le_mul_iff_right ht0 ENNReal.ofReal_ne_top).mp ?_
      rw [← mul_assoc, ← ENNReal.ofReal_mul ht.le, ← ENNReal.ofReal_mul ht.le]
      calc ENNReal.ofReal (t * t)
            * GaussMeasure n {x | t < ‖(RieszTransform g : EuclideanSpace ℝ (Fin n)
              → EuclideanSpace ℝ (Fin n)) x‖}
          ≤ ENNReal.ofReal (t * t)
              * GaussMeasure n {x | ENNReal.ofReal t
                ≤ ‖(RieszTransform g : EuclideanSpace ℝ (Fin n)
                  → EuclideanSpace ℝ (Fin n)) x‖ₑ} := by gcongr
        _ ≤ ENNReal.ofReal (‖RieszTransform g‖ ^ (2 : ℝ)) := by
              have h2 : t * t = t ^ (2 : ℝ) := by
                rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) from by norm_num, Real.rpow_natCast]
                ring
              rw [h2]; exact hch
        _ ≤ ENNReal.ofReal (t * ‖ToL1 f‖) := by
              refine ENNReal.ofReal_le_ofReal ?_
              rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) from by norm_num, Real.rpow_natCast]
              exact hR2
    calc ENNReal.ofReal t
          * GaussMeasure n {x | t < ‖(RieszTransform f : EuclideanSpace ℝ (Fin n)
            → EuclideanSpace ℝ (Fin n)) x‖}
        ≤ ENNReal.ofReal t * (GaussMeasure n Ω
            + GaussMeasure n {x | t < ‖(RieszTransform g : EuclideanSpace ℝ (Fin n)
              → EuclideanSpace ℝ (Fin n)) x‖}) := by gcongr
      _ = ENNReal.ofReal t * GaussMeasure n Ω
            + ENNReal.ofReal t
              * GaussMeasure n {x | t < ‖(RieszTransform g : EuclideanSpace ℝ (Fin n)
                → EuclideanSpace ℝ (Fin n)) x‖} := mul_add _ _ _
      _ ≤ ENNReal.ofReal ‖ToL1 f‖ + ENNReal.ofReal ‖ToL1 f‖ := add_le_add hΩbd hcheb
      _ = ENNReal.ofReal (2 * ‖ToL1 f‖) := by
            rw [← ENNReal.ofReal_add hM0 hM0]
            congr 1
            ring
