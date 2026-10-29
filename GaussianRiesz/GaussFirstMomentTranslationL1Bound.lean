module

public import GaussianRiesz.GaussEuclideanMomentBounds
public import GaussianRiesz.GaussSecondMomentIntegralBound

@[expose] public section
open MeasureTheory
theorem GaussFirstMomentTranslationL1Bound {n : ℕ} (j : Fin n) :
    ∀ b c : ℝ, 0 < b → 0 ≤ c → ∀ d : EuclideanSpace ℝ (Fin n),
      ∫ z : EuclideanSpace ℝ (Fin n),
          |c * ((z + d) j) * Real.exp (-b * ‖z + d‖ ^ 2)
            - c * (z j) * Real.exp (-b * ‖z‖ ^ 2)|
        ≤ c * ‖d‖ * ((Real.pi / b) ^ ((n : ℝ) / 2) * (5 + 24 * (8 : ℝ) ^ ((n : ℝ) / 2))) := by
  classical
  obtain ⟨gint, gval, coordle, -, -, -⟩ := GaussEuclideanMomentBounds (n := n)

  have gsq := fun (b : ℝ) (hb : 0 < b) => (GaussSecondMomentIntegralBound (n := n) b hb).2

  -- the exponential difference bound
  have expdiff : ∀ a b m : ℝ, m ≤ a → m ≤ b →
      |Real.exp (-a) - Real.exp (-b)| ≤ |a - b| * Real.exp (-m) := by
    intro a b m ha hb
    rcases le_total a b with h | h
    · have h1 : Real.exp (-b) ≤ Real.exp (-a) := Real.exp_le_exp.mpr (by linarith)
      have h2 : (1 : ℝ) - Real.exp (-(b - a)) ≤ b - a := by
        linarith [Real.add_one_le_exp (-(b - a))]
      have h3 : Real.exp (-b) = Real.exp (-a) * Real.exp (-(b - a)) := by
        rw [← Real.exp_add]; ring_nf
      have h4 : Real.exp (-a) ≤ Real.exp (-m) := Real.exp_le_exp.mpr (by linarith)
      have h5 : (0 : ℝ) < Real.exp (-a) := Real.exp_pos _
      rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ Real.exp (-a) - Real.exp (-b)),
        abs_of_nonpos (by linarith : a - b ≤ 0), h3]
      nlinarith
    · have h1 : Real.exp (-a) ≤ Real.exp (-b) := Real.exp_le_exp.mpr (by linarith)
      have h2 : (1 : ℝ) - Real.exp (-(a - b)) ≤ a - b := by
        linarith [Real.add_one_le_exp (-(a - b))]
      have h3 : Real.exp (-a) = Real.exp (-b) * Real.exp (-(a - b)) := by
        rw [← Real.exp_add]; ring_nf
      have h4 : Real.exp (-b) ≤ Real.exp (-m) := Real.exp_le_exp.mpr (by linarith)
      have h5 : (0 : ℝ) < Real.exp (-b) := Real.exp_pos _
      rw [abs_of_nonpos (by linarith : Real.exp (-a) - Real.exp (-b) ≤ 0),
        abs_of_nonneg (by linarith : (0:ℝ) ≤ a - b), h3]
      nlinarith


  intro b c hb hc d
  have htri : ∀ u v : ℝ, |u + v| ≤ |u| + |v| := fun u v => by simpa using norm_add_le u v
  have htri' : ∀ u v : ℝ, |u - v| ≤ |u| + |v| := fun u v => by simpa using norm_sub_le u v
  have hb4 : (0 : ℝ) < b / 4 := by positivity
  have hd0 : (0 : ℝ) ≤ ‖d‖ := norm_nonneg _
  set E : EuclideanSpace ℝ (Fin n) → ℝ := fun z => Real.exp (-b * ‖z‖ ^ 2) with hE
  have hEpos : ∀ z, (0 : ℝ) < E z := fun z => Real.exp_pos _
  have hIE : Integrable E volume := gint b hb
  have hIEd : Integrable (fun z : EuclideanSpace ℝ (Fin n) => E (z + d)) volume := by
    have h := ((measurePreserving_add_right
      (volume : Measure (EuclideanSpace ℝ (Fin n))) d).integrable_comp_emb
      (measurableEmbedding_addRight d)).mpr hIE
    simpa [Function.comp_def] using h
  have hIEdval : ∫ z : EuclideanSpace ℝ (Fin n), E (z + d) = ∫ z, E z := by
    have h := (measurePreserving_add_right
      (volume : Measure (EuclideanSpace ℝ (Fin n))) d).integral_comp
      (measurableEmbedding_addRight d) E
    simpa using h
  have hIsq : Integrable (fun z : EuclideanSpace ℝ (Fin n) =>
      ‖z‖ ^ 2 * Real.exp (-(b / 4) * ‖z‖ ^ 2)) volume := (gsq (b / 4) hb4).1
  set M : EuclideanSpace ℝ (Fin n) → ℝ := fun z =>
    c * ‖d‖ * (3 * E (z + d) + 2 * E z
      + 3 * b * (‖z‖ ^ 2 * Real.exp (-(b / 4) * ‖z‖ ^ 2))) with hM
  have hIM : Integrable M volume := by
    rw [hM]
    exact (((hIEd.const_mul 3).add (hIE.const_mul 2)).add
      (hIsq.const_mul (3 * b))).const_mul _
  set h : EuclideanSpace ℝ (Fin n) → ℝ := fun z =>
    c * ((z + d) j) * E (z + d) - c * (z j) * E z with hh
  have hcont : Continuous h := by rw [hh, hE]; fun_prop
  have hptwise : ∀ z, |h z| ≤ M z := by
    intro z
    have hj1 : |(d : EuclideanSpace ℝ (Fin n)) j| ≤ ‖d‖ := coordle d j
    have hj2 : |z j| ≤ ‖z‖ := coordle z j
    have hz0 : (0 : ℝ) ≤ ‖z‖ := norm_nonneg _
    have hcd : (0 : ℝ) ≤ c * ‖d‖ := mul_nonneg hc hd0
    have hsqpos : (0 : ℝ) ≤ 3 * b * (‖z‖ ^ 2 * Real.exp (-(b / 4) * ‖z‖ ^ 2)) := by positivity
    have hdecomp : h z = c * (d j) * E (z + d) + c * (z j) * (E (z + d) - E z) := by
      rw [hh]
      simp only
      have hcoord : ((z + d) j) = z j + d j := by simp
      rw [hcoord]
      ring
    have hbase : |h z| ≤ c * ‖d‖ * E (z + d) + c * |z j| * |E (z + d) - E z| := by
      rw [hdecomp]
      refine le_trans (htri _ _) ?_
      have e1 : |c * (d j) * E (z + d)| ≤ c * ‖d‖ * E (z + d) := by
        rw [abs_mul, abs_mul, abs_of_nonneg hc, abs_of_pos (hEpos _)]
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hj1 hc) (hEpos _).le
      have e2 : |c * (z j) * (E (z + d) - E z)| = c * |z j| * |E (z + d) - E z| := by
        rw [abs_mul, abs_mul, abs_of_nonneg hc]
      linarith
    show |h z| ≤ c * ‖d‖ * (3 * E (z + d) + 2 * E z
      + 3 * b * (‖z‖ ^ 2 * Real.exp (-(b / 4) * ‖z‖ ^ 2)))
    rcases le_or_gt ‖z‖ (2 * ‖d‖) with hcase | hcase
    · have e3 : |E (z + d) - E z| ≤ E (z + d) + E z := by
        refine le_trans (htri' _ _) ?_
        rw [abs_of_pos (hEpos _), abs_of_pos (hEpos _)]
      have e4 : c * |z j| * |E (z + d) - E z| ≤ c * (2 * ‖d‖) * (E (z + d) + E z) :=
        mul_le_mul (mul_le_mul_of_nonneg_left (le_trans hj2 hcase) hc) e3
          (abs_nonneg _) (by positivity)
      calc |h z| ≤ c * ‖d‖ * E (z + d) + c * (2 * ‖d‖) * (E (z + d) + E z) := by linarith
        _ = c * ‖d‖ * (3 * E (z + d) + 2 * E z) := by ring
        _ ≤ c * ‖d‖ * (3 * E (z + d) + 2 * E z
              + 3 * b * (‖z‖ ^ 2 * Real.exp (-(b / 4) * ‖z‖ ^ 2))) :=
            mul_le_mul_of_nonneg_left (by linarith) hcd
    · have hdz : ‖d‖ ≤ ‖z‖ / 2 := by linarith
      have hzd : ‖z‖ / 2 ≤ ‖z + d‖ := by
        have h1 : ‖z‖ - ‖d‖ ≤ ‖z + d‖ := by
          simpa [sub_neg_eq_add] using norm_sub_norm_le z (-d)
        linarith
      have hm1 : (b / 4) * ‖z‖ ^ 2 ≤ b * ‖z + d‖ ^ 2 := by
        have hsq : (‖z‖ / 2) ^ 2 ≤ ‖z + d‖ ^ 2 := pow_le_pow_left₀ (by positivity) hzd 2
        have hq : ‖z‖ ^ 2 / 4 ≤ ‖z + d‖ ^ 2 := by
          calc ‖z‖ ^ 2 / 4 = (‖z‖ / 2) ^ 2 := by ring
            _ ≤ ‖z + d‖ ^ 2 := hsq
        calc (b / 4) * ‖z‖ ^ 2 = b * (‖z‖ ^ 2 / 4) := by ring
          _ ≤ b * ‖z + d‖ ^ 2 := mul_le_mul_of_nonneg_left hq hb.le
      have hm2 : (b / 4) * ‖z‖ ^ 2 ≤ b * ‖z‖ ^ 2 :=
        mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      have hdiffnorm : |b * ‖z + d‖ ^ 2 - b * ‖z‖ ^ 2| ≤ 3 * b * (‖z‖ * ‖d‖) := by
        have hexp : ‖z + d‖ ^ 2 = ‖z‖ ^ 2 + 2 * inner ℝ z d + ‖d‖ ^ 2 := norm_add_sq_real z d
        have hip : |inner ℝ z d| ≤ ‖z‖ * ‖d‖ := abs_real_inner_le_norm z d
        have hd2 : ‖d‖ ^ 2 ≤ (‖z‖ / 2) * ‖d‖ := by
          calc ‖d‖ ^ 2 = ‖d‖ * ‖d‖ := sq _
            _ ≤ (‖z‖ / 2) * ‖d‖ := mul_le_mul_of_nonneg_right hdz hd0
        have heq : b * ‖z + d‖ ^ 2 - b * ‖z‖ ^ 2 = b * (2 * inner ℝ z d + ‖d‖ ^ 2) := by
          rw [hexp]; ring
        rw [heq, abs_mul, abs_of_pos hb]
        have hinner : |2 * inner ℝ z d + ‖d‖ ^ 2| ≤ 3 * (‖z‖ * ‖d‖) := by
          have h1 : |2 * inner ℝ z d + ‖d‖ ^ 2| ≤ |2 * inner ℝ z d| + |‖d‖ ^ 2| := htri _ _
          have h2 : |2 * inner ℝ z d| = 2 * |inner ℝ z d| := by rw [abs_mul]; norm_num
          have h3 : |‖d‖ ^ 2| = ‖d‖ ^ 2 := abs_of_nonneg (by positivity)
          rw [h2, h3] at h1
          linarith [hip, hd2, mul_nonneg hz0 hd0]
        calc b * |2 * inner ℝ z d + ‖d‖ ^ 2| ≤ b * (3 * (‖z‖ * ‖d‖)) :=
              mul_le_mul_of_nonneg_left hinner hb.le
          _ = 3 * b * (‖z‖ * ‖d‖) := by ring
      have hneg : Real.exp (-((b / 4) * ‖z‖ ^ 2)) = Real.exp (-(b / 4) * ‖z‖ ^ 2) := by
        rw [neg_mul]
      have e6 : |E (z + d) - E z|
          ≤ (3 * b * (‖z‖ * ‖d‖)) * Real.exp (-((b / 4) * ‖z‖ ^ 2)) := by
        have hed := expdiff (b * ‖z + d‖ ^ 2) (b * ‖z‖ ^ 2) ((b / 4) * ‖z‖ ^ 2) hm1 hm2
        have hEE : E (z + d) - E z
            = Real.exp (-(b * ‖z + d‖ ^ 2)) - Real.exp (-(b * ‖z‖ ^ 2)) := by
          rw [hE]; simp only; rw [neg_mul, neg_mul]
        rw [hEE]
        exact le_trans hed (mul_le_mul_of_nonneg_right hdiffnorm (Real.exp_pos _).le)
      have e7 : c * |z j| * |E (z + d) - E z|
          ≤ c * ‖d‖ * (3 * b * (‖z‖ ^ 2 * Real.exp (-(b / 4) * ‖z‖ ^ 2))) := by
        calc c * |z j| * |E (z + d) - E z|
            ≤ c * ‖z‖ * ((3 * b * (‖z‖ * ‖d‖)) * Real.exp (-((b / 4) * ‖z‖ ^ 2))) :=
              mul_le_mul (mul_le_mul_of_nonneg_left hj2 hc) e6 (abs_nonneg _) (by positivity)
          _ = c * ‖d‖ * (3 * b * (‖z‖ ^ 2 * Real.exp (-((b / 4) * ‖z‖ ^ 2)))) := by ring
          _ = c * ‖d‖ * (3 * b * (‖z‖ ^ 2 * Real.exp (-(b / 4) * ‖z‖ ^ 2))) := by rw [hneg]
      calc |h z| ≤ c * ‖d‖ * E (z + d)
              + c * ‖d‖ * (3 * b * (‖z‖ ^ 2 * Real.exp (-(b / 4) * ‖z‖ ^ 2))) := by linarith
        _ = c * ‖d‖ * (E (z + d)
              + 3 * b * (‖z‖ ^ 2 * Real.exp (-(b / 4) * ‖z‖ ^ 2))) := by ring
        _ ≤ c * ‖d‖ * (3 * E (z + d) + 2 * E z
              + 3 * b * (‖z‖ ^ 2 * Real.exp (-(b / 4) * ‖z‖ ^ 2))) := by
            refine mul_le_mul_of_nonneg_left ?_ hcd
            linarith [(hEpos (z + d)).le, (hEpos z).le]
  have hIh : Integrable h volume := by
    refine Integrable.mono' hIM hcont.aestronglyMeasurable
      (Filter.Eventually.of_forall fun z => ?_)
    rw [Real.norm_eq_abs]
    exact hptwise z
  have hMval : ∫ z, M z
      = c * ‖d‖ * (3 * (∫ z : EuclideanSpace ℝ (Fin n), E z) + 2 * (∫ z, E z)
          + 3 * b * (∫ z : EuclideanSpace ℝ (Fin n),
              ‖z‖ ^ 2 * Real.exp (-(b / 4) * ‖z‖ ^ 2))) := by
    have hI1 : Integrable (fun z : EuclideanSpace ℝ (Fin n) => 3 * E (z + d) + 2 * E z)
        volume := (hIEd.const_mul 3).add (hIE.const_mul 2)
    have hI2 : Integrable (fun z : EuclideanSpace ℝ (Fin n) =>
        3 * b * (‖z‖ ^ 2 * Real.exp (-(b / 4) * ‖z‖ ^ 2))) volume := hIsq.const_mul (3 * b)
    have hI3 : Integrable (fun z : EuclideanSpace ℝ (Fin n) => 3 * E (z + d)) volume :=
      hIEd.const_mul 3
    have hI4 : Integrable (fun z : EuclideanSpace ℝ (Fin n) => 2 * E z) volume :=
      hIE.const_mul 2
    rw [hM, integral_const_mul]
    congr 1
    rw [integral_add hI1 hI2, integral_add hI3 hI4,
      integral_const_mul, integral_const_mul, integral_const_mul, hIEdval]
  calc ∫ z : EuclideanSpace ℝ (Fin n), |h z|
      ≤ ∫ z, M z := integral_mono hIh.abs hIM hptwise
    _ ≤ c * ‖d‖ * ((Real.pi / b) ^ ((n : ℝ) / 2) * (5 + 24 * (8 : ℝ) ^ ((n : ℝ) / 2))) := by
        have hEval : ∫ z : EuclideanSpace ℝ (Fin n), E z
            = (Real.pi / b) ^ ((n : ℝ) / 2) := by rw [hE]; exact gval b hb
        rw [hMval, hEval]
        have hsq := (gsq (b / 4) hb4).2
        have hpb : (0 : ℝ) < Real.pi / b := by positivity
        have hrw : Real.pi / (b / 4 / 2) = 8 * (Real.pi / b) := by field_simp; ring
        have h8 : (2 / (b / 4)) = 8 / b := by field_simp; norm_num
        rw [hrw, Real.mul_rpow (by norm_num) hpb.le, h8] at hsq
        have hbig : 3 * b * (∫ w : EuclideanSpace ℝ (Fin n),
            ‖w‖ ^ 2 * Real.exp (-(b / 4) * ‖w‖ ^ 2))
            ≤ 24 * ((8 : ℝ) ^ ((n : ℝ) / 2) * (Real.pi / b) ^ ((n : ℝ) / 2)) := by
          have h3b : (0 : ℝ) ≤ 3 * b := by positivity
          calc 3 * b * (∫ w : EuclideanSpace ℝ (Fin n),
                ‖w‖ ^ 2 * Real.exp (-(b / 4) * ‖w‖ ^ 2))
              ≤ 3 * b * (8 / b * ((8 : ℝ) ^ ((n : ℝ) / 2)
                  * (Real.pi / b) ^ ((n : ℝ) / 2))) := mul_le_mul_of_nonneg_left hsq h3b
            _ = 24 * ((8 : ℝ) ^ ((n : ℝ) / 2) * (Real.pi / b) ^ ((n : ℝ) / 2)) := by
                field_simp; ring
        have hcd : (0 : ℝ) ≤ c * ‖d‖ := mul_nonneg hc hd0
        refine mul_le_mul_of_nonneg_left ?_ hcd
        calc 3 * (Real.pi / b) ^ ((n : ℝ) / 2) + 2 * (Real.pi / b) ^ ((n : ℝ) / 2)
              + 3 * b * (∫ w : EuclideanSpace ℝ (Fin n),
                  ‖w‖ ^ 2 * Real.exp (-(b / 4) * ‖w‖ ^ 2))
            ≤ 3 * (Real.pi / b) ^ ((n : ℝ) / 2) + 2 * (Real.pi / b) ^ ((n : ℝ) / 2)
              + 24 * ((8 : ℝ) ^ ((n : ℝ) / 2) * (Real.pi / b) ^ ((n : ℝ) / 2)) := by
              linarith [hbig]
          _ = (Real.pi / b) ^ ((n : ℝ) / 2) * (5 + 24 * (8 : ℝ) ^ ((n : ℝ) / 2)) := by ring
