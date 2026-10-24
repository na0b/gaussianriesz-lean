import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import GaussianRiesz.GaussEuclideanMomentBounds
open MeasureTheory
theorem PVTruncatedSliceEnormBound {n : ℕ} :
    ∀ (j : Fin n) (x : EuclideanSpace ℝ (Fin n)) (ε : ℝ), 0 < ε →
    ∀ (s : ℝ), 0 < s → ∀ (D : EuclideanSpace ℝ (Fin n) → ℝ),
    (∀ y : EuclideanSpace ℝ (Fin n), D y =
      Real.sqrt 2 * Real.exp (-s) * (y j - Real.exp (-s) * x j) / (1 - Real.exp (-2 * s))
        * (Real.pi ^ (-(n : ℝ) / 2) * (1 - Real.exp (-2 * s)) ^ (-(n : ℝ) / 2)
            * Real.exp (-‖Real.exp (-s) • x - y‖ ^ 2 / (1 - Real.exp (-2 * s))))) →
        (‖x - Real.exp (-s) • x‖ ≤ ε / 2 →
    ∫⁻ y in {y : EuclideanSpace ℝ (Fin n) | ε < ‖x - y‖}, ‖D y‖ₑ
    ≤ ENNReal.ofReal (40 * Real.sqrt 2 * 4 ^ ((n : ℝ) / 2) / ε ^ 2))
    ∧ ∫⁻ y in {y : EuclideanSpace ℝ (Fin n) | ε < ‖x - y‖}, ‖D y‖ₑ
    ≤ ENNReal.ofReal (3 * Real.sqrt 2 * 2 ^ ((n : ℝ) / 2) * Real.exp (-s)
    / (1 - Real.exp (-2 * s))) := by
  obtain ⟨gint, gval, coordle, fmom, gfirst, canon⟩ := GaussEuclideanMomentBounds (n := n)

  have expinv : ∀ (t : ℝ) (ht : 0 < t),
        Real.exp (-t) ≤ 1 / t := by
    intro t ht
    have h1 : t ≤ Real.exp t := by linarith [Real.add_one_le_exp t]
    have h3 : t * Real.exp (-t) ≤ 1 := by
      calc t * Real.exp (-t) ≤ Real.exp t * Real.exp (-t) := by nlinarith [Real.exp_pos (-t)]
        _ = 1 := by rw [← Real.exp_add]; simp
    rw [le_div_iff₀ ht]
    nlinarith [h3]

  intro j x ε hε s hs D hD
  have hr1 : Real.exp (-s) < 1 := by rw [Real.exp_lt_one_iff]; linarith
  have hσ0 : 0 < 1 - Real.exp (-2 * s) := by
    have : Real.exp (-2 * s) < 1 := by rw [Real.exp_lt_one_iff]; linarith
    linarith
  have hσ1 : 1 - Real.exp (-2 * s) ≤ 1 := by have := Real.exp_pos (-2 * s); linarith
  set σ : ℝ := 1 - Real.exp (-2 * s) with hσdef
  set r : ℝ := Real.exp (-s) with hrdef
  set b : ℝ := σ⁻¹ with hbdef
  have hb : 0 < b := by rw [hbdef]; positivity
  have hbσ : σ * b = 1 := by rw [hbdef]; field_simp
  have hval4 : 1 / (σ * (b / 4)) = 4 := by
    rw [show σ * (b / 4) = σ * b / 4 by ring, hbσ]; norm_num
  have hval2 : 1 / (σ * (b / 2)) = 2 := by
    rw [show σ * (b / 2) = σ * b / 2 by ring, hbσ]; norm_num
  set c : ℝ := Real.sqrt 2 * r / σ * (Real.pi ^ (-(n : ℝ) / 2) * σ ^ (-(n : ℝ) / 2)) with hcdef
  have hc0 : 0 < c := by
    rw [hcdef]; have h2 : (0:ℝ) < Real.sqrt 2 := by positivity
    positivity
  -- the truncation region and its translate
  set S : Set (EuclideanSpace ℝ (Fin n)) := {y | ε < ‖x - y‖} with hSdef
  have hSm : MeasurableSet S := by
    rw [hSdef]; exact measurableSet_lt measurable_const (by fun_prop)
  set d : EuclideanSpace ℝ (Fin n) := x - r • x with hddef
  set R : Set (EuclideanSpace ℝ (Fin n)) := {w | ε < ‖d - w‖} with hRdef
  have hRm : MeasurableSet R := by
    rw [hRdef]; exact measurableSet_lt measurable_const (by fun_prop)
  have hpre : (fun w : EuclideanSpace ℝ (Fin n) => r • x + w) ⁻¹' S = R := by
    ext w
    have hxw : x - (r • x + w) = d - w := by rw [hddef]; abel
    simp only [hSdef, hRdef, Set.mem_preimage, Set.mem_ofPred_eq, hxw]
  have htrans : ∀ G : EuclideanSpace ℝ (Fin n) → ENNReal,
      ∫⁻ w in R, G (r • x + w) = ∫⁻ y in S, G y := by
    intro G
    have hmp := (MeasureTheory.measurePreserving_add_left
      (volume : Measure (EuclideanSpace ℝ (Fin n))) (r • x)).restrict_preimage hSm
    rw [hpre] at hmp
    exact hmp.lintegral_comp_emb (measurableEmbedding_addLeft (r • x)) G
  -- the pointwise majorant after translation
  have hptw : ∀ w : EuclideanSpace ℝ (Fin n),
      ‖D (r • x + w)‖ₑ ≤ ENNReal.ofReal (c * (‖w‖ * Real.exp (-b * ‖w‖ ^ 2))) := by
    intro w
    have h1 : (r • x + w) j - r * x j = w j := by
      simp [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
    have h2 : ‖r • x - (r • x + w)‖ = ‖w‖ := by
      have h3 : r • x - (r • x + w) = -w := by abel
      rw [h3, norm_neg]
    have hexp : Real.exp (-‖w‖ ^ 2 / σ) = Real.exp (-b * ‖w‖ ^ 2) := by
      congr 1; rw [hbdef]; field_simp
    rw [hD, h1, h2, hexp, ← ofReal_norm]
    refine ENNReal.ofReal_le_ofReal ?_
    have hfac : Real.sqrt 2 * r * w j / σ
        * (Real.pi ^ (-(n : ℝ) / 2) * σ ^ (-(n : ℝ) / 2) * Real.exp (-b * ‖w‖ ^ 2))
        = c * (w j * Real.exp (-b * ‖w‖ ^ 2)) := by rw [hcdef]; ring
    rw [hfac, Real.norm_eq_abs, abs_mul, abs_of_pos hc0, abs_mul,
      abs_of_pos (Real.exp_pos (-b * ‖w‖ ^ 2))]
    exact mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right (coordle w j) (Real.exp_pos _).le) hc0.le
  refine ⟨fun hd => ?_, ?_⟩
  · -- SMALL s: the region forces ‖w‖ > ε/2, and the Gaussian pays e^{-ε²/(8σ)}
    have hreg : ∀ w ∈ R, ε / 2 < ‖w‖ := by
      intro w hw
      rw [hRdef, Set.mem_ofPred_eq] at hw
      have h4 : ‖d - w‖ ≤ ‖d‖ + ‖w‖ := norm_sub_le d w
      linarith
    set C : ℝ := c * Real.exp (-(b * ε ^ 2 / 8)) * (1 + 4 / b) with hCdef
    have hC0 : 0 ≤ C := by
      rw [hCdef]
      have : (0:ℝ) < 1 + 4 / b := by positivity
      positivity
    have hmaj : ∀ w ∈ R, ENNReal.ofReal (c * (‖w‖ * Real.exp (-b * ‖w‖ ^ 2)))
        ≤ ENNReal.ofReal (C * Real.exp (-(b / 4) * ‖w‖ ^ 2)) := by
      intro w hw
      have hwn : ε / 2 < ‖w‖ := hreg w hw
      refine ENNReal.ofReal_le_ofReal ?_
      have hsplit : Real.exp (-b * ‖w‖ ^ 2)
          = Real.exp (-(b / 2) * ‖w‖ ^ 2) * Real.exp (-(b / 2) * ‖w‖ ^ 2) := by
        rw [← Real.exp_add]; ring_nf
      have hA : ‖w‖ * Real.exp (-(b / 2) * ‖w‖ ^ 2)
          ≤ (1 + 2 / (b / 2)) * Real.exp (-((b / 2) / 2) * ‖w‖ ^ 2) := fmom (b / 2) (by positivity) w
      have hB : Real.exp (-(b / 2) * ‖w‖ ^ 2) ≤ Real.exp (-(b * ε ^ 2 / 8)) := by
        refine Real.exp_le_exp.2 ?_
        nlinarith [hb]
      calc c * (‖w‖ * Real.exp (-b * ‖w‖ ^ 2))
          = c * ((‖w‖ * Real.exp (-(b / 2) * ‖w‖ ^ 2)) * Real.exp (-(b / 2) * ‖w‖ ^ 2)) := by
            rw [hsplit]; ring
        _ ≤ c * (((1 + 2 / (b / 2)) * Real.exp (-((b / 2) / 2) * ‖w‖ ^ 2))
              * Real.exp (-(b * ε ^ 2 / 8))) := by
            refine mul_le_mul_of_nonneg_left ?_ hc0.le
            exact mul_le_mul hA hB (Real.exp_pos _).le (by positivity)
        _ = C * Real.exp (-(b / 4) * ‖w‖ ^ 2) := by
            rw [hCdef, show (b / 2) / 2 = b / 4 by ring,
              show (2:ℝ) / (b / 2) = 4 / b by rw [div_div_eq_mul_div]; norm_num]
            ring
    rw [← htrans]
    calc ∫⁻ w in R, ‖D (r • x + w)‖ₑ
        ≤ ∫⁻ w in R, ENNReal.ofReal (C * Real.exp (-(b / 4) * ‖w‖ ^ 2)) := by
          refine lintegral_mono_ae ((ae_restrict_iff' hRm).2 ?_)
          exact Filter.Eventually.of_forall fun w hw => (hptw w).trans (hmaj w hw)
      _ ≤ ∫⁻ w : EuclideanSpace ℝ (Fin n), ENNReal.ofReal (C * Real.exp (-(b / 4) * ‖w‖ ^ 2)) :=
          setLIntegral_le_lintegral _ _
      _ = ENNReal.ofReal (C * (Real.pi / (b / 4)) ^ ((n : ℝ) / 2)) := by
          rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal
            ((gint (b / 4) (by positivity)).const_mul C)
            (Filter.Eventually.of_forall fun w =>
              mul_nonneg hC0 (Real.exp_pos (-(b / 4) * ‖w‖ ^ 2)).le),
            integral_const_mul, gval (b / 4) (by positivity)]
      _ ≤ ENNReal.ofReal (40 * Real.sqrt 2 * 4 ^ ((n : ℝ) / 2) / ε ^ 2) := by
          refine ENNReal.ofReal_le_ofReal ?_
          have hcan : Real.pi ^ (-(n : ℝ) / 2) * σ ^ (-(n : ℝ) / 2)
              * (Real.pi / (b / 4)) ^ ((n : ℝ) / 2) = 4 ^ ((n : ℝ) / 2) := by
            rw [canon σ (b / 4) hσ0 (by positivity), hval4]
          have hCval : C * (Real.pi / (b / 4)) ^ ((n : ℝ) / 2)
              = Real.sqrt 2 * r / σ * 4 ^ ((n : ℝ) / 2)
                * (Real.exp (-(b * ε ^ 2 / 8)) * (1 + 4 / b)) := by
            rw [hCdef, hcdef]
            calc Real.sqrt 2 * r / σ * (Real.pi ^ (-(n : ℝ) / 2) * σ ^ (-(n : ℝ) / 2))
                  * Real.exp (-(b * ε ^ 2 / 8)) * (1 + 4 / b)
                  * (Real.pi / (b / 4)) ^ ((n : ℝ) / 2)
                = Real.sqrt 2 * r / σ * (Real.pi ^ (-(n : ℝ) / 2) * σ ^ (-(n : ℝ) / 2)
                    * (Real.pi / (b / 4)) ^ ((n : ℝ) / 2))
                  * (Real.exp (-(b * ε ^ 2 / 8)) * (1 + 4 / b)) := by ring
              _ = _ := by rw [hcan]
          rw [hCval]
          -- e^{-ε²/(8σ)} ≤ 8σ/ε², 4/b = 4σ ≤ 4, r ≤ 1
          have hexp : Real.exp (-(b * ε ^ 2 / 8)) ≤ 8 * σ / ε ^ 2 := by
            have ht : (0:ℝ) < b * ε ^ 2 / 8 := by positivity
            refine (expinv _ ht).trans ?_
            rw [div_le_div_iff₀ ht (by positivity)]
            have : σ * b = 1 := hbσ
            nlinarith [sq_nonneg ε, hσ0]
          have h4b : 4 / b = 4 * σ := by
            rw [hbdef]; field_simp
          have hσpos : 0 < σ := hσ0
          rw [h4b]
          have hstep : Real.exp (-(b * ε ^ 2 / 8)) * (1 + 4 * σ) ≤ (8 * σ / ε ^ 2) * 5 := by
            have h5 : 1 + 4 * σ ≤ 5 := by linarith
            exact mul_le_mul hexp h5 (by positivity) (by positivity)
          have hlead : 0 < Real.sqrt 2 * r / σ * 4 ^ ((n : ℝ) / 2) := by
            have : (0:ℝ) < Real.sqrt 2 := by positivity
            positivity
          calc Real.sqrt 2 * r / σ * 4 ^ ((n : ℝ) / 2)
                * (Real.exp (-(b * ε ^ 2 / 8)) * (1 + 4 * σ))
              ≤ Real.sqrt 2 * r / σ * 4 ^ ((n : ℝ) / 2) * ((8 * σ / ε ^ 2) * 5) :=
                mul_le_mul_of_nonneg_left hstep hlead.le
            _ = 40 * Real.sqrt 2 * 4 ^ ((n : ℝ) / 2) / ε ^ 2 * r := by field_simp; ring
            _ ≤ 40 * Real.sqrt 2 * 4 ^ ((n : ℝ) / 2) / ε ^ 2 := by
                have hQ : (0:ℝ) ≤ 40 * Real.sqrt 2 * 4 ^ ((n : ℝ) / 2) / ε ^ 2 := by positivity
                nlinarith [hQ, hr1]
  · -- LARGE s: drop the region and use the global first moment
    rw [← htrans]
    calc ∫⁻ w in R, ‖D (r • x + w)‖ₑ
        ≤ ∫⁻ w in R, ENNReal.ofReal (c * (‖w‖ * Real.exp (-b * ‖w‖ ^ 2))) :=
          lintegral_mono fun w => hptw w
      _ ≤ ∫⁻ w : EuclideanSpace ℝ (Fin n),
            ENNReal.ofReal (c * (‖w‖ * Real.exp (-b * ‖w‖ ^ 2))) := setLIntegral_le_lintegral _ _
      _ = ENNReal.ofReal (c * ∫ w : EuclideanSpace ℝ (Fin n), ‖w‖ * Real.exp (-b * ‖w‖ ^ 2)) := by
          rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal
            ((gfirst b hb).1.const_mul c)
            (Filter.Eventually.of_forall fun w =>
              mul_nonneg hc0.le (mul_nonneg (norm_nonneg w) (Real.exp_pos _).le)),
            integral_const_mul]
      _ ≤ ENNReal.ofReal (c * ((1 + 2 / b) * (Real.pi / (b / 2)) ^ ((n : ℝ) / 2))) :=
          ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left (gfirst b hb).2 hc0.le)
      _ ≤ ENNReal.ofReal (3 * Real.sqrt 2 * 2 ^ ((n : ℝ) / 2) * r / σ) := by
          refine ENNReal.ofReal_le_ofReal ?_
          have hcan : Real.pi ^ (-(n : ℝ) / 2) * σ ^ (-(n : ℝ) / 2)
              * (Real.pi / (b / 2)) ^ ((n : ℝ) / 2) = 2 ^ ((n : ℝ) / 2) := by
            rw [canon σ (b / 2) hσ0 (by positivity), hval2]
          have h2b : 2 / b = 2 * σ := by rw [hbdef]; field_simp
          have hval : c * ((1 + 2 / b) * (Real.pi / (b / 2)) ^ ((n : ℝ) / 2))
              = Real.sqrt 2 * r / σ * 2 ^ ((n : ℝ) / 2) * (1 + 2 * σ) := by
            rw [hcdef, h2b]
            calc Real.sqrt 2 * r / σ * (Real.pi ^ (-(n : ℝ) / 2) * σ ^ (-(n : ℝ) / 2))
                  * ((1 + 2 * σ) * (Real.pi / (b / 2)) ^ ((n : ℝ) / 2))
                = Real.sqrt 2 * r / σ * (Real.pi ^ (-(n : ℝ) / 2) * σ ^ (-(n : ℝ) / 2)
                    * (Real.pi / (b / 2)) ^ ((n : ℝ) / 2)) * (1 + 2 * σ) := by ring
              _ = _ := by rw [hcan]
          rw [hval]
          have hlead : 0 < Real.sqrt 2 * r / σ * 2 ^ ((n : ℝ) / 2) := by
            have : (0:ℝ) < Real.sqrt 2 := by positivity
            positivity
          calc Real.sqrt 2 * r / σ * 2 ^ ((n : ℝ) / 2) * (1 + 2 * σ)
              ≤ Real.sqrt 2 * r / σ * 2 ^ ((n : ℝ) / 2) * 3 :=
                mul_le_mul_of_nonneg_left (by linarith) hlead.le
            _ = 3 * Real.sqrt 2 * 2 ^ ((n : ℝ) / 2) * r / σ := by field_simp
