module

public import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
public import GaussianRiesz.Preamble
public import GaussianRiesz.GaussEuclideanMomentBounds
public import GaussianRiesz.GaussSecondMomentIntegralBound

@[expose] public section
open MeasureTheory
theorem PVSubtractedSliceBound {n : ℕ} (j : Fin n) (x : EuclideanSpace ℝ (Fin n)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (f : EuclideanSpace ℝ (Fin n) → ℝ) (L : ℝ), 0 ≤ L →
      (∀ y : EuclideanSpace ℝ (Fin n), |f y - f x| ≤ L * ‖y - x‖) →
      ∀ s : ℝ, 0 < s →
        ∫⁻ y : EuclideanSpace ℝ (Fin n),
            ‖(Real.sqrt 2 * Real.exp (-s) * (y j - Real.exp (-s) * x j) / (1 - Real.exp (-2 * s))
                * (Real.pi ^ (-(n : ℝ) / 2) * (1 - Real.exp (-2 * s)) ^ (-(n : ℝ) / 2)
                    * Real.exp (-‖Real.exp (-s) • x - y‖ ^ 2 / (1 - Real.exp (-2 * s)))))
              * (f y - f x)‖ₑ
          ≤ ENNReal.ofReal (C * L * Real.exp (-s) * (1 + ‖x‖)) := by
  -- Steps 1-3 of the statement's proof are the elementary Gaussian facts collected in
  -- `GaussEuclideanMomentBounds` and `GaussSecondMomentIntegralBound`.  The estimate
  -- itself is the block after them: translate by `e^{-s} x`, split
  -- `|y - x| <= |w| + |d|`, and read off the two moments at the rate `1/sigma`.
  obtain ⟨-, -, coordle, -, gfirst, canon⟩ := GaussEuclideanMomentBounds (n := n)

  have gsq := fun (b : ℝ) (hb : 0 < b) => (GaussSecondMomentIntegralBound (n := n) b hb).2

  -- the exponential difference bound
  refine ⟨3 * Real.sqrt 2 * 2 ^ ((n : ℝ) / 2), by positivity, ?_⟩
  intro f L hL0 hL s hs
  have hx0 : (0:ℝ) ≤ ‖x‖ := norm_nonneg x
  have hr0 : 0 < Real.exp (-s) := Real.exp_pos _
  have hr1 : Real.exp (-s) < 1 := by rw [Real.exp_lt_one_iff]; linarith
  have hsq : Real.exp (-s) ^ 2 = Real.exp (-2 * s) := by
    rw [sq, ← Real.exp_add]; ring_nf
  set r : ℝ := Real.exp (-s) with hrdef
  set σ : ℝ := 1 - Real.exp (-2 * s) with hσdef
  have hσeq : σ = (1 - r) * (1 + r) := by rw [hσdef, ← hsq]; ring
  have h1r : 0 ≤ 1 - r := by linarith
  have hσ0 : 0 < σ := by rw [hσeq]; nlinarith
  have hσ1 : σ ≤ 1 := by rw [hσeq]; nlinarith
  set b : ℝ := σ⁻¹ with hbdef
  have hb : 0 < b := by rw [hbdef]; positivity
  have hbσ : σ * b = 1 := by rw [hbdef]; field_simp
  have hval2 : 1 / (σ * (b / 2)) = 2 := by
    rw [show σ * (b / 2) = σ * b / 2 by ring, hbσ]; norm_num
  have h2b : 2 / b = 2 * σ := by rw [hbdef]; field_simp
  set c : ℝ := Real.sqrt 2 * r / σ * (Real.pi ^ (-(n : ℝ) / 2) * σ ^ (-(n : ℝ) / 2)) with hcdef
  have hc0 : 0 < c := by
    rw [hcdef]; have h2 : (0:ℝ) < Real.sqrt 2 := by positivity
    positivity
  clear_value c
  set d : EuclideanSpace ℝ (Fin n) := x - r • x with hddef
  have hdn : ‖d‖ = (1 - r) * ‖x‖ := by
    rw [hddef, show x - r • x = (1 - r) • x by rw [sub_smul, one_smul], norm_smul,
      Real.norm_eq_abs, abs_of_nonneg h1r]
  -- STEP 3a: translation, and the pointwise majorant after it
  have htrans : ∀ G : EuclideanSpace ℝ (Fin n) → ENNReal,
      ∫⁻ w : EuclideanSpace ℝ (Fin n), G (r • x + w) = ∫⁻ y : EuclideanSpace ℝ (Fin n), G y :=
    fun G => (MeasureTheory.measurePreserving_add_left
      (volume : Measure (EuclideanSpace ℝ (Fin n))) (r • x)).lintegral_comp_emb
        (measurableEmbedding_addLeft (r • x)) G
  have hptw : ∀ w : EuclideanSpace ℝ (Fin n),
      ‖(Real.sqrt 2 * r * ((r • x + w) j - r * x j) / σ
            * (Real.pi ^ (-(n : ℝ) / 2) * σ ^ (-(n : ℝ) / 2)
                * Real.exp (-‖r • x - (r • x + w)‖ ^ 2 / σ)))
          * (f (r • x + w) - f x)‖ₑ
        ≤ ENNReal.ofReal (c * L * (‖w‖ ^ 2 * Real.exp (-b * ‖w‖ ^ 2))
            + c * L * ‖d‖ * (‖w‖ * Real.exp (-b * ‖w‖ ^ 2))) := by
    intro w
    have h1 : (r • x + w) j - r * x j = w j := by
      simp [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
    have h2 : ‖r • x - (r • x + w)‖ = ‖w‖ := by
      have h3 : r • x - (r • x + w) = -w := by abel
      rw [h3, norm_neg]
    have hexp : Real.exp (-‖w‖ ^ 2 / σ) = Real.exp (-b * ‖w‖ ^ 2) := by
      congr 1; rw [hbdef]; field_simp
    have hfac : Real.sqrt 2 * r * w j / σ
        * (Real.pi ^ (-(n : ℝ) / 2) * σ ^ (-(n : ℝ) / 2) * Real.exp (-b * ‖w‖ ^ 2))
        = c * (w j * Real.exp (-b * ‖w‖ ^ 2)) := by rw [hcdef]; ring
    rw [h1, h2, hexp, hfac, ← ofReal_norm]
    refine ENNReal.ofReal_le_ofReal ?_
    have hE : (0:ℝ) < Real.exp (-b * ‖w‖ ^ 2) := Real.exp_pos _
    have hyx : ‖(r • x + w) - x‖ ≤ ‖w‖ + ‖d‖ := by
      have h4 : (r • x + w) - x = w - d := by rw [hddef]; abel
      rw [h4]
      exact norm_sub_le w d
    have hdiff : |f (r • x + w) - f x| ≤ L * (‖w‖ + ‖d‖) :=
      (hL (r • x + w)).trans (mul_le_mul_of_nonneg_left hyx hL0)
    have hwj : |w j| ≤ ‖w‖ := coordle w j
    have hfirst : |c * (w j * Real.exp (-b * ‖w‖ ^ 2))|
        ≤ c * (‖w‖ * Real.exp (-b * ‖w‖ ^ 2)) := by
      rw [abs_mul c (w j * Real.exp (-b * ‖w‖ ^ 2)), abs_of_pos hc0,
        abs_mul (w j) (Real.exp (-b * ‖w‖ ^ 2)), abs_of_pos hE]
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hwj hE.le) hc0.le
    rw [Real.norm_eq_abs, abs_mul]
    calc |c * (w j * Real.exp (-b * ‖w‖ ^ 2))| * |f (r • x + w) - f x|
        ≤ c * (‖w‖ * Real.exp (-b * ‖w‖ ^ 2)) * (L * (‖w‖ + ‖d‖)) :=
          mul_le_mul hfirst hdiff (abs_nonneg _)
            (mul_nonneg hc0.le (mul_nonneg (norm_nonneg w) hE.le))
      _ = c * L * (‖w‖ ^ 2 * Real.exp (-b * ‖w‖ ^ 2))
            + c * L * ‖d‖ * (‖w‖ * Real.exp (-b * ‖w‖ ^ 2)) := by ring
  -- STEP 3b: the two Gaussian moments at the rate 1/σ
  have hA : Integrable (fun w : EuclideanSpace ℝ (Fin n) =>
      ‖w‖ ^ 2 * Real.exp (-b * ‖w‖ ^ 2)) volume := (gsq b hb).1
  have hB : Integrable (fun w : EuclideanSpace ℝ (Fin n) =>
      ‖w‖ * Real.exp (-b * ‖w‖ ^ 2)) volume := (gfirst b hb).1
  have hH : Integrable (fun w : EuclideanSpace ℝ (Fin n) =>
      c * L * (‖w‖ ^ 2 * Real.exp (-b * ‖w‖ ^ 2))
        + c * L * ‖d‖ * (‖w‖ * Real.exp (-b * ‖w‖ ^ 2))) volume :=
    (hA.const_mul _).add (hB.const_mul _)
  have hHval : ∫ w : EuclideanSpace ℝ (Fin n),
      (c * L * (‖w‖ ^ 2 * Real.exp (-b * ‖w‖ ^ 2))
        + c * L * ‖d‖ * (‖w‖ * Real.exp (-b * ‖w‖ ^ 2)))
      = c * L * (∫ w : EuclideanSpace ℝ (Fin n), ‖w‖ ^ 2 * Real.exp (-b * ‖w‖ ^ 2))
        + c * L * ‖d‖ * (∫ w : EuclideanSpace ℝ (Fin n), ‖w‖ * Real.exp (-b * ‖w‖ ^ 2)) := by
    rw [integral_add (hA.const_mul _) (hB.const_mul _), integral_const_mul, integral_const_mul]
  -- STEP 3c: assemble
  have hcan : c * (Real.pi / (b / 2)) ^ ((n : ℝ) / 2)
      = Real.sqrt 2 * r / σ * 2 ^ ((n : ℝ) / 2) := by
    rw [hcdef]
    calc Real.sqrt 2 * r / σ * (Real.pi ^ (-(n : ℝ) / 2) * σ ^ (-(n : ℝ) / 2))
          * (Real.pi / (b / 2)) ^ ((n : ℝ) / 2)
        = Real.sqrt 2 * r / σ * (Real.pi ^ (-(n : ℝ) / 2) * σ ^ (-(n : ℝ) / 2)
            * (Real.pi / (b / 2)) ^ ((n : ℝ) / 2)) := by ring
      _ = Real.sqrt 2 * r / σ * 2 ^ ((n : ℝ) / 2) := by
          rw [canon σ (b / 2) hσ0 (by positivity), hval2]
  have hkey : 2 * σ + ‖d‖ * (1 + 2 * σ) ≤ 3 * σ * (1 + ‖x‖) := by
    rw [hdn]
    have e : 3 * σ * (1 + ‖x‖) - (2 * σ + (1 - r) * ‖x‖ * (1 + 2 * σ))
        = σ + (1 - r) * ‖x‖ * (3 * (1 + r) - (1 + 2 * σ)) := by rw [hσeq]; ring
    have hpos : 0 ≤ (1 - r) * ‖x‖ * (3 * (1 + r) - (1 + 2 * σ)) :=
      mul_nonneg (mul_nonneg h1r hx0) (by linarith)
    linarith
  rw [← htrans]
  calc ∫⁻ w : EuclideanSpace ℝ (Fin n),
        ‖(Real.sqrt 2 * r * ((r • x + w) j - r * x j) / σ
            * (Real.pi ^ (-(n : ℝ) / 2) * σ ^ (-(n : ℝ) / 2)
                * Real.exp (-‖r • x - (r • x + w)‖ ^ 2 / σ)))
          * (f (r • x + w) - f x)‖ₑ
      ≤ ∫⁻ w : EuclideanSpace ℝ (Fin n), ENNReal.ofReal
          (c * L * (‖w‖ ^ 2 * Real.exp (-b * ‖w‖ ^ 2))
            + c * L * ‖d‖ * (‖w‖ * Real.exp (-b * ‖w‖ ^ 2))) := lintegral_mono hptw
    _ = ENNReal.ofReal (∫ w : EuclideanSpace ℝ (Fin n),
          (c * L * (‖w‖ ^ 2 * Real.exp (-b * ‖w‖ ^ 2))
            + c * L * ‖d‖ * (‖w‖ * Real.exp (-b * ‖w‖ ^ 2)))) := by
        refine (MeasureTheory.ofReal_integral_eq_lintegral_ofReal hH
          (Filter.Eventually.of_forall fun w => ?_)).symm
        have hcl : (0:ℝ) ≤ c * L := mul_nonneg hc0.le hL0
        refine add_nonneg (mul_nonneg hcl (by positivity))
          (mul_nonneg (mul_nonneg hcl (norm_nonneg d)) (by positivity))
    _ ≤ ENNReal.ofReal (3 * Real.sqrt 2 * 2 ^ ((n : ℝ) / 2) * L * r * (1 + ‖x‖)) := by
        refine ENNReal.ofReal_le_ofReal ?_
        rw [hHval]
        have hd0 : (0:ℝ) ≤ ‖d‖ := norm_nonneg d
        have hstep : c * L * (∫ w : EuclideanSpace ℝ (Fin n), ‖w‖ ^ 2 * Real.exp (-b * ‖w‖ ^ 2))
              + c * L * ‖d‖ * (∫ w : EuclideanSpace ℝ (Fin n), ‖w‖ * Real.exp (-b * ‖w‖ ^ 2))
            ≤ c * L * ((2 / b) * (Real.pi / (b / 2)) ^ ((n : ℝ) / 2))
              + c * L * ‖d‖ * ((1 + 2 / b) * (Real.pi / (b / 2)) ^ ((n : ℝ) / 2)) := by
          have hcl : (0:ℝ) ≤ c * L := mul_nonneg hc0.le hL0
          have hcld : (0:ℝ) ≤ c * L * ‖d‖ := mul_nonneg hcl hd0
          exact add_le_add (mul_le_mul_of_nonneg_left (gsq b hb).2 hcl)
            (mul_le_mul_of_nonneg_left (gfirst b hb).2 hcld)
        refine hstep.trans ?_
        have hfold : c * L * ((2 / b) * (Real.pi / (b / 2)) ^ ((n : ℝ) / 2))
              + c * L * ‖d‖ * ((1 + 2 / b) * (Real.pi / (b / 2)) ^ ((n : ℝ) / 2))
            = (Real.sqrt 2 * r / σ * 2 ^ ((n : ℝ) / 2)) * L * (2 * σ + ‖d‖ * (1 + 2 * σ)) := by
          rw [← hcan, h2b]; ring
        rw [hfold]
        have hlead : (0:ℝ) < Real.sqrt 2 * r / σ * 2 ^ ((n : ℝ) / 2) := by
          positivity
        calc (Real.sqrt 2 * r / σ * 2 ^ ((n : ℝ) / 2)) * L * (2 * σ + ‖d‖ * (1 + 2 * σ))
            ≤ (Real.sqrt 2 * r / σ * 2 ^ ((n : ℝ) / 2)) * L * (3 * σ * (1 + ‖x‖)) := by
              exact mul_le_mul_of_nonneg_left hkey (mul_nonneg hlead.le hL0)
          _ = 3 * Real.sqrt 2 * 2 ^ ((n : ℝ) / 2) * L * r * (1 + ‖x‖) := by
              field_simp
