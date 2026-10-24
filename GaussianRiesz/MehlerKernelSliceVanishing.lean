import GaussianRiesz.MehlerKernelXDerivative
import GaussianRiesz.GaussIsProb
open MeasureTheory
theorem MehlerKernelSliceVanishing {n : ℕ} (j : Fin n) (x : EuclideanSpace ℝ (Fin n)) :
    ∀ s : ℝ, 0 < s →
        Integrable (fun y : EuclideanSpace ℝ (Fin n) =>
            Real.sqrt 2 * Real.exp (-s) * (y j - Real.exp (-s) * x j) / (1 - Real.exp (-2 * s))
              * (Real.pi ^ (-(n : ℝ) / 2) * (1 - Real.exp (-2 * s)) ^ (-(n : ℝ) / 2)
                  * Real.exp (-‖Real.exp (-s) • x - y‖ ^ 2 / (1 - Real.exp (-2 * s)))))
            volume
          ∧ ∫ y : EuclideanSpace ℝ (Fin n),
              Real.sqrt 2 * Real.exp (-s) * (y j - Real.exp (-s) * x j) / (1 - Real.exp (-2 * s))
                * (Real.pi ^ (-(n : ℝ) / 2) * (1 - Real.exp (-2 * s)) ^ (-(n : ℝ) / 2)
                    * Real.exp (-‖Real.exp (-s) • x - y‖ ^ 2
                        / (1 - Real.exp (-2 * s)))) = 0 := by
  intro s hs
  -- the appendix's letters: `r = e^{-s}` and `σ = 1 - e^{-2s}`
  set r : ℝ := Real.exp (-s) with hr
  set σ : ℝ := 1 - Real.exp (-2 * s) with hσ
  have hr0 : 0 < r := Real.exp_pos _
  have hσ0 : 0 < σ := by
    rw [hσ]
    have h : Real.exp (-2 * s) < 1 := by rw [Real.exp_lt_one_iff]; linarith
    linarith
  set F : EuclideanSpace ℝ (Fin n) → ℝ := fun y =>
    Real.sqrt 2 * r * (y j - r * x j) / σ
      * (Real.pi ^ (-(n : ℝ) / 2) * σ ^ (-(n : ℝ) / 2)
          * Real.exp (-‖r • x - y‖ ^ 2 / σ)) with hF
  -- Step 0: the translated integrand `G w = F (r • x + w)`, in which the linear factor
  -- is `w j` and the Gaussian depends only on `‖w‖`.
  set G : EuclideanSpace ℝ (Fin n) → ℝ := fun w =>
    Real.sqrt 2 * r * w j / σ
      * (Real.pi ^ (-(n : ℝ) / 2) * σ ^ (-(n : ℝ) / 2) * Real.exp (-‖w‖ ^ 2 / σ)) with hG
  have hshift : ∀ w : EuclideanSpace ℝ (Fin n), F (r • x + w) = G w := by
    intro w
    simp only [hF, hG]
    have h1 : (r • x + w) j - r * x j = w j := by simp
    have h2 : r • x - (r • x + w) = -w := by abel
    rw [h1, h2, norm_neg]
  -- Step 1: the Gaussian majorant.  `‖w‖ e^{-‖w‖²/σ} ≤ (1+2σ) e^{-‖w‖²/(2σ)}`, which is
  -- `u e^{-u} ≤ 1` at `u = ‖w‖²/(2σ)` together with `t ≤ 1 + t²`.
  have hkey : ∀ w : EuclideanSpace ℝ (Fin n),
      ‖w‖ * Real.exp (-‖w‖ ^ 2 / σ)
        ≤ (1 + 2 * σ) * Real.exp (-(1 / (2 * σ)) * ‖w‖ ^ 2) := by
    intro w
    set t : ℝ := ‖w‖ with ht
    set E : ℝ := Real.exp (-(1 / (2 * σ)) * t ^ 2) with hE
    have hE0 : 0 < E := Real.exp_pos _
    have hE1 : E ≤ 1 := by
      rw [hE, Real.exp_le_one_iff]
      have h : (0 : ℝ) ≤ (1 / (2 * σ)) * t ^ 2 := by positivity
      linarith
    have hEE : Real.exp (-t ^ 2 / σ) = E * E := by
      rw [hE, ← Real.exp_add]
      congr 1
      field_simp
      ring
    have hue : ((1 / (2 * σ)) * t ^ 2) * E ≤ 1 := by
      rw [hE]
      have h1 : (1 / (2 * σ)) * t ^ 2 ≤ Real.exp ((1 / (2 * σ)) * t ^ 2) := by
        linarith [Real.add_one_le_exp ((1 / (2 * σ)) * t ^ 2)]
      have h2 : (0 : ℝ) < Real.exp (-(1 / (2 * σ)) * t ^ 2) := Real.exp_pos _
      have h3 : Real.exp ((1 / (2 * σ)) * t ^ 2) * Real.exp (-(1 / (2 * σ)) * t ^ 2) = 1 := by
        rw [← Real.exp_add]; ring_nf; exact Real.exp_zero
      nlinarith
    have hmom : t ^ 2 * E ≤ 2 * σ := by
      have h2σ : (0 : ℝ) < 2 * σ := by linarith
      have h := mul_le_mul_of_nonneg_left hue h2σ.le
      rw [mul_one] at h
      calc t ^ 2 * E = (2 * σ) * (((1 / (2 * σ)) * t ^ 2) * E) := by field_simp
        _ ≤ 2 * σ := h
    calc t * Real.exp (-t ^ 2 / σ) = t * (E * E) := by rw [hEE]
      _ ≤ (1 + t ^ 2) * (E * E) := by nlinarith [sq_nonneg (t - 1), mul_pos hE0 hE0]
      _ = E * E + (t ^ 2 * E) * E := by ring
      _ ≤ 1 * E + (2 * σ) * E := by nlinarith
      _ = (1 + 2 * σ) * E := by ring
  have hgauss : Integrable (fun w : EuclideanSpace ℝ (Fin n) =>
      Real.exp (-(1 / (2 * σ)) * ‖w‖ ^ 2)) volume := by
    have hc : (0 : ℝ) < 1 / (2 * σ) := by positivity
    have h := (GaussianFourier.integrable_cexp_neg_mul_sq_norm_add
        (V := EuclideanSpace ℝ (Fin n)) (b := ((1 / (2 * σ) : ℝ) : ℂ)) (by simpa using hc) 0
        (0 : EuclideanSpace ℝ (Fin n))).re
    refine h.congr ?_
    filter_upwards with v
    simp only [zero_mul, add_zero, neg_mul]
    simp [← Complex.ofReal_pow, Complex.exp_re]
  -- Step 2: integrability of `G`, hence of `F`
  have hGcont : Continuous G := by rw [hG]; fun_prop
  have hGint : Integrable G volume := by
    refine Integrable.mono' (hgauss.const_mul (Real.sqrt 2 * r / σ
        * (Real.pi ^ (-(n : ℝ) / 2) * σ ^ (-(n : ℝ) / 2)) * (1 + 2 * σ)))
      hGcont.aestronglyMeasurable (Filter.Eventually.of_forall fun w => ?_)
    have hcoord : |w j| ≤ ‖w‖ := by simpa using PiLp.norm_apply_le w j
    have h1 : (0 : ℝ) < Real.pi ^ (-(n : ℝ) / 2) := Real.rpow_pos_of_pos Real.pi_pos _
    have h2 : (0 : ℝ) < σ ^ (-(n : ℝ) / 2) := Real.rpow_pos_of_pos hσ0 _
    have h3 : (0 : ℝ) < Real.sqrt 2 := by positivity
    have h4 : (0 : ℝ) < Real.exp (-‖w‖ ^ 2 / σ) := Real.exp_pos _
    have h5 := hkey w
    have hEG : ‖G w‖ = Real.sqrt 2 * r / σ * (Real.pi ^ (-(n : ℝ) / 2) * σ ^ (-(n : ℝ) / 2))
        * (|w j| * Real.exp (-‖w‖ ^ 2 / σ)) := by
      rw [hG]
      simp only [Real.norm_eq_abs, abs_mul, abs_div, abs_mul]
      rw [abs_of_pos h3, abs_of_pos hr0, abs_of_pos hσ0, abs_of_pos h1, abs_of_pos h2,
        abs_of_pos h4]
      ring
    rw [hEG]
    have h6 : |w j| * Real.exp (-‖w‖ ^ 2 / σ)
        ≤ (1 + 2 * σ) * Real.exp (-(1 / (2 * σ)) * ‖w‖ ^ 2) := by
      refine le_trans (mul_le_mul_of_nonneg_right hcoord h4.le) h5
    have h7 : (0 : ℝ) ≤ Real.sqrt 2 * r / σ
        * (Real.pi ^ (-(n : ℝ) / 2) * σ ^ (-(n : ℝ) / 2)) := by positivity
    calc Real.sqrt 2 * r / σ * (Real.pi ^ (-(n : ℝ) / 2) * σ ^ (-(n : ℝ) / 2))
          * (|w j| * Real.exp (-‖w‖ ^ 2 / σ))
        ≤ Real.sqrt 2 * r / σ * (Real.pi ^ (-(n : ℝ) / 2) * σ ^ (-(n : ℝ) / 2))
            * ((1 + 2 * σ) * Real.exp (-(1 / (2 * σ)) * ‖w‖ ^ 2)) :=
          mul_le_mul_of_nonneg_left h6 h7
      _ = Real.sqrt 2 * r / σ * (Real.pi ^ (-(n : ℝ) / 2) * σ ^ (-(n : ℝ) / 2))
            * (1 + 2 * σ) * Real.exp (-(1 / (2 * σ)) * ‖w‖ ^ 2) := by ring
  have hFGfun : (fun w : EuclideanSpace ℝ (Fin n) => F (r • x + w)) = G := funext hshift
  have hFint : Integrable F volume := by
    have hmp := measurePreserving_add_left (volume : Measure (EuclideanSpace ℝ (Fin n))) (r • x)
    refine (hmp.integrable_comp_emb (measurableEmbedding_addLeft (r • x))).mp ?_
    simp only [Function.comp_def]
    rw [hFGfun]
    exact hGint
  -- Step 3: oddness.  `G (-w) = -G w` because `w ↦ w j` is odd and `w ↦ ‖w‖` is even.
  have hGodd : ∀ w : EuclideanSpace ℝ (Fin n), G (-w) = -G w := by
    intro w
    have h1 : ((-w : EuclideanSpace ℝ (Fin n)) j) = -(w j) := by simp
    have h2 : ‖(-w : EuclideanSpace ℝ (Fin n))‖ = ‖w‖ := norm_neg w
    simp only [hG, h1, h2]
    ring
  have hGzero : ∫ w, G w = 0 := by
    have h1 : ∫ w, G (-w) = ∫ w, G w := integral_neg_eq_self G volume
    have h2 : ∫ w, G (-w) = -∫ w, G w := by
      rw [show (fun w : EuclideanSpace ℝ (Fin n) => G (-w)) = fun w => -G w from funext hGodd,
        integral_neg]
    rw [h2] at h1
    linarith
  refine ⟨hFint, ?_⟩
  calc ∫ y, F y = ∫ w, F (r • x + w) := (integral_add_left_eq_self (f := F) (r • x)).symm
    _ = ∫ w, G w := by rw [hFGfun]
    _ = 0 := hGzero
