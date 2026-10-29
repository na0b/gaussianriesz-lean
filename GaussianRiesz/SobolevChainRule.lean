module

public import GaussianRiesz.GaussD
public import GaussianRiesz.GaussL2LocallyIntegrable
public import GaussianRiesz.MollifierL2Local
public import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
public import Mathlib.Analysis.Calculus.BumpFunction.Normed
public import GaussianRiesz.GaussWeakGradChainRule
public import GaussianRiesz.GaussWeakGradAECongr
public import GaussianRiesz.GaussDWitness
public import GaussianRiesz.GaussCoordMemLp

@[expose] public section
open MeasureTheory
open scoped ENNReal
theorem SobolevChainRule {n : ℕ} (δ : ℝ) (hδ : 0 < δ) (u : Lp ℝ 2 (GaussMeasure n))
    (hu : u ∈ SobolevW12 n) (w : Lp ℝ 2 (GaussMeasure n))
    (hw : (w : EuclideanSpace ℝ (Fin n) → ℝ) =ᵐ[GaussMeasure n]
      fun x => Real.sqrt (((u : EuclideanSpace ℝ (Fin n) → ℝ) x) ^ 2 + δ ^ 2) - δ) :
    w ∈ SobolevW12 n
      ∧ (GaussD w : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
          =ᵐ[GaussMeasure n] fun x =>
            ((u : EuclideanSpace ℝ (Fin n) → ℝ) x
              / Real.sqrt (((u : EuclideanSpace ℝ (Fin n) → ℝ) x) ^ 2 + δ ^ 2))
            • (GaussD u : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) x := by
  -- Step 0: the analytic properties of `q_δ(t) = √(t²+δ²) - δ`.
  have qdProps :
      (∀ t : ℝ, δ ≤ Real.sqrt (t ^ 2 + δ ^ 2))
      ∧ (∀ t : ℝ, HasDerivAt (fun s : ℝ => Real.sqrt (s ^ 2 + δ ^ 2) - δ)
          (t / Real.sqrt (t ^ 2 + δ ^ 2)) t)
      ∧ (∀ t : ℝ, |t / Real.sqrt (t ^ 2 + δ ^ 2)| ≤ 1)
      ∧ (∀ s t : ℝ, |(Real.sqrt (s ^ 2 + δ ^ 2) - δ) - (Real.sqrt (t ^ 2 + δ ^ 2) - δ)|
          ≤ |s - t|)
      ∧ (∀ s t : ℝ, |s / Real.sqrt (s ^ 2 + δ ^ 2) - t / Real.sqrt (t ^ 2 + δ ^ 2)|
          ≤ δ⁻¹ * |s - t|)
      ∧ Continuous (fun t : ℝ => t / Real.sqrt (t ^ 2 + δ ^ 2)) := by
    have hpos : ∀ t : ℝ, 0 < t ^ 2 + δ ^ 2 := by intro t; positivity
    have hSpos : ∀ t : ℝ, 0 < Real.sqrt (t ^ 2 + δ ^ 2) := fun t => Real.sqrt_pos.2 (hpos t)
    have hSsq : ∀ t : ℝ, Real.sqrt (t ^ 2 + δ ^ 2) ^ 2 = t ^ 2 + δ ^ 2 :=
      fun t => Real.sq_sqrt (hpos t).le
    have hSδ : ∀ t : ℝ, δ ≤ Real.sqrt (t ^ 2 + δ ^ 2) := fun t =>
      (Real.le_sqrt hδ.le (hpos t).le).2 (by nlinarith [sq_nonneg t])
    -- the first derivative
    have hd1 : ∀ t : ℝ, HasDerivAt (fun s : ℝ => Real.sqrt (s ^ 2 + δ ^ 2) - δ)
        (t / Real.sqrt (t ^ 2 + δ ^ 2)) t := by
      intro t
      have hinner : HasDerivAt (fun s : ℝ => s ^ 2 + δ ^ 2) (2 * t) t := by
        simpa using (hasDerivAt_pow 2 t).add_const (δ ^ 2)
      have hs := (hinner.sqrt (hpos t).ne').sub_const δ
      have heq : 2 * t / (2 * Real.sqrt (t ^ 2 + δ ^ 2)) = t / Real.sqrt (t ^ 2 + δ ^ 2) := by
        rw [mul_div_mul_left _ _ (two_ne_zero)]
      rw [← heq]
      exact hs
    -- `|q'| ≤ 1`
    have hb1 : ∀ t : ℝ, |t / Real.sqrt (t ^ 2 + δ ^ 2)| ≤ 1 := by
      intro t
      rw [abs_div, abs_of_pos (hSpos t), div_le_one (hSpos t)]
      calc |t| = Real.sqrt (t ^ 2) := (Real.sqrt_sq_eq_abs t).symm
        _ ≤ Real.sqrt (t ^ 2 + δ ^ 2) := Real.sqrt_le_sqrt (by nlinarith [sq_nonneg δ])
    -- the second derivative
    have hd2 : ∀ t : ℝ, HasDerivAt (fun s : ℝ => s / Real.sqrt (s ^ 2 + δ ^ 2))
        (δ ^ 2 / Real.sqrt (t ^ 2 + δ ^ 2) ^ 3) t := by
      intro t
      have hD : HasDerivAt (fun s : ℝ => Real.sqrt (s ^ 2 + δ ^ 2))
          (t / Real.sqrt (t ^ 2 + δ ^ 2)) t := by
        simpa using (hd1 t).add_const δ
      have hq := (hasDerivAt_id t).div hD (hSpos t).ne'
      have heq : (1 * Real.sqrt (t ^ 2 + δ ^ 2) - t * (t / Real.sqrt (t ^ 2 + δ ^ 2)))
            / Real.sqrt (t ^ 2 + δ ^ 2) ^ 2
          = δ ^ 2 / Real.sqrt (t ^ 2 + δ ^ 2) ^ 3 := by
        rw [div_eq_div_iff (by positivity) (by positivity)]
        have h2 := hSsq t
        field_simp
        nlinarith [h2]
      rw [← heq]
      exact hq
    refine ⟨hSδ, hd1, hb1, ?_, ?_, ?_⟩
    · -- `q_δ` is 1-Lipschitz
      intro s t
      have hL : LipschitzWith 1 (fun s : ℝ => Real.sqrt (s ^ 2 + δ ^ 2) - δ) := by
        refine lipschitzWith_of_nnnorm_deriv_le (fun t => (hd1 t).differentiableAt) ?_
        intro t
        rw [← NNReal.coe_le_coe, coe_nnnorm, (hd1 t).deriv, Real.norm_eq_abs]
        exact hb1 t
      have h := hL.dist_le_mul s t
      simpa [Real.dist_eq] using h
    · -- `q_δ'` is `1/δ`-Lipschitz
      intro s t
      have hL : LipschitzWith (Real.toNNReal δ⁻¹)
          (fun s : ℝ => s / Real.sqrt (s ^ 2 + δ ^ 2)) := by
        refine lipschitzWith_of_nnnorm_deriv_le (fun t => (hd2 t).differentiableAt) ?_
        intro t
        rw [← NNReal.coe_le_coe, coe_nnnorm, Real.coe_toNNReal _ (by positivity), (hd2 t).deriv]
        have h3 : δ ^ 3 ≤ Real.sqrt (t ^ 2 + δ ^ 2) ^ 3 := by
          gcongr
          exact hSδ t
        have hp3 : (0:ℝ) < Real.sqrt (t ^ 2 + δ ^ 2) ^ 3 := by positivity
        rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), div_le_iff₀ hp3]
        have hid : δ⁻¹ * δ ^ 3 = δ ^ 2 := by
          rw [show δ ^ 3 = δ * δ ^ 2 by ring, ← mul_assoc, inv_mul_cancel₀ hδ.ne', one_mul]
        calc δ ^ 2 = δ⁻¹ * δ ^ 3 := hid.symm
          _ ≤ δ⁻¹ * Real.sqrt (t ^ 2 + δ ^ 2) ^ 3 :=
              mul_le_mul_of_nonneg_left h3 (by positivity)
      have h := hL.dist_le_mul s t
      rw [Real.dist_eq, Real.dist_eq, Real.coe_toNNReal _ (by positivity)] at h
      exact h
    · -- continuity of `q_δ'`
      have hc : Continuous (fun t : ℝ => Real.sqrt (t ^ 2 + δ ^ 2)) := by fun_prop
      exact Continuous.div continuous_id hc (fun t => (hSpos t).ne')
  obtain ⟨hSδ, hd1, hb1, hLip, hLip', hQc⟩ := qdProps
  -- the data of the problem
  have hGu : HasGaussWeakGrad (u : EuclideanSpace ℝ (Fin n) → ℝ)
      (fun x => Real.sqrt 2 •
        (GaussD u : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) x) := by
    have hg : GaussD u = hu.choose := by simp only [GaussD, dif_pos hu]
    rw [hg]
    exact hu.choose_spec
  have hpos : ∀ t : ℝ, 0 < t ^ 2 + δ ^ 2 := by intro t; positivity
  have hΘc : Continuous (fun t : ℝ => t / Real.sqrt (t ^ 2 + δ ^ 2)) := by
    refine Continuous.div continuous_id (by fun_prop) (fun t => ?_)
    exact (Real.sqrt_pos.2 (hpos t)).ne'
  have hUm : AEStronglyMeasurable (u : EuclideanSpace ℝ (Fin n) → ℝ) (GaussMeasure n) :=
    Lp.aestronglyMeasurable u
  have hΘm : AEStronglyMeasurable
      (fun x => (u : EuclideanSpace ℝ (Fin n) → ℝ) x
        / Real.sqrt (((u : EuclideanSpace ℝ (Fin n) → ℝ) x) ^ 2 + δ ^ 2))
      (GaussMeasure n) := hΘc.comp_aestronglyMeasurable hUm
  have hΘb : ∀ t : ℝ, |t / Real.sqrt (t ^ 2 + δ ^ 2)| ≤ 1 := by
    intro t
    have hS := Real.sqrt_pos.2 (hpos t)
    rw [abs_div, abs_of_pos hS, div_le_one hS]
    calc |t| = Real.sqrt (t ^ 2) := (Real.sqrt_sq_eq_abs t).symm
      _ ≤ Real.sqrt (t ^ 2 + δ ^ 2) := Real.sqrt_le_sqrt (by nlinarith [sq_nonneg δ])
  -- the candidate gradient
  have hWmem : MemLp (fun x => ((u : EuclideanSpace ℝ (Fin n) → ℝ) x
        / Real.sqrt (((u : EuclideanSpace ℝ (Fin n) → ℝ) x) ^ 2 + δ ^ 2))
      • (GaussD u : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) x) 2
      (GaussMeasure n) := by
    refine MemLp.of_le (Lp.memLp (GaussD u))
      (hΘm.smul (Lp.aestronglyMeasurable (GaussD u)))
      (Filter.Eventually.of_forall fun x => ?_)
    rw [norm_smul, Real.norm_eq_abs]
    refine le_trans (mul_le_mul_of_nonneg_right (hΘb _) (norm_nonneg _)) ?_
    rw [one_mul]
  set W : Lp (EuclideanSpace ℝ (Fin n)) 2 (GaussMeasure n) := hWmem.toLp _ with hWdef
  have hWcoe : (W : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
      =ᵐ[GaussMeasure n] fun x => ((u : EuclideanSpace ℝ (Fin n) → ℝ) x
        / Real.sqrt (((u : EuclideanSpace ℝ (Fin n) → ℝ) x) ^ 2 + δ ^ 2))
      • (GaussD u : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) x := hWmem.coeFn_toLp
  -- THE CORE CLAIM
  have hGL2 : ∀ i : Fin n, MemLp (fun x => (Real.sqrt 2 •
      (GaussD u : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) x) i) 2
      (GaussMeasure n) := by
    intro i
    have hb := GaussCoordMemLp (GaussD u) i
    refine (hb.const_mul (Real.sqrt 2)).ae_eq ?_
    filter_upwards with x
    simp
  have hq0 : Real.sqrt ((0:ℝ) ^ 2 + δ ^ 2) - δ = 0 := by
    rw [show ((0:ℝ)) ^ 2 + δ ^ 2 = δ ^ 2 by ring, Real.sqrt_sq hδ.le, sub_self]
  have hcore : HasGaussWeakGrad
      (fun x => Real.sqrt (((u : EuclideanSpace ℝ (Fin n) → ℝ) x) ^ 2 + δ ^ 2) - δ)
      (fun x => ((u : EuclideanSpace ℝ (Fin n) → ℝ) x
          / Real.sqrt (((u : EuclideanSpace ℝ (Fin n) → ℝ) x) ^ 2 + δ ^ 2))
        • (Real.sqrt 2 •
            (GaussD u : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) x)) :=
    GaussWeakGradChainRule (fun t => Real.sqrt (t ^ 2 + δ ^ 2) - δ)
      (fun t => t / Real.sqrt (t ^ 2 + δ ^ 2)) δ⁻¹ (by positivity)
      hd1 hQc hb1 hLip hLip' hq0
      (u : EuclideanSpace ℝ (Fin n) → ℝ)
      (fun x => Real.sqrt 2 •
        (GaussD u : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) x)
      (Lp.memLp u) hGL2 hGu
  -- transfer to `w` and `W`
  have hGW : HasGaussWeakGrad (w : EuclideanSpace ℝ (Fin n) → ℝ)
      (fun x => Real.sqrt 2 •
        (W : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) x) := by
    refine GaussWeakGradAECongr _ _ _ _ hw.symm ?_ hcore
    filter_upwards [hWcoe] with x hx
    rw [hx, smul_comm]
  obtain ⟨hmem, hGD⟩ := GaussDWitness w W hGW
  exact ⟨hmem, by rw [hGD]; exact hWcoe⟩
