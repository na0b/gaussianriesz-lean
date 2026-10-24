import GaussianRiesz.GaussD
import GaussianRiesz.MehlerLebesgueKernel
open MeasureTheory
theorem MehlerKernelXDerivative {n : ℕ} (s : ℝ) (hs : 0 < s)
    (x y : EuclideanSpace ℝ (Fin n)) (j : Fin n) :
    DifferentiableAt ℝ (fun w : EuclideanSpace ℝ (Fin n) =>
        Real.pi ^ (-(n : ℝ) / 2) * (1 - Real.exp (-2 * s)) ^ (-(n : ℝ) / 2)
          * Real.exp (-‖Real.exp (-s) • w - y‖ ^ 2 / (1 - Real.exp (-2 * s)))) x
      ∧ (Real.sqrt 2)⁻¹ *
          fderiv ℝ (fun w : EuclideanSpace ℝ (Fin n) =>
              Real.pi ^ (-(n : ℝ) / 2) * (1 - Real.exp (-2 * s)) ^ (-(n : ℝ) / 2)
                * Real.exp (-‖Real.exp (-s) • w - y‖ ^ 2 / (1 - Real.exp (-2 * s)))) x
            (EuclideanSpace.single j (1 : ℝ))
        = Real.sqrt 2 * Real.exp (-s) * (y j - Real.exp (-s) * x j)
            / (1 - Real.exp (-2 * s))
          * (Real.pi ^ (-(n : ℝ) / 2) * (1 - Real.exp (-2 * s)) ^ (-(n : ℝ) / 2)
              * Real.exp (-‖Real.exp (-s) • x - y‖ ^ 2 / (1 - Real.exp (-2 * s)))) := by
  have hc : (0:ℝ) < 1 - Real.exp (-2 * s) := by
    have : Real.exp (-2 * s) < 1 := by
      rw [Real.exp_lt_one_iff]; linarith
    linarith
  set r : ℝ := Real.exp (-s) with hr
  set c : ℝ := 1 - Real.exp (-2 * s) with hcdef
  set K : ℝ := Real.pi ^ (-(n : ℝ) / 2) * c ^ (-(n : ℝ) / 2) with hK
  have h1 : HasFDerivAt (fun w : EuclideanSpace ℝ (Fin n) => r • w - y)
      (r • ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n))) x := by
    simpa using (((hasFDerivAt_id x).const_smul r).sub_const y)
  have h2 : HasFDerivAt (fun w : EuclideanSpace ℝ (Fin n) => ‖r • w - y‖ ^ 2)
      (2 • (innerSL ℝ (r • x - y)).comp
        (r • ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n)))) x := h1.norm_sq
  have hfeq : (fun w : EuclideanSpace ℝ (Fin n) => -‖r • w - y‖ ^ 2 / c)
      =ᶠ[nhds x] (fun w : EuclideanSpace ℝ (Fin n) => (-c⁻¹) * ‖r • w - y‖ ^ 2) :=
    Filter.Eventually.of_forall (fun w => by ring)
  have h3 := (h2.const_mul (-c⁻¹)).congr_of_eventuallyEq hfeq
  have h4 := h3.exp
  have h5 := h4.const_mul K
  refine ⟨h5.differentiableAt, ?_⟩
  rw [h5.fderiv]
  have hinner : ((innerSL ℝ (r • x - y)).comp
        (r • ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n))))
        (EuclideanSpace.single j (1:ℝ)) = r * (r * x j - y j) := by
    simp [EuclideanSpace.inner_single_right]
  have h2s : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hs2 : Real.sqrt 2 ≠ 0 := by positivity
  have hinv : (Real.sqrt 2)⁻¹ = Real.sqrt 2 / 2 := by
    rw [inv_eq_one_div, div_eq_div_iff hs2 (two_ne_zero)]
    linarith [h2s]
  simp only [smul_apply, smul_eq_mul, hinner, hinv]
  field_simp
  ring
