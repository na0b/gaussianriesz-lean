module

public import GaussianRiesz.GaussRieszKernel
public import GaussianRiesz.TauPowerIntegralBounds
public import GaussianRiesz.GaussRieszKernelNearFDerivBound
public import GaussianRiesz.GaussRieszKernelNearSliceL1Bound

@[expose] public section
open MeasureTheory Filter Topology
theorem GaussRieszKernelNearBounds {n : ℕ} (j : Fin n) (R : ℝ) (hR : 0 < R) :
    ∃ C : ℝ, 0 < C ∧
      (∀ x y : EuclideanSpace ℝ (Fin n), ‖x‖ ≤ R + 1 → 0 < ‖x - y‖ → ‖x - y‖ ≤ 2 →
          IntegrableOn (fun r : ℝ =>
              (y j - r * x j) / ((1 - r ^ 2) ^ ((n : ℝ) / 2 + 1) * Real.sqrt (-Real.log r))
                * Real.exp (-‖r • x - y‖ ^ 2 / (1 - r ^ 2))) (Set.Ioo (0 : ℝ) 1) volume
            ∧ |GaussRieszKernel j x y| ≤ C / ‖x - y‖ ^ n
            ∧ ∃ g : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ,
                HasFDerivAt (fun w : EuclideanSpace ℝ (Fin n) => GaussRieszKernel j w y) g x
                  ∧ ‖g‖ ≤ C / ‖x - y‖ ^ (n + 1))
        ∧ (∀ x y z : EuclideanSpace ℝ (Fin n), ‖x‖ ≤ R → 0 < ‖x - y‖ → ‖x - y‖ ≤ 1 →
            ‖x - z‖ ≤ ‖x - y‖ / 2 →
            |GaussRieszKernel j x y - GaussRieszKernel j z y|
              ≤ C * ‖x - z‖ / ‖x - y‖ ^ (n + 1)) := by
  classical
  have hcn : (0:ℝ) < Real.sqrt 2 * Real.pi ^ (-((n : ℝ) + 1) / 2) := by positivity
  obtain ⟨M, hM, hMR⟩ : ∃ M : ℝ, 3 ≤ M ∧ M = R + 3 := ⟨R + 3, by linarith, rfl⟩
  -- antitonicity of `t ↦ t ^ (-s)` and the quotient identity
  have hanti : ∀ u v s : ℝ, 0 < u → u ≤ v → 0 ≤ s → v ^ (-s) ≤ u ^ (-s) := by
    intro u v s hu huv hs
    rw [Real.rpow_neg hu.le, Real.rpow_neg (by linarith)]
    exact inv_anti₀ (Real.rpow_pos_of_pos hu _) (Real.rpow_le_rpow hu.le huv hs)
  have hdivrpow0 : ∀ t u s : ℝ, 0 ≤ t → 0 < u → (t / u) ^ (-s) = t ^ (-s) * u ^ s := by
    intro t u s ht hu
    rw [Real.div_rpow ht hu.le, Real.rpow_neg hu.le s, div_eq_mul_inv, inv_inv]
  -- the `rpow`-to-`npow` conversions used in the final assembly
  have hrn : ∀ d : ℝ, 0 < d → d ^ (-(n:ℝ)) = (d ^ n)⁻¹ := by
    intro d hd
    rw [Real.rpow_neg hd.le, Real.rpow_natCast]
  have hrn1 : ∀ d : ℝ, 0 < d → d ^ (-((n:ℝ) + 1)) = (d ^ (n + 1))⁻¹ := by
    intro d hd
    rw [show -((n:ℝ) + 1) = -(((n + 1 : ℕ) : ℝ)) from by push_cast; ring,
      Real.rpow_neg hd.le, Real.rpow_natCast]
  -- the `tau` power-integral fact used in the final assembly
  have h5 := TauPowerIntegralBounds.2
  -- STEP 2 of the `.tex`: clause (1)(a) and the `tau`-integral behind clause (1)(b)
  obtain ⟨A, hApos, hA⟩ := GaussRieszKernelNearSliceL1Bound j M hM
  -- STEP 3 of the `.tex`: clause (1)(c), by differentiation under the integral sign
  obtain ⟨B, hBpos, hB⟩ := GaussRieszKernelNearFDerivBound j R M hR hMR
  -- the hypotheses of clause (1) hold at every `x` of the stated range
  have hyM : ∀ x y : EuclideanSpace ℝ (Fin n), ‖x‖ ≤ R + 1 → ‖x - y‖ ≤ 2 → ‖y‖ ≤ M := by
    intro x y hxR hd2
    have h1 : ‖y‖ - ‖x‖ ≤ ‖y - x‖ := norm_sub_norm_le y x
    rw [norm_sub_rev] at h1
    rw [hMR]; linarith
  have hxM : ∀ x : EuclideanSpace ℝ (Fin n), ‖x‖ ≤ R + 1 → ‖x‖ ≤ M := by
    intro x hxR; rw [hMR]; linarith
  -- the final constant
  refine ⟨max (Real.sqrt 2 * Real.pi ^ (-((n : ℝ) + 1) / 2) * A) (2 ^ ((n:ℝ) + 1) * B) + 1,
    ?_, ?_, ?_⟩
  · have h1 : (0:ℝ) ≤ max (Real.sqrt 2 * Real.pi ^ (-((n : ℝ) + 1) / 2) * A)
        (2 ^ ((n:ℝ) + 1) * B) :=
      le_trans (by positivity) (le_max_left _ _)
    linarith
  · -- clause (1)
    intro x y hxR hd0 hd2
    obtain ⟨hint, hbd⟩ := hA x y (hxM x hxR) (hyM x y hxR hd2) hd0 hd2
    refine ⟨hint, ?_, ?_⟩
    · -- clause (1)(b)
      have hker : GaussRieszKernel j x y
          = Real.sqrt 2 * Real.pi ^ (-((n : ℝ) + 1) / 2) * ∫ r in Set.Ioo (0:ℝ) 1,
            (y j - r * x j) / ((1 - r ^ 2) ^ ((n : ℝ) / 2 + 1) * Real.sqrt (-Real.log r))
              * Real.exp (-‖r • x - y‖ ^ 2 / (1 - r ^ 2)) := by
        rw [GaussRieszKernel]
      have habs : |∫ r in Set.Ioo (0:ℝ) 1,
            (y j - r * x j) / ((1 - r ^ 2) ^ ((n : ℝ) / 2 + 1) * Real.sqrt (-Real.log r))
              * Real.exp (-‖r • x - y‖ ^ 2 / (1 - r ^ 2))|
          ≤ ∫ r in Set.Ioo (0:ℝ) 1,
            |(y j - r * x j) / ((1 - r ^ 2) ^ ((n : ℝ) / 2 + 1) * Real.sqrt (-Real.log r))
              * Real.exp (-‖r • x - y‖ ^ 2 / (1 - r ^ 2))| := by
        have h := norm_integral_le_integral_norm (μ := volume.restrict (Set.Ioo (0:ℝ) 1))
          (fun r : ℝ =>
            (y j - r * x j) / ((1 - r ^ 2) ^ ((n : ℝ) / 2 + 1) * Real.sqrt (-Real.log r))
              * Real.exp (-‖r • x - y‖ ^ 2 / (1 - r ^ 2)))
        simp only [Real.norm_eq_abs] at h
        exact h
      have hfin : (max (Real.sqrt 2 * Real.pi ^ (-((n : ℝ) + 1) / 2) * A) (2 ^ ((n:ℝ) + 1) * B) + 1) / ‖x - y‖ ^ n
          = (max (Real.sqrt 2 * Real.pi ^ (-((n : ℝ) + 1) / 2) * A) (2 ^ ((n:ℝ) + 1) * B) + 1) * ‖x - y‖ ^ (-(n:ℝ)) := by
        rw [hrn ‖x - y‖ hd0, div_eq_mul_inv]
      rw [hker, abs_mul, abs_of_pos hcn, hfin]
      have hstep : Real.sqrt 2 * Real.pi ^ (-((n : ℝ) + 1) / 2)
            * |∫ r in Set.Ioo (0:ℝ) 1,
              (y j - r * x j) / ((1 - r ^ 2) ^ ((n : ℝ) / 2 + 1) * Real.sqrt (-Real.log r))
                * Real.exp (-‖r • x - y‖ ^ 2 / (1 - r ^ 2))|
          ≤ Real.sqrt 2 * Real.pi ^ (-((n : ℝ) + 1) / 2) * (A * ‖x - y‖ ^ (-(n:ℝ))) :=
        mul_le_mul_of_nonneg_left (le_trans habs hbd) hcn.le
      refine le_trans hstep ?_
      have hle : Real.sqrt 2 * Real.pi ^ (-((n : ℝ) + 1) / 2) * A
          ≤ max (Real.sqrt 2 * Real.pi ^ (-((n : ℝ) + 1) / 2) * A) (2 ^ ((n:ℝ) + 1) * B) + 1 := by
        linarith [le_max_left (Real.sqrt 2 * Real.pi ^ (-((n : ℝ) + 1) / 2) * A)
          (2 ^ ((n:ℝ) + 1) * B)]
      have hd : (0:ℝ) < ‖x - y‖ ^ (-(n:ℝ)) := Real.rpow_pos_of_pos hd0 _
      calc Real.sqrt 2 * Real.pi ^ (-((n : ℝ) + 1) / 2) * (A * ‖x - y‖ ^ (-(n:ℝ)))
          = Real.sqrt 2 * Real.pi ^ (-((n : ℝ) + 1) / 2) * A * ‖x - y‖ ^ (-(n:ℝ)) := by ring
        _ ≤ (max (Real.sqrt 2 * Real.pi ^ (-((n : ℝ) + 1) / 2) * A) (2 ^ ((n:ℝ) + 1) * B) + 1)
              * ‖x - y‖ ^ (-(n:ℝ)) := mul_le_mul_of_nonneg_right hle hd.le
    · -- clause (1)(c)
      obtain ⟨g, hg1, hg2⟩ := hB x y hxR (hyM x y hxR hd2) hd0 hd2 hint
      refine ⟨g, hg1, ?_⟩
      have hfin : (max (Real.sqrt 2 * Real.pi ^ (-((n : ℝ) + 1) / 2) * A) (2 ^ ((n:ℝ) + 1) * B) + 1) / ‖x - y‖ ^ (n + 1)
          = (max (Real.sqrt 2 * Real.pi ^ (-((n : ℝ) + 1) / 2) * A) (2 ^ ((n:ℝ) + 1) * B) + 1) * ‖x - y‖ ^ (-((n:ℝ) + 1)) := by
        rw [hrn1 ‖x - y‖ hd0, div_eq_mul_inv]
      rw [hfin]
      have hpow1 : (1:ℝ) ≤ 2 ^ ((n:ℝ) + 1) := by
        refine Real.one_le_rpow (by norm_num) (by linarith)
      have hle : B ≤ max (Real.sqrt 2 * Real.pi ^ (-((n : ℝ) + 1) / 2) * A)
          (2 ^ ((n:ℝ) + 1) * B) + 1 := by
        have h1 : B ≤ 2 ^ ((n:ℝ) + 1) * B := by nlinarith [hBpos, hpow1]
        linarith [le_max_right (Real.sqrt 2 * Real.pi ^ (-((n : ℝ) + 1) / 2) * A)
          (2 ^ ((n:ℝ) + 1) * B)]
      have hd : (0:ℝ) < ‖x - y‖ ^ (-((n:ℝ) + 1)) := Real.rpow_pos_of_pos hd0 _
      exact le_trans hg2 (mul_le_mul_of_nonneg_right hle hd.le)
  · -- clause (2): STEP 4 of the `.tex`, the mean value inequality on a convex ball
    intro x y z hxR hd0 hd1' hxz
    have hyM2 : ‖y‖ ≤ M := hyM x y (by linarith) (by linarith)
    have hball : ∀ w ∈ Metric.closedBall x (‖x - y‖ / 2),
        ‖w‖ ≤ R + 1 ∧ 0 < ‖w - y‖ ∧ ‖w - y‖ ≤ 2 ∧ ‖x - y‖ / 2 ≤ ‖w - y‖ := by
      intro w hw
      have hwx : ‖w - x‖ ≤ ‖x - y‖ / 2 := by
        simpa [Metric.mem_closedBall, dist_eq_norm] using hw
      have h1 : ‖w‖ - ‖x‖ ≤ ‖w - x‖ := norm_sub_norm_le w x
      have h2 : ‖x - y‖ - ‖w - x‖ ≤ ‖w - y‖ := by
        have e1 : x - y = (w - y) - (w - x) := by abel
        have h3 := norm_sub_le (w - y) (w - x)
        rw [← e1] at h3; linarith
      have h4 : ‖w - y‖ ≤ ‖w - x‖ + ‖x - y‖ := by
        have e1 : w - y = (w - x) + (x - y) := by abel
        have h5 := norm_add_le (w - x) (x - y)
        rw [← e1] at h5; linarith
      exact ⟨by linarith, by linarith, by linarith, by linarith⟩
    have hintw : ∀ w ∈ Metric.closedBall x (‖x - y‖ / 2),
        IntegrableOn (fun r : ℝ =>
            (y j - r * w j) / ((1 - r ^ 2) ^ ((n : ℝ) / 2 + 1) * Real.sqrt (-Real.log r))
              * Real.exp (-‖r • w - y‖ ^ 2 / (1 - r ^ 2))) (Set.Ioo (0:ℝ) 1) volume := by
      intro w hw
      obtain ⟨hw1, hw2, hw3, hw4⟩ := hball w hw
      exact (hA w y (hxM w hw1) hyM2 hw2 hw3).1
    have hhalf : (‖x - y‖ / 2) ^ (-((n:ℝ) + 1))
        = 2 ^ ((n:ℝ) + 1) * ‖x - y‖ ^ (-((n:ℝ) + 1)) := by
      rw [hdivrpow0 ‖x - y‖ 2 ((n:ℝ) + 1) (norm_nonneg _) (by norm_num)]
      ring
    have hdw : ∀ w ∈ Metric.closedBall x (‖x - y‖ / 2),
        HasFDerivWithinAt (fun v : EuclideanSpace ℝ (Fin n) => GaussRieszKernel j v y)
          (fderiv ℝ (fun v : EuclideanSpace ℝ (Fin n) => GaussRieszKernel j v y) w)
          (Metric.closedBall x (‖x - y‖ / 2)) w := by
      intro w hw
      obtain ⟨hw1, hw2, hw3, hw4⟩ := hball w hw
      obtain ⟨g, hg1, hg2⟩ := hB w y hw1 hyM2 hw2 hw3 (hintw w hw)
      rw [hg1.fderiv]
      exact hg1.hasFDerivWithinAt
    have hbdw : ∀ w ∈ Metric.closedBall x (‖x - y‖ / 2),
        ‖fderiv ℝ (fun v : EuclideanSpace ℝ (Fin n) => GaussRieszKernel j v y) w‖
          ≤ 2 ^ ((n:ℝ) + 1) * B * ‖x - y‖ ^ (-((n:ℝ) + 1)) := by
      intro w hw
      obtain ⟨hw1, hw2, hw3, hw4⟩ := hball w hw
      obtain ⟨g, hg1, hg2⟩ := hB w y hw1 hyM2 hw2 hw3 (hintw w hw)
      rw [hg1.fderiv]
      refine le_trans hg2 ?_
      have ha := hanti (‖x - y‖ / 2) ‖w - y‖ ((n:ℝ) + 1) (by positivity) hw4 (by linarith)
      rw [hhalf] at ha
      calc B * ‖w - y‖ ^ (-((n:ℝ) + 1))
          ≤ B * (2 ^ ((n:ℝ) + 1) * ‖x - y‖ ^ (-((n:ℝ) + 1))) :=
            mul_le_mul_of_nonneg_left ha hBpos.le
        _ = 2 ^ ((n:ℝ) + 1) * B * ‖x - y‖ ^ (-((n:ℝ) + 1)) := by ring
    have hzmem : z ∈ Metric.closedBall x (‖x - y‖ / 2) := by
      simpa [Metric.mem_closedBall, dist_eq_norm, norm_sub_rev] using hxz
    have hmvt := Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le hdw hbdw
      (convex_closedBall x (‖x - y‖ / 2))
      (Metric.mem_closedBall_self (by positivity)) hzmem
    -- hmvt : ‖K z y - K x y‖ ≤ (2^(n+1) * B * d^(-(n+1))) * ‖z - x‖
    rw [Real.norm_eq_abs, abs_sub_comm,
      show ‖z - x‖ = ‖x - z‖ from norm_sub_rev z x] at hmvt
    have hfin : (max (Real.sqrt 2 * Real.pi ^ (-((n : ℝ) + 1) / 2) * A) (2 ^ ((n:ℝ) + 1) * B) + 1) * ‖x - z‖ / ‖x - y‖ ^ (n + 1)
        = (max (Real.sqrt 2 * Real.pi ^ (-((n : ℝ) + 1) / 2) * A) (2 ^ ((n:ℝ) + 1) * B) + 1) * ‖x - z‖ * ‖x - y‖ ^ (-((n:ℝ) + 1)) := by
      rw [hrn1 ‖x - y‖ hd0, div_eq_mul_inv]
    rw [hfin]
    have hle : 2 ^ ((n:ℝ) + 1) * B
        ≤ max (Real.sqrt 2 * Real.pi ^ (-((n : ℝ) + 1) / 2) * A) (2 ^ ((n:ℝ) + 1) * B) + 1 := by
      linarith [le_max_right (Real.sqrt 2 * Real.pi ^ (-((n : ℝ) + 1) / 2) * A)
        (2 ^ ((n:ℝ) + 1) * B)]
    have hd : (0:ℝ) < ‖x - y‖ ^ (-((n:ℝ) + 1)) := Real.rpow_pos_of_pos hd0 _
    refine le_trans hmvt ?_
    calc 2 ^ ((n:ℝ) + 1) * B * ‖x - y‖ ^ (-((n:ℝ) + 1)) * ‖x - z‖
        ≤ (max (Real.sqrt 2 * Real.pi ^ (-((n : ℝ) + 1) / 2) * A) (2 ^ ((n:ℝ) + 1) * B) + 1)
            * ‖x - y‖ ^ (-((n:ℝ) + 1)) * ‖x - z‖ := by
          have := mul_le_mul_of_nonneg_right hle hd.le
          exact mul_le_mul_of_nonneg_right this (norm_nonneg _)
      _ = (max (Real.sqrt 2 * Real.pi ^ (-((n : ℝ) + 1) / 2) * A) (2 ^ ((n:ℝ) + 1) * B) + 1)
            * ‖x - z‖ * ‖x - y‖ ^ (-((n:ℝ) + 1)) := by ring
