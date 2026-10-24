import GaussianRiesz.CoordinateEndpointBound
import GaussianRiesz.GaussLebesgueBallComparison
open MeasureTheory Metric
open scoped ENNReal
theorem CoordinateEndpointLevelSetSmall {n : ℕ}
    (T : Lp ℝ 1 (GaussMeasure n) →ₗ[ℝ]
      (EuclideanSpace ℝ (Fin n) →ₘ[GaussMeasure n] EuclideanSpace ℝ (Fin n)))
    (hext : ∀ v : Lp ℝ 2 (GaussMeasure n),
      T (ToL1 v) = (RieszTransform v : EuclideanSpace ℝ (Fin n)
        →ₘ[GaussMeasure n] EuclideanSpace ℝ (Fin n)))
    (hT : ∀ (f : Lp ℝ 1 (GaussMeasure n)) (t : ℝ), 0 < t →
      ENNReal.ofReal t * GaussMeasure n {x | t < ‖T f x‖} ≤ ENNReal.ofReal (2 * ‖f‖))
    (j : Fin n) (R : ℝ) (hR : 1 ≤ R) :
    ∃ K : ℝ, 0 < K ∧
      ∀ (h : Lp ℝ 1 (GaussMeasure n)) (x : EuclideanSpace ℝ (Fin n)) (ε Φ : ℝ),
        ‖x‖ ≤ R → 0 < ε → ε ≤ 1 → 0 ≤ Φ →
        (∫ y, |(h : EuclideanSpace ℝ (Fin n) → ℝ) y| ∂(GaussMeasure n)
            ≤ Φ * (volume (ball x ε)).toReal) →
        GaussMeasure n {z : EuclideanSpace ℝ (Fin n) |
            z ∈ ball x (ε / 2)
              ∧ K * Φ < |(T h : EuclideanSpace ℝ (Fin n)
                  → EuclideanSpace ℝ (Fin n)) z j|}
          ≤ GaussMeasure n (ball x (ε / 2)) / 4 := by
  haveI : Nonempty (Fin n) := ⟨j⟩
  have hdim : Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) = n := by simp
  obtain ⟨-, cl2, -, -⟩ := (GaussLebesgueBallComparison (n := n))
  obtain ⟨a, ha0, haval⟩ : ∃ a : ℝ, 0 < a
      ∧ a = Real.pi ^ (-(n:ℝ)/2) * Real.exp (-(R + 2) ^ 2) := ⟨_, by positivity, rfl⟩
  refine ⟨8 * 2 ^ n / a, by positivity, ?_⟩
  intro h x ε Φ hxR hε0 hε1 hΦ0 hnorm
  obtain ⟨V, hV0, hVval⟩ : ∃ V : ℝ, 0 ≤ V ∧ V = (volume (ball x ε)).toReal :=
    ⟨_, ENNReal.toReal_nonneg, rfl⟩
  rw [← hVval] at hnorm
  have hVfin : volume (ball x ε) ≠ ⊤ := measure_ball_lt_top.ne
  have hVeq : volume (ball x ε) = ENNReal.ofReal V := by
    rw [hVval, ENNReal.ofReal_toReal hVfin]
  -- the halved ball has volume 2^{-n} times the whole one
  have hhalf : volume (ball x (ε / 2))
      = ENNReal.ofReal (1 / 2 ^ n) * volume (ball x ε) := by
    rw [Measure.addHaar_ball volume x (by positivity : (0:ℝ) ≤ ε / 2),
      Measure.addHaar_ball volume x hε0.le, hdim,
      show (ε / 2) ^ n = (1 / 2 ^ n) * ε ^ n from by rw [div_pow]; ring,
      ENNReal.ofReal_mul (by positivity)]
    ring
  -- the Gaussian lower bound on the halved ball
  have hBsub : ball x (ε / 2) ⊆ closedBall (0 : EuclideanSpace ℝ (Fin n)) (R + 2) := by
    intro y hy
    have h1 : ‖y - x‖ < ε / 2 := by simpa [mem_ball, dist_eq_norm] using hy
    have h2 : ‖y‖ - ‖x‖ ≤ ‖y - x‖ := norm_sub_norm_le y x
    simp only [mem_closedBall, dist_zero_right]
    linarith
  have hlow : ENNReal.ofReal a * volume (ball x (ε / 2))
      ≤ GaussMeasure n (ball x (ε / 2)) := by
    rw [haval]
    exact cl2 (R + 2) (ball x (ε / 2)) measurableSet_ball hBsub
  -- the target quantity, as an `ofReal`
  have hdiv4 : ENNReal.ofReal (a * (1 / 2 ^ n) * V / 4)
      ≤ GaussMeasure n (ball x (ε / 2)) / 4 := by
    have heq : ENNReal.ofReal a * volume (ball x (ε / 2))
        = ENNReal.ofReal (a * (1 / 2 ^ n) * V) := by
      rw [hhalf, hVeq, ← ENNReal.ofReal_mul (by positivity),
        ← ENNReal.ofReal_mul ha0.le]
      congr 1
      ring
    calc ENNReal.ofReal (a * (1 / 2 ^ n) * V / 4)
        = ENNReal.ofReal (a * (1 / 2 ^ n) * V) / 4 := by
          rw [ENNReal.ofReal_div_of_pos (by norm_num)]
          norm_num
      _ = (ENNReal.ofReal a * volume (ball x (ε / 2))) / 4 := by rw [heq]
      _ ≤ GaussMeasure n (ball x (ε / 2)) / 4 := ENNReal.div_le_div_right hlow 4
  -- the L^1 norm of h
  have hnorm' : ‖h‖ ≤ Φ * V := by
    rw [L1.norm_eq_integral_norm]
    simpa [Real.norm_eq_abs] using hnorm
  rcases eq_or_lt_of_le hΦ0 with hΦ | hΦ
  · -- the degenerate case `Φ = 0`: `h` is the zero class and the level set is null
    have hn0 : ‖h‖ = 0 := by
      have h1 : (0:ℝ) ≤ ‖h‖ := norm_nonneg h
      have h2 : ‖h‖ ≤ 0 := by rw [← hΦ] at hnorm'; linarith [hnorm']
      linarith
    have hh0 : h = 0 := norm_eq_zero.1 hn0
    have hae : ∀ᵐ z ∂(GaussMeasure n),
        (T h : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) z = 0 := by
      have h0 : (T h : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
          =ᵐ[GaussMeasure n] 0 := by
        rw [hh0, map_zero]; exact AEEqFun.coeFn_zero
      filter_upwards [h0] with z hz
      simpa using hz
    have hsub : {z : EuclideanSpace ℝ (Fin n) |
          z ∈ ball x (ε / 2) ∧ (8 * 2 ^ n / a) * Φ
            < |(T h : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) z j|}
        ⊆ {z : EuclideanSpace ℝ (Fin n) |
          ¬ ((T h : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) z = 0) } := by
      intro z hz
      obtain ⟨-, hz2⟩ := hz
      rw [← hΦ, mul_zero] at hz2
      intro hcon
      rw [hcon] at hz2
      simp at hz2
    rw [measure_mono_null hsub hae]
    exact zero_le
  · -- the main case `Φ > 0`
    have ht0 : (0:ℝ) < (8 * 2 ^ n / a) * Φ := by positivity
    have hce := CoordinateEndpointBound T hext hT h j ((8 * 2 ^ n / a) * Φ) ht0
    have hmono : GaussMeasure n {z : EuclideanSpace ℝ (Fin n) |
          z ∈ ball x (ε / 2) ∧ (8 * 2 ^ n / a) * Φ
            < |(T h : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) z j|}
        ≤ GaussMeasure n {z : EuclideanSpace ℝ (Fin n) | (8 * 2 ^ n / a) * Φ
            < |(T h : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) z j|} :=
      measure_mono (fun z hz => hz.2)
    refine le_trans hmono (le_trans ?_ hdiv4)
    -- rearrange the weak-type inequality
    have htne : ENNReal.ofReal ((8 * 2 ^ n / a) * Φ) ≠ 0 := by
      simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]; exact ht0
    have hrearr : GaussMeasure n {z : EuclideanSpace ℝ (Fin n) | (8 * 2 ^ n / a) * Φ
          < |(T h : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) z j|}
        ≤ (ENNReal.ofReal ((8 * 2 ^ n / a) * Φ))⁻¹ * ENNReal.ofReal (2 * ‖h‖) := by
      calc GaussMeasure n {z : EuclideanSpace ℝ (Fin n) | (8 * 2 ^ n / a) * Φ
              < |(T h : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) z j|}
          = (ENNReal.ofReal ((8 * 2 ^ n / a) * Φ))⁻¹
              * (ENNReal.ofReal ((8 * 2 ^ n / a) * Φ)
                * GaussMeasure n {z : EuclideanSpace ℝ (Fin n) | (8 * 2 ^ n / a) * Φ
                  < |(T h : EuclideanSpace ℝ (Fin n)
                      → EuclideanSpace ℝ (Fin n)) z j|}) := by
            rw [← mul_assoc, ENNReal.inv_mul_cancel htne ENNReal.ofReal_ne_top, one_mul]
        _ ≤ (ENNReal.ofReal ((8 * 2 ^ n / a) * Φ))⁻¹ * ENNReal.ofReal (2 * ‖h‖) :=
            mul_le_mul' le_rfl hce
    refine le_trans hrearr ?_
    rw [← ENNReal.ofReal_inv_of_pos ht0, ← ENNReal.ofReal_mul (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [inv_mul_eq_div, div_le_iff₀ ht0,
      show a * (1 / 2 ^ n) * V / 4 * ((8 * 2 ^ n / a) * Φ) = 2 * (V * Φ) from by
        field_simp; ring]
    nlinarith [hnorm', hΦ.le, hV0]
