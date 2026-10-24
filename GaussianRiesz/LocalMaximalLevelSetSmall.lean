import GaussianRiesz.GaussLebesgueBallComparison
open MeasureTheory Metric
open scoped ENNReal
theorem LocalMaximalLevelSetSmall {n : ℕ} (hn : 0 < n) (R : ℝ) (hR : 1 ≤ R) :
    ∃ K : ℝ, 0 < K ∧
      ∀ (u : EuclideanSpace ℝ (Fin n) → ℝ) (x : EuclideanSpace ℝ (Fin n)) (ε Ψ : ℝ),
        ‖x‖ ≤ R → 0 < ε → ε ≤ 1 → 0 ≤ Ψ → (∀ y, 0 ≤ u y) →
        AEMeasurable u volume →
        (∫⁻ y in closedBall x (ε / 2), ‖u y‖ₑ
            ≤ ENNReal.ofReal Ψ * volume (closedBall x (ε / 2))) →
        GaussMeasure n {z : EuclideanSpace ℝ (Fin n) |
            z ∈ ball x (ε / 2) ∧ K * Ψ < u z}
          ≤ GaussMeasure n (ball x (ε / 2)) / 4 := by
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have hdim : Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) = n := by simp
  obtain ⟨cl1, cl2, -, cl4⟩ := (GaussLebesgueBallComparison (n := n))
  obtain ⟨p, hp0, hpval⟩ : ∃ p : ℝ, 0 < p ∧ p = Real.pi ^ (-(n:ℝ)/2) :=
    ⟨_, by positivity, rfl⟩
  obtain ⟨a, ha0, haval⟩ : ∃ a : ℝ, 0 < a
      ∧ a = Real.pi ^ (-(n:ℝ)/2) * Real.exp (-(R + 2) ^ 2) := ⟨_, by positivity, rfl⟩
  have hpa : p / (4 * Real.exp ((R + 2) ^ 2)) = a / 4 := by
    rw [hpval, haval, Real.exp_neg]
    ring
  refine ⟨4 * Real.exp ((R + 2) ^ 2), by positivity, ?_⟩
  intro u x ε Ψ hxR hε0 hε1 hΨ0 hu0 humeas hmax
  have hSmeas : MeasurableSet (closedBall x (ε / 2)) := measurableSet_closedBall
  have hBsubS : ball x (ε / 2) ⊆ closedBall x (ε / 2) := ball_subset_closedBall
  -- the closed and open balls have the same volume
  have hvol : volume (closedBall x (ε / 2)) = volume (ball x (ε / 2)) := by
    rw [Measure.addHaar_closedBall volume x (by positivity : (0:ℝ) ≤ ε / 2),
      Measure.addHaar_ball volume x (by positivity : (0:ℝ) ≤ ε / 2)]
  -- the Gaussian lower bound on the ball
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
  have henorm : ∀ y : EuclideanSpace ℝ (Fin n), ‖u y‖ₑ = ENNReal.ofReal (u y) := by
    intro y
    rw [Real.enorm_eq_ofReal_abs, abs_of_nonneg (hu0 y)]
  rcases eq_or_lt_of_le hΨ0 with hΨ | hΨ
  · -- the degenerate case `Psi = 0`: `u` vanishes a.e. on the ball
    have hzero : ∫⁻ y in closedBall x (ε / 2), ‖u y‖ₑ = 0 := by
      refine le_antisymm ?_ (by simp)
      rw [← hΨ] at hmax
      simpa using hmax
    have hae0 : (fun y => ‖u y‖ₑ) =ᵐ[volume.restrict (closedBall x (ε / 2))] 0 :=
      (lintegral_eq_zero_iff' (μ := volume.restrict (closedBall x (ε / 2)))
        humeas.enorm.restrict).1 hzero
    have hae' : ∀ᵐ y ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
        y ∈ closedBall x (ε / 2) → u y = 0 := by
      rw [← ae_restrict_iff' hSmeas]
      filter_upwards [hae0] with y hy
      have : ‖u y‖ₑ = 0 := by simpa using hy
      simpa [henorm y, ENNReal.ofReal_eq_zero] using le_antisymm (by simpa [henorm y] using this.le) (hu0 y)
    have hnull : volume {z : EuclideanSpace ℝ (Fin n) |
        z ∈ ball x (ε / 2) ∧ (4 * Real.exp ((R + 2) ^ 2)) * Ψ < u z} = 0 := by
      refine measure_mono_null ?_ hae'
      intro z hz
      obtain ⟨hz1, hz2⟩ := hz
      rw [← hΨ, mul_zero] at hz2
      intro hcon
      exact absurd (hcon (hBsubS hz1)) (ne_of_gt hz2)
    rw [cl4 _ |>.2 hnull]
    exact zero_le
  · -- the main case `Psi > 0`
    have ht0 : (0:ℝ) < (4 * Real.exp ((R + 2) ^ 2)) * Ψ := by positivity
    have hE : NullMeasurableSet {z : EuclideanSpace ℝ (Fin n) |
        z ∈ ball x (ε / 2) ∧ (4 * Real.exp ((R + 2) ^ 2)) * Ψ < u z} volume := by
      have h1 : NullMeasurableSet
          {z : EuclideanSpace ℝ (Fin n) |
            (4 * Real.exp ((R + 2) ^ 2)) * Ψ < u z} volume :=
        (humeas.nullMeasurable measurableSet_Ioi : NullMeasurableSet (u ⁻¹' Set.Ioi _) volume)
      exact (measurableSet_ball.nullMeasurableSet).inter h1
    -- Chebyshev on the level set
    have hcheb : ENNReal.ofReal ((4 * Real.exp ((R + 2) ^ 2)) * Ψ)
          * volume {z : EuclideanSpace ℝ (Fin n) |
            z ∈ ball x (ε / 2) ∧ (4 * Real.exp ((R + 2) ^ 2)) * Ψ < u z}
        ≤ ENNReal.ofReal Ψ * volume (ball x (ε / 2)) := by
      calc ENNReal.ofReal ((4 * Real.exp ((R + 2) ^ 2)) * Ψ)
            * volume {z : EuclideanSpace ℝ (Fin n) |
              z ∈ ball x (ε / 2) ∧ (4 * Real.exp ((R + 2) ^ 2)) * Ψ < u z}
          = ∫⁻ _y in {z : EuclideanSpace ℝ (Fin n) |
              z ∈ ball x (ε / 2) ∧ (4 * Real.exp ((R + 2) ^ 2)) * Ψ < u z},
              ENNReal.ofReal ((4 * Real.exp ((R + 2) ^ 2)) * Ψ) := by
            rw [setLIntegral_const]
        _ ≤ ∫⁻ y in {z : EuclideanSpace ℝ (Fin n) |
              z ∈ ball x (ε / 2) ∧ (4 * Real.exp ((R + 2) ^ 2)) * Ψ < u z}, ‖u y‖ₑ := by
            refine lintegral_mono_ae ?_
            filter_upwards [ae_restrict_mem₀ hE] with y hy
            rw [henorm y]
            exact ENNReal.ofReal_le_ofReal hy.2.le
        _ ≤ ∫⁻ y in closedBall x (ε / 2), ‖u y‖ₑ :=
            lintegral_mono_set (fun z hz => hBsubS hz.1)
        _ ≤ ENNReal.ofReal Ψ * volume (closedBall x (ε / 2)) := hmax
        _ = ENNReal.ofReal Ψ * volume (ball x (ε / 2)) := by rw [hvol]
    -- divide through and convert to the Gaussian measure
    have htne : ENNReal.ofReal ((4 * Real.exp ((R + 2) ^ 2)) * Ψ) ≠ 0 := by
      simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]; exact ht0
    have hlam : volume {z : EuclideanSpace ℝ (Fin n) |
          z ∈ ball x (ε / 2) ∧ (4 * Real.exp ((R + 2) ^ 2)) * Ψ < u z}
        ≤ (ENNReal.ofReal ((4 * Real.exp ((R + 2) ^ 2)) * Ψ))⁻¹
            * (ENNReal.ofReal Ψ * volume (ball x (ε / 2))) := by
      calc volume {z : EuclideanSpace ℝ (Fin n) |
              z ∈ ball x (ε / 2) ∧ (4 * Real.exp ((R + 2) ^ 2)) * Ψ < u z}
          = (ENNReal.ofReal ((4 * Real.exp ((R + 2) ^ 2)) * Ψ))⁻¹
              * (ENNReal.ofReal ((4 * Real.exp ((R + 2) ^ 2)) * Ψ)
                * volume {z : EuclideanSpace ℝ (Fin n) |
                  z ∈ ball x (ε / 2) ∧ (4 * Real.exp ((R + 2) ^ 2)) * Ψ < u z}) := by
            rw [← mul_assoc, ENNReal.inv_mul_cancel htne ENNReal.ofReal_ne_top, one_mul]
        _ ≤ (ENNReal.ofReal ((4 * Real.exp ((R + 2) ^ 2)) * Ψ))⁻¹
              * (ENNReal.ofReal Ψ * volume (ball x (ε / 2))) := mul_le_mul' le_rfl hcheb
    have hΨne : Ψ ≠ 0 := ne_of_gt hΨ
    have hscalar : ENNReal.ofReal p
          * ((ENNReal.ofReal ((4 * Real.exp ((R + 2) ^ 2)) * Ψ))⁻¹ * ENNReal.ofReal Ψ)
        = ENNReal.ofReal (a / 4) := by
      rw [← ENNReal.ofReal_inv_of_pos ht0, ← ENNReal.ofReal_mul (by positivity),
        ← ENNReal.ofReal_mul hp0.le]
      congr 1
      rw [← hpa]
      field_simp
    calc GaussMeasure n {z : EuclideanSpace ℝ (Fin n) |
            z ∈ ball x (ε / 2) ∧ (4 * Real.exp ((R + 2) ^ 2)) * Ψ < u z}
        ≤ ENNReal.ofReal p * volume {z : EuclideanSpace ℝ (Fin n) |
            z ∈ ball x (ε / 2) ∧ (4 * Real.exp ((R + 2) ^ 2)) * Ψ < u z} := by
          rw [hpval]; exact cl1 _
      _ ≤ ENNReal.ofReal p * ((ENNReal.ofReal ((4 * Real.exp ((R + 2) ^ 2)) * Ψ))⁻¹
            * (ENNReal.ofReal Ψ * volume (ball x (ε / 2)))) := mul_le_mul' le_rfl hlam
      _ = (ENNReal.ofReal p * ((ENNReal.ofReal ((4 * Real.exp ((R + 2) ^ 2)) * Ψ))⁻¹
            * ENNReal.ofReal Ψ)) * volume (ball x (ε / 2)) := by ring
      _ = ENNReal.ofReal (a / 4) * volume (ball x (ε / 2)) := by rw [hscalar]
      _ = (ENNReal.ofReal a * volume (ball x (ε / 2))) / 4 := by
          rw [ENNReal.ofReal_div_of_pos (by norm_num)]
          norm_num
          rw [div_eq_mul_inv]
          exact mul_right_comm _ _ _
      _ ≤ GaussMeasure n (ball x (ε / 2)) / 4 := ENNReal.div_le_div_right hlow 4
