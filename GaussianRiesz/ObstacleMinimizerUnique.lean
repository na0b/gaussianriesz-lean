import GaussianRiesz.ObstacleFunctional
import GaussianRiesz.ObstacleCone
import GaussianRiesz.EnergyBil
import GaussianRiesz.EnergyConstantInvariance
import GaussianRiesz.EnergyFormBilinear
import GaussianRiesz.FractionalGap
import GaussianRiesz.ProjZeroCentering
import GaussianRiesz.L2IntoL1
open MeasureTheory
theorem ObstacleMinimizerUnique {n : ℕ} (F : Lp ℝ 2 (GaussMeasure n)) (m a : ℝ)
    (hm : m = ∫ x, (F : EuclideanSpace ℝ (Fin n) → ℝ) x ∂(GaussMeasure n)) (ha : m < a)
    (u₁ u₂ : Lp ℝ 2 (GaussMeasure n)) (hu₁ : u₁ ∈ ObstacleCone n) (hu₂ : u₂ ∈ ObstacleCone n)
    (hmin₁ : ∀ v ∈ ObstacleCone n, ObstacleFunctional F a u₁ ≤ ObstacleFunctional F a v)
    (hmin₂ : ∀ v ∈ ObstacleCone n, ObstacleFunctional F a u₂ ≤ ObstacleFunctional F a v) :
    u₁ = u₂ := by
  classical
  obtain ⟨hmix, hdiag, hbil, hsub⟩ := EnergyFormBilinear (n := n)
  obtain ⟨hV₁, hn₁⟩ := hu₁
  obtain ⟨hV₂, hn₂⟩ := hu₂
  -- the difference and the midpoint
  set w : Lp ℝ 2 (GaussMeasure n) := u₁ - u₂ with hwdef
  have hneg₂ : Energy ((-1 : ℝ) • u₂) ≠ ⊤ := (hsub u₂ u₂ (-1) hV₂ hV₂).2
  have hwadd : w = u₁ + (-1 : ℝ) • u₂ := by rw [hwdef, neg_one_smul, sub_eq_add_neg]
  have hwV : Energy w ≠ ⊤ := by
    rw [hwadd]; exact (hsub u₁ ((-1 : ℝ) • u₂) 0 hV₁ hneg₂).1
  set mid : Lp ℝ 2 (GaussMeasure n) := (1 / 2 : ℝ) • (u₁ + u₂) with hmiddef
  have hsumV : Energy (u₁ + u₂) ≠ ⊤ := (hsub u₁ u₂ 0 hV₁ hV₂).1
  have hmidV : Energy mid ≠ ⊤ := by
    rw [hmiddef]; exact (hsub (u₁ + u₂) (u₁ + u₂) (1 / 2 : ℝ) hsumV hsumV).2
  have hmidK : mid ∈ ObstacleCone n := by
    refine ⟨hmidV, ?_⟩
    filter_upwards [hn₁, hn₂, Lp.coeFn_smul (1 / 2 : ℝ) (u₁ + u₂), Lp.coeFn_add u₁ u₂]
      with x h1 h2 hsm hadd
    rw [hsm, Pi.smul_apply, smul_eq_mul, hadd, Pi.add_apply]
    nlinarith
  -- the energy parallelogram identity
  have hpar : (Energy mid).toReal
      = ((Energy u₁).toReal + (Energy u₂).toReal) / 2 - (Energy w).toReal / 4 := by
    have b₁₂ : EnergyBil u₁ u₂ = EnergyBil u₂ u₁ := (hbil u₁ u₂ u₂ 0 hV₁ hV₂ hV₂).2.2
    -- expand `EnergyBil mid mid`
    have hm1 : EnergyBil mid mid = (1 / 2 : ℝ) * EnergyBil (u₁ + u₂) mid := by
      rw [hmiddef]
      exact (hbil (u₁ + u₂) (u₁ + u₂) mid (1 / 2 : ℝ) hsumV hsumV hmidV).2.1
    have hm2 : EnergyBil (u₁ + u₂) mid = EnergyBil u₁ mid + EnergyBil u₂ mid :=
      (hbil u₁ u₂ mid 0 hV₁ hV₂ hmidV).1
    have hm3 : ∀ y : Lp ℝ 2 (GaussMeasure n), Energy y ≠ ⊤ →
        EnergyBil y mid = (1 / 2 : ℝ) * (EnergyBil y u₁ + EnergyBil y u₂) := by
      intro y hy
      rw [(hbil y y mid 0 hy hy hmidV).2.2, hmiddef,
        (hbil (u₁ + u₂) (u₁ + u₂) y (1 / 2 : ℝ) hsumV hsumV hy).2.1,
        (hbil u₁ u₂ y 0 hV₁ hV₂ hy).1,
        (hbil y y u₁ 0 hy hy hV₁).2.2, (hbil y y u₂ 0 hy hy hV₂).2.2]
    -- expand `EnergyBil w w`
    have hw2 : ∀ y : Lp ℝ 2 (GaussMeasure n), Energy y ≠ ⊤ →
        EnergyBil w y = EnergyBil u₁ y + (-1 : ℝ) * EnergyBil u₂ y := by
      intro y hy
      have h := (hbil u₁ ((-1 : ℝ) • u₂) y 0 hV₁ hneg₂ hy).1
      rw [← hwadd] at h
      rw [h, (hbil u₂ u₂ y (-1) hV₂ hV₂ hy).2.1]
    have hw1 : EnergyBil w w = EnergyBil u₁ u₁ + (-1 : ℝ) * (2 * EnergyBil u₁ u₂)
        + EnergyBil u₂ u₂ := by
      have a1 := hw2 w hwV
      have a2 := hw2 u₁ hV₁
      have a3 := hw2 u₂ hV₂
      have s1 : EnergyBil u₁ w = EnergyBil w u₁ := (hbil u₁ u₁ w 0 hV₁ hV₁ hwV).2.2
      have s2 : EnergyBil u₂ w = EnergyBil w u₂ := (hbil u₂ u₂ w 0 hV₂ hV₂ hwV).2.2
      have s3 : EnergyBil u₂ u₁ = EnergyBil u₁ u₂ := (hbil u₂ u₂ u₁ 0 hV₂ hV₂ hV₁).2.2
      rw [s1, s2, a2, a3, s3] at a1
      linarith [a1]
    rw [← hdiag mid hmidV, ← hdiag u₁ hV₁, ← hdiag u₂ hV₂, ← hdiag w hwV,
      hm1, hm2, hm3 u₁ hV₁, hm3 u₂ hV₂, hw1, b₁₂]
    ring
  -- the linear term is affine along the midpoint
  have hFa : MemLp (fun x => a - (F : EuclideanSpace ℝ (Fin n) → ℝ) x) 2 (GaussMeasure n) :=
    (memLp_const a).sub (Lp.memLp F)
  have hLin : ∀ y : Lp ℝ 2 (GaussMeasure n), Integrable
      (fun x => (a - (F : EuclideanSpace ℝ (Fin n) → ℝ) x)
        * (y : EuclideanSpace ℝ (Fin n) → ℝ) x) (GaussMeasure n) :=
    fun y => hFa.integrable_mul (Lp.memLp y)
  have hlinmid : (∫ x, (a - (F : EuclideanSpace ℝ (Fin n) → ℝ) x)
        * (mid : EuclideanSpace ℝ (Fin n) → ℝ) x ∂(GaussMeasure n))
      = ((∫ x, (a - (F : EuclideanSpace ℝ (Fin n) → ℝ) x)
            * (u₁ : EuclideanSpace ℝ (Fin n) → ℝ) x ∂(GaussMeasure n))
        + ∫ x, (a - (F : EuclideanSpace ℝ (Fin n) → ℝ) x)
            * (u₂ : EuclideanSpace ℝ (Fin n) → ℝ) x ∂(GaussMeasure n)) / 2 := by
    rw [div_eq_inv_mul, ← integral_add (hLin u₁) (hLin u₂), ← integral_const_mul]
    refine integral_congr_ae ?_
    filter_upwards [Lp.coeFn_smul (1 / 2 : ℝ) (u₁ + u₂), Lp.coeFn_add u₁ u₂] with x hsm hadd
    rw [hmiddef, hsm, Pi.smul_apply, smul_eq_mul, hadd, Pi.add_apply]
    ring
  -- minimality forces the difference to have zero energy
  have heq12 : ObstacleFunctional F a u₁ = ObstacleFunctional F a u₂ :=
    le_antisymm (hmin₁ u₂ ⟨hV₂, hn₂⟩) (hmin₂ u₁ ⟨hV₁, hn₁⟩)
  have hmidval : ObstacleFunctional F a mid
      = ObstacleFunctional F a u₁ - (Energy w).toReal / 8 := by
    rw [ObstacleFunctional, ObstacleFunctional, hpar, hlinmid]
    rw [ObstacleFunctional, ObstacleFunctional] at heq12
    linarith
  have hEw0 : (Energy w).toReal = 0 := by
    have h1 := hmin₁ mid hmidK
    rw [hmidval] at h1
    have h2 : (0 : ℝ) ≤ (Energy w).toReal := ENNReal.toReal_nonneg
    linarith
  have hEw : Energy w = 0 := by
    rcases ENNReal.toReal_eq_zero_iff (Energy w) |>.mp hEw0 with h | h
    · exact h
    · exact absurd h hwV
  -- rigidity: zero energy means `w` is the constant `d·1`
  set d : ℝ := ∫ x, (w : EuclideanSpace ℝ (Fin n) → ℝ) x ∂(GaussMeasure n) with hddef
  have hproj : FracPow (0 : ℝ) w = 0 := by
    have h1 : ENNReal.ofReal (‖FracPow (0 : ℝ) w‖ ^ 2) = 0 := by
      have h0 := FractionalGap w
      rw [hEw] at h0
      simpa using h0
    have h2 : ‖FracPow (0 : ℝ) w‖ ^ 2 ≤ 0 := ENNReal.ofReal_eq_zero.mp h1
    have h3 : ‖FracPow (0 : ℝ) w‖ = 0 := by nlinarith [norm_nonneg (FracPow (0 : ℝ) w)]
    exact norm_eq_zero.mp h3
  have hwconst : w = d • HermiteL2 (0 : Fin n → ℕ) := by
    have := ProjZeroCentering w
    rw [hproj] at this
    rw [hddef]
    linear_combination (norm := module) -this
  -- the constant mode is pinned by `a > m`
  have hconst : (HermiteL2 (0 : Fin n → ℕ) : EuclideanSpace ℝ (Fin n) → ℝ)
      =ᵐ[GaussMeasure n] fun _ => (1 : ℝ) := by
    filter_upwards [MemLp.coeFn_toLp (HermiteFunMemLp (0 : Fin n → ℕ))] with x hx
    rw [show ((HermiteL2 (0 : Fin n → ℕ) : Lp ℝ 2 (GaussMeasure n)) :
      EuclideanSpace ℝ (Fin n) → ℝ) x = HermiteFun (0 : Fin n → ℕ) x from hx]
    simp [HermiteFun, Hermite1Zero]
  have hu1 : u₁ = u₂ + d • HermiteL2 (0 : Fin n → ℕ) := by
    rw [← hwconst, hwdef]; abel
  have hEeq : Energy u₁ = Energy u₂ := by
    rw [hu1]; exact (EnergyConstantInvariance u₂ d).2
  -- equality of the functionals then forces the linear terms to agree
  have hlineq : (∫ x, (a - (F : EuclideanSpace ℝ (Fin n) → ℝ) x)
        * (w : EuclideanSpace ℝ (Fin n) → ℝ) x ∂(GaussMeasure n)) = 0 := by
    rw [ObstacleFunctional, ObstacleFunctional, hEeq] at heq12
    have hsplit : (∫ x, (a - (F : EuclideanSpace ℝ (Fin n) → ℝ) x)
        * (w : EuclideanSpace ℝ (Fin n) → ℝ) x ∂(GaussMeasure n))
        = (∫ x, (a - (F : EuclideanSpace ℝ (Fin n) → ℝ) x)
            * (u₁ : EuclideanSpace ℝ (Fin n) → ℝ) x ∂(GaussMeasure n))
          - ∫ x, (a - (F : EuclideanSpace ℝ (Fin n) → ℝ) x)
            * (u₂ : EuclideanSpace ℝ (Fin n) → ℝ) x ∂(GaussMeasure n) := by
      rw [← integral_sub (hLin u₁) (hLin u₂)]
      refine integral_congr_ae ?_
      filter_upwards [Lp.coeFn_sub u₁ u₂] with x hx
      rw [hwdef, hx, Pi.sub_apply]
      ring
    rw [hsplit]
    linarith
  have hdm : d * (a - m) = 0 := by
    have hIf : Integrable (F : EuclideanSpace ℝ (Fin n) → ℝ) (GaussMeasure n) :=
      (Lp.memLp F).integrable (by norm_num)
    have h1 : (∫ x, (a - (F : EuclideanSpace ℝ (Fin n) → ℝ) x)
        * (w : EuclideanSpace ℝ (Fin n) → ℝ) x ∂(GaussMeasure n))
        = d * (a - m) := by
      have h2 : (∫ x, (a - (F : EuclideanSpace ℝ (Fin n) → ℝ) x)
          * (w : EuclideanSpace ℝ (Fin n) → ℝ) x ∂(GaussMeasure n))
          = ∫ x, d * (a - (F : EuclideanSpace ℝ (Fin n) → ℝ) x) ∂(GaussMeasure n) := by
        refine integral_congr_ae ?_
        filter_upwards [hwconst ▸ Lp.coeFn_smul d (HermiteL2 (0 : Fin n → ℕ)), hconst]
          with x hx h1
        rw [hx, Pi.smul_apply, h1, smul_eq_mul]
        ring
      rw [h2, integral_const_mul, integral_sub (integrable_const a) hIf, integral_const,
        show (GaussMeasure n).real Set.univ = 1 by simp, smul_eq_mul, one_mul, hm]
    rw [← h1, hlineq]
  have hd0 : d = 0 := by
    rcases mul_eq_zero.mp hdm with h | h
    · exact h
    · exact absurd h (by linarith : a - m ≠ 0)
  have : w = 0 := by rw [hwconst, hd0, zero_smul]
  rw [hwdef] at this
  exact sub_eq_zero.mp this
