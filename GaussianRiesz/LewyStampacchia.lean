import GaussianRiesz.MultiplierPositive
import GaussianRiesz.DisjointCrossTermSign
import GaussianRiesz.L2IntoL1
import GaussianRiesz.PosPartConstSubMemLp
open MeasureTheory
-- binder retained for statement fidelity to the paper; intentionally unused in the proof
set_option linter.unusedVariables false
theorem LewyStampacchia {n : ℕ} (F : Lp ℝ 2 (GaussMeasure n))
    (hF : 0 ≤ᵐ[GaussMeasure n] (F : EuclideanSpace ℝ (Fin n) → ℝ)) (a : ℝ)
    (u : Lp ℝ 2 (GaussMeasure n)) (hu : u ∈ ObstacleCone n)
    (hmin : ∀ w ∈ ObstacleCone n, ObstacleFunctional F a u ≤ ObstacleFunctional F a w)
    (φ : Lp ℝ 2 (GaussMeasure n)) (hφ : φ ∈ ObstacleCone n) :
    ObstacleMultiplier F a u φ
      ≤ ∫ x, max (a - (F : EuclideanSpace ℝ (Fin n) → ℝ) x) 0
          * (φ : EuclideanSpace ℝ (Fin n) → ℝ) x ∂(GaussMeasure n) := by
  classical
  have hprob : IsProbabilityMeasure (GaussMeasure n) := GaussIsProb n
  obtain ⟨-, hdiag, hbil, hclosed⟩ := EnergyFormBilinear (n := n)
  obtain ⟨-, hneg⟩ := DisjointCrossTermSign (n := n)
  have huE : Energy u ≠ ⊤ := hu.1
  have hu0 := hu.2
  have hφE : Energy φ ≠ ⊤ := hφ.1
  have hφ0 := hφ.2
  -- the three bilinearity facts, named
  have hadd : ∀ v₁ v₂ w : Lp ℝ 2 (GaussMeasure n), Energy v₁ ≠ ⊤ → Energy v₂ ≠ ⊤ →
      Energy w ≠ ⊤ → EnergyBil (v₁ + v₂) w = EnergyBil v₁ w + EnergyBil v₂ w :=
    fun v₁ v₂ w h1 h2 hw => (hbil v₁ v₂ w 0 h1 h2 hw).1
  have hsmul : ∀ (v w : Lp ℝ 2 (GaussMeasure n)) (c : ℝ), Energy v ≠ ⊤ → Energy w ≠ ⊤ →
      EnergyBil (c • v) w = c * EnergyBil v w :=
    fun v w c h1 hw => (hbil v v w c h1 h1 hw).2.1
  have hsymm : ∀ v w : Lp ℝ 2 (GaussMeasure n), Energy v ≠ ⊤ → Energy w ≠ ⊤ →
      EnergyBil v w = EnergyBil w v :=
    fun v w h1 hw => (hbil v v w 0 h1 h1 hw).2.2
  have hsm : ∀ (v : Lp ℝ 2 (GaussMeasure n)) (c : ℝ), Energy v ≠ ⊤ → Energy (c • v) ≠ ⊤ :=
    fun v c hv => (hclosed v v c hv hv).2
  have hsum : ∀ v w : Lp ℝ 2 (GaussMeasure n), Energy v ≠ ⊤ → Energy w ≠ ⊤ →
      Energy (v + w) ≠ ⊤ := fun v w hv hw => (hclosed v w 0 hv hw).1
  -- THE POLARIZATION EXPANSION, which replaces Cauchy-Schwarz
  have hexpand : ∀ (x y : Lp ℝ 2 (GaussMeasure n)) (c : ℝ), Energy x ≠ ⊤ → Energy y ≠ ⊤ →
      (Energy (x + c • y)).toReal
        = (Energy x).toReal + 2 * c * EnergyBil x y + c ^ 2 * (Energy y).toReal := by
    intro x y c hx hy
    have hcy : Energy (c • y) ≠ ⊤ := hsm y c hy
    have hS : Energy (x + c • y) ≠ ⊤ := hsum x (c • y) hx hcy
    have e1 : (Energy (x + c • y)).toReal = EnergyBil (x + c • y) (x + c • y) :=
      (hdiag (x + c • y) hS).symm
    have e2 : EnergyBil (x + c • y) (x + c • y)
        = EnergyBil x (x + c • y) + c * EnergyBil y (x + c • y) := by
      rw [hadd x (c • y) (x + c • y) hx hcy hS, hsmul y (x + c • y) c hy hS]
    have e3 : EnergyBil x (x + c • y) = (Energy x).toReal + c * EnergyBil y x := by
      rw [hsymm x (x + c • y) hx hS, hadd x (c • y) x hx hcy hx,
        hsmul y x c hy hx, hdiag x hx]
    have e4 : EnergyBil y (x + c • y) = EnergyBil x y + c * (Energy y).toReal := by
      rw [hsymm y (x + c • y) hy hS, hadd x (c • y) y hx hcy hy,
        hsmul y y c hy hy, hdiag y hy, hsymm x y hx hy]
    have e5 : EnergyBil y x = EnergyBil x y := (hsymm y x hy hx)
    rw [e1, e2, e3, e4, e5]
    ring
  -- integrability package for the load terms
  have hFa : MemLp (fun x => (F : EuclideanSpace ℝ (Fin n) → ℝ) x - a) 2 (GaussMeasure n) :=
    (Lp.memLp F).sub (memLp_const a)
  have hk := PosPartConstSubMemLp F a
  have hintk : Integrable (fun x => max (a - (F : EuclideanSpace ℝ (Fin n) → ℝ) x) 0
      * (φ : EuclideanSpace ℝ (Fin n) → ℝ) x) (GaussMeasure n) :=
    hk.integrable_mul (Lp.memLp φ)
  have hintφ : Integrable (fun x => ((F : EuclideanSpace ℝ (Fin n) → ℝ) x - a)
      * (φ : EuclideanSpace ℝ (Fin n) → ℝ) x) (GaussMeasure n) :=
    hFa.integrable_mul (Lp.memLp φ)
  -- the Lipschitz map cutting out the negative part
  have hLipm : LipschitzWith 1 (fun t : ℝ => max (-t) 0) := by
    refine LipschitzWith.of_dist_le_mul fun x y => ?_
    simp only [Real.dist_eq, NNReal.coe_one, one_mul]
    calc |max (-x) 0 - max (-y) 0| ≤ |(-x) - (-y)| := abs_max_sub_max_le_abs _ _ _
      _ = |x - y| := by rw [neg_sub_neg, abs_sub_comm]
  -- MAIN ESTIMATE, for each `ε > 0`
  have key : ∀ ε : ℝ, 0 < ε →
      ObstacleMultiplier F a u φ
        ≤ (ε / 4) * (Energy φ).toReal
          + ∫ x, max (a - (F : EuclideanSpace ℝ (Fin n) → ℝ) x) 0
              * (φ : EuclideanSpace ℝ (Fin n) → ℝ) x ∂(GaussMeasure n) := by
    intro ε hε
    have hzE : Energy (u + (-ε) • φ) ≠ ⊤ := hsum u ((-ε) • φ) huE (hsm φ (-ε) hφE)
    -- the negative part of `z = u - εφ`, as an `L²` element
    have hzmmem : MemLp (fun x => max (-((u + (-ε) • φ : Lp ℝ 2 (GaussMeasure n)) :
        EuclideanSpace ℝ (Fin n) → ℝ) x) 0) 2 (GaussMeasure n) := by
      refine MemLp.of_le (Lp.memLp (u + (-ε) • φ)) ?_ ?_
      · exact aestronglyMeasurable_iff_aemeasurable.mpr
          ((Lp.aestronglyMeasurable (u + (-ε) • φ)).aemeasurable.neg.max aemeasurable_const)
      · filter_upwards with x
        rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
        rcases le_total (((u + (-ε) • φ : Lp ℝ 2 (GaussMeasure n)) :
            EuclideanSpace ℝ (Fin n) → ℝ) x) 0 with h | h
        · rw [max_eq_left (by linarith)]
          rw [abs_of_nonpos h]
        · rw [max_eq_right (by linarith)]
          positivity
    -- the negative part as an `L²` element, and its finite energy via `LatticeContraction`
    have hzmchar : ((MemLp.toLp _ hzmmem : Lp ℝ 2 (GaussMeasure n)) :
          EuclideanSpace ℝ (Fin n) → ℝ)
        =ᵐ[GaussMeasure n] fun x => max (-((u + (-ε) • φ : Lp ℝ 2 (GaussMeasure n)) :
          EuclideanSpace ℝ (Fin n) → ℝ) x) 0 := hzmmem.coeFn_toLp
    set zm : Lp ℝ 2 (GaussMeasure n) := MemLp.toLp _ hzmmem with hzmdef
    have hzmV := LatticeContraction (fun t : ℝ => max (-t) 0) hLipm (by simp)
      (u + (-ε) • φ) zm hzE hzmchar
    have hzmE : Energy zm ≠ ⊤ := hzmV.1
    have hzmint : Integrable (fun x => ((F : EuclideanSpace ℝ (Fin n) → ℝ) x - a)
        * (zm : EuclideanSpace ℝ (Fin n) → ℝ) x) (GaussMeasure n) :=
      hFa.integrable_mul (Lp.memLp zm)
    -- the competitor is `z⁺ = z + z⁻`; no lattice operation on `Lp` is needed
    have hzp0 : 0 ≤ᵐ[GaussMeasure n]
        (((u + (-ε) • φ) + zm : Lp ℝ 2 (GaussMeasure n)) :
          EuclideanSpace ℝ (Fin n) → ℝ) := by
      filter_upwards [Lp.coeFn_add (u + (-ε) • φ) zm, hzmchar] with x hx h2
      rw [hx]
      simp only [Pi.add_apply]
      rw [h2]
      rcases le_total (((u + (-ε) • φ : Lp ℝ 2 (GaussMeasure n)) :
          EuclideanSpace ℝ (Fin n) → ℝ) x) 0 with h | h
      · rw [max_eq_left (by linarith)]; simp only [Pi.zero_apply]; linarith
      · rw [max_eq_right (by linarith)]; simp only [Pi.zero_apply]; linarith
    have hzpcone : ((u + (-ε) • φ) + zm) ∈ ObstacleCone n := ⟨hsum _ _ hzE hzmE, hzp0⟩
    have hVI := VariationalInequality F a u hu hmin _ hzpcone
    -- the competitor difference, as an `Lp` identity and then pointwise
    have hdiff : ((u + (-ε) • φ) + zm) - u = zm + (-ε) • φ := by abel
    have hptw : ∀ᵐ x ∂(GaussMeasure n),
        ((((u + (-ε) • φ) + zm : Lp ℝ 2 (GaussMeasure n)) :
            EuclideanSpace ℝ (Fin n) → ℝ) x - (u : EuclideanSpace ℝ (Fin n) → ℝ) x)
          = (zm : EuclideanSpace ℝ (Fin n) → ℝ) x
            + (-ε) * (φ : EuclideanSpace ℝ (Fin n) → ℝ) x := by
      have h1 := Lp.coeFn_sub ((u + (-ε) • φ) + zm) u
      rw [hdiff] at h1
      have h2 := Lp.coeFn_add zm ((-ε) • φ)
      have h3 := Lp.coeFn_smul (-ε) φ
      filter_upwards [h1, h2, h3] with x e1 e2 e3
      simp only [Pi.sub_apply, Pi.add_apply] at e1 e2
      simp only [Pi.smul_apply, smul_eq_mul] at e3
      rw [← e1, e2, e3]
    -- bilinear expansion of the energy side
    have hBu : EnergyBil u (((u + (-ε) • φ) + zm) - u)
        = EnergyBil u zm + (-ε) * EnergyBil u φ := by
      rw [hdiff, hsymm u (zm + (-ε) • φ) huE (hsum zm ((-ε) • φ) hzmE (hsm φ (-ε) hφE)),
        hadd zm ((-ε) • φ) u hzmE (hsm φ (-ε) hφE) huE, hsmul φ u (-ε) hφE huE,
        hsymm zm u hzmE huE, hsymm φ u hφE huE]
    -- STEP 2: the energy term, by the polarization expansion -- no Cauchy-Schwarz
    have hstep2 : EnergyBil u zm ≤ (ε ^ 2 / 4) * (Energy φ).toReal := by
      -- NOTE: `rw [u = (u + (-ε)•φ) + ε•φ]` rewrites too much (the RHS contains `u`),
      -- so build the identity in the eliminating direction instead
      have hueq : (u + (-ε) • φ) + ε • φ = u := by module
      have h1 : EnergyBil u zm
          = EnergyBil (u + (-ε) • φ) zm + ε * EnergyBil φ zm := by
        rw [← hsmul φ zm ε hφE hzmE,
          ← hadd (u + (-ε) • φ) (ε • φ) zm hzE (hsm φ ε hφE) hzmE, hueq]
      have h2 : EnergyBil (u + (-ε) • φ) zm ≤ -(Energy zm).toReal :=
        hneg (u + (-ε) • φ) zm hzE hzmchar
      have h3 : (0 : ℝ) ≤ (Energy (zm + (-(ε / 2)) • φ)).toReal := ENNReal.toReal_nonneg
      rw [hexpand zm φ (-(ε / 2)) hzmE hφE] at h3
      have h3' : ε * EnergyBil zm φ
          ≤ (Energy zm).toReal + (ε ^ 2 / 4) * (Energy φ).toReal := by nlinarith [h3]
      have h4 : EnergyBil φ zm = EnergyBil zm φ := hsymm φ zm hφE hzmE
      rw [h1, h4]
      linarith [h2, h3']
    -- STEP 3: the load term
    have hload : - ∫ x, ((F : EuclideanSpace ℝ (Fin n) → ℝ) x - a)
            * (zm : EuclideanSpace ℝ (Fin n) → ℝ) x ∂(GaussMeasure n)
        ≤ ε * ∫ x, max (a - (F : EuclideanSpace ℝ (Fin n) → ℝ) x) 0
            * (φ : EuclideanSpace ℝ (Fin n) → ℝ) x ∂(GaussMeasure n) := by
      rw [← integral_neg, ← integral_const_mul]
      refine integral_mono_ae hzmint.neg (hintk.const_mul ε) ?_
      filter_upwards [hzmchar, hu0, hφ0, Lp.coeFn_add u ((-ε) • φ), Lp.coeFn_smul (-ε) φ]
        with x hzm hux hφx hadd' hsm'
      simp only [Pi.zero_apply] at hux hφx
      have hzx : ((u + (-ε) • φ : Lp ℝ 2 (GaussMeasure n)) :
          EuclideanSpace ℝ (Fin n) → ℝ) x
          = (u : EuclideanSpace ℝ (Fin n) → ℝ) x
            + (-ε) * (φ : EuclideanSpace ℝ (Fin n) → ℝ) x := by
        rw [hadd']
        simp only [Pi.add_apply]
        rw [hsm']
        simp only [Pi.smul_apply, smul_eq_mul]
      rw [hzm, hzx]
      have h0 : (0 : ℝ) ≤ max (-((u : EuclideanSpace ℝ (Fin n) → ℝ) x
          + (-ε) * (φ : EuclideanSpace ℝ (Fin n) → ℝ) x)) 0 := le_max_right _ _
      have hle : max (-((u : EuclideanSpace ℝ (Fin n) → ℝ) x
            + (-ε) * (φ : EuclideanSpace ℝ (Fin n) → ℝ) x)) 0
          ≤ ε * (φ : EuclideanSpace ℝ (Fin n) → ℝ) x := by
        refine max_le (by linarith) (mul_nonneg hε.le hφx)
      have hk0 : (0 : ℝ) ≤ max (a - (F : EuclideanSpace ℝ (Fin n) → ℝ) x) 0 :=
        le_max_right _ _
      have hkge : a - (F : EuclideanSpace ℝ (Fin n) → ℝ) x
          ≤ max (a - (F : EuclideanSpace ℝ (Fin n) → ℝ) x) 0 := le_max_left _ _
      nlinarith [h0, hle, hk0, hkge]
    -- the load integral splits along the competitor difference
    have hLHS : (∫ x, ((F : EuclideanSpace ℝ (Fin n) → ℝ) x - a)
          * ((((u + (-ε) • φ) + zm : Lp ℝ 2 (GaussMeasure n)) :
              EuclideanSpace ℝ (Fin n) → ℝ) x
            - (u : EuclideanSpace ℝ (Fin n) → ℝ) x) ∂(GaussMeasure n))
        = (∫ x, ((F : EuclideanSpace ℝ (Fin n) → ℝ) x - a)
            * (zm : EuclideanSpace ℝ (Fin n) → ℝ) x ∂(GaussMeasure n))
          + (-ε) * ∫ x, ((F : EuclideanSpace ℝ (Fin n) → ℝ) x - a)
              * (φ : EuclideanSpace ℝ (Fin n) → ℝ) x ∂(GaussMeasure n) := by
      rw [← integral_const_mul, ← integral_add hzmint (hintφ.const_mul (-ε))]
      refine integral_congr_ae ?_
      filter_upwards [hptw] with x hx
      rw [hx]; ring
    rw [hLHS, hBu] at hVI
    have hfin : ε * (EnergyBil u φ
          - ∫ x, ((F : EuclideanSpace ℝ (Fin n) → ℝ) x - a)
              * (φ : EuclideanSpace ℝ (Fin n) → ℝ) x ∂(GaussMeasure n))
        ≤ ε * ((ε / 4) * (Energy φ).toReal
          + ∫ x, max (a - (F : EuclideanSpace ℝ (Fin n) → ℝ) x) 0
              * (φ : EuclideanSpace ℝ (Fin n) → ℝ) x ∂(GaussMeasure n)) := by
      nlinarith [hVI, hstep2, hload]
    rw [ObstacleMultiplier]
    exact le_of_mul_le_mul_left hfin hε
  -- letting `ε ↓ 0`
  refine le_of_forall_pos_le_add fun δ hδ => ?_
  rcases eq_or_lt_of_le (show (0 : ℝ) ≤ (Energy φ).toReal from ENNReal.toReal_nonneg)
    with h0 | h0
  · have h := key 1 one_pos
    rw [← h0] at h
    linarith
  · have h := key (4 * δ / (Energy φ).toReal) (by positivity)
    rw [show 4 * δ / (Energy φ).toReal / 4 * (Energy φ).toReal = δ from by
      field_simp] at h
    linarith
