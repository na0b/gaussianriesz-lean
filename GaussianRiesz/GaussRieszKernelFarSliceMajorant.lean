module

public import GaussianRiesz.GaussRieszKernel
public import GaussianRiesz.GaussRieszKernelEndpointSliceBound
public import GaussianRiesz.GaussianUnitIntegralLinearFactorBound
public import GaussianRiesz.MehlerNumeratorCoordinateBallBound

@[expose] public section
open MeasureTheory
theorem GaussRieszKernelFarSliceMajorant {n : ℕ} (j : Fin n) :
    ∀ R ρ : ℝ, 0 < R → 0 < ρ → ∃ C : ℝ, 0 < C ∧
      ∀ x y : EuclideanSpace ℝ (Fin n), ‖x‖ ≤ R → ρ ≤ ‖x - y‖ →
        IntegrableOn (fun r : ℝ =>
            (y j - r * x j) / ((1 - r ^ 2) ^ ((n : ℝ) / 2 + 1) * Real.sqrt (-Real.log r))
              * Real.exp (-‖r • x - y‖ ^ 2 / (1 - r ^ 2))) (Set.Ioo (0 : ℝ) 1) volume
          ∧ |GaussRieszKernel j x y| ≤ C * Real.exp (-‖y‖ ^ 2) := by
  -- The whole estimate runs on the REFLECTED integrand: the identity
  -- `|rx-y|²/(1-r²) = (|y|²-|x|²) + |x-ry|²/(1-r²)` extracts the factor `e^{|x|²}e^{-|y|²}`
  -- that the majorant advertises, and leaves a kernel in which `x` and `y` have swapped
  -- roles.  On `(0,1/2]` the prefactor is bounded and the Gaussian decays in `r|y|`, which
  -- an `(e^{-((t-R)^+)^2} ≤ e^{R^2}e^{-t^2/4})` step turns into a genuine Gaussian in `r`
  -- whose integral carries the `1/|y|` that pairs with the `|y|` in the numerator; on
  -- `[1/2,1)` the pointwise constant bound is `GaussRieszKernelEndpointSliceBound`.  The
  -- two combine into one majorant `B₁ + B₂ e^{-(|y|²/4)r²}`, valid on all of `(0,1)`, which
  -- gives both the integrability and the `y`-independent bound on the integral.
  have hsplit : ∀ (x y : EuclideanSpace ℝ (Fin n)) (r : ℝ),
      ‖r • x - y‖ ^ 2 - (1 - r ^ 2) * (‖y‖ ^ 2 - ‖x‖ ^ 2) = ‖x - r • y‖ ^ 2 := by
    intro x y r
    rw [norm_sub_sq_real, norm_sub_sq_real, norm_smul, norm_smul,
      real_inner_smul_left, real_inner_smul_right]
    simp only [Real.norm_eq_abs, mul_pow, sq_abs]
    ring
  have hPpos : ∀ r : ℝ, 0 < r → r < 1 →
      0 < (1 - r ^ 2) ^ ((n : ℝ) / 2 + 1) * Real.sqrt (-Real.log r) := by
    intro r h0 h1
    have h2 : (0:ℝ) < 1 - r ^ 2 := by
      have := pow_lt_one₀ h0.le h1 (two_ne_zero); linarith
    have h3 : (0:ℝ) < -Real.log r := by have := Real.log_neg h0 h1; linarith
    have h4 : (0:ℝ) < (1 - r ^ 2) ^ ((n : ℝ) / 2 + 1) := Real.rpow_pos_of_pos h2 _
    have h5 : (0:ℝ) < Real.sqrt (-Real.log r) := Real.sqrt_pos.2 h3
    positivity
  intro R ρ hR hρ
  obtain ⟨R', -, hRR'⟩ : ∃ R' : ℝ, 1 ≤ R' ∧ R ≤ R' :=
    ⟨max R 1, le_max_right _ _, le_max_left _ _⟩
  obtain ⟨ρ', hρ'0, -, hρρ'⟩ : ∃ ρ' : ℝ, 0 < ρ' ∧ ρ' ≤ 1 ∧ ρ' ≤ ρ :=
    ⟨min ρ 1, lt_min hρ one_pos, min_le_right _ _, min_le_left _ _⟩
  have hR'0 : (0:ℝ) < R' := by linarith
  obtain ⟨C₂, hC₂0, hC₂bd⟩ := GaussRieszKernelEndpointSliceBound j R' ρ' hR'0 hρ'0
  have hnum := MehlerNumeratorCoordinateBallBound j R'
  obtain ⟨K, hK0, hK2⟩ : ∃ K : ℝ, 0 < K ∧ ∀ r : ℝ, 0 < r → r ≤ 1/2 →
      ((1 - r ^ 2) ^ ((n : ℝ) / 2 + 1) * Real.sqrt (-Real.log r))⁻¹ ≤ K := by
    have hlog2 : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
    have h1 : (0:ℝ) < ((3:ℝ)/4) ^ ((n : ℝ) / 2 + 1) := Real.rpow_pos_of_pos (by norm_num) _
    have h2 : (0:ℝ) < Real.sqrt (Real.log 2) := Real.sqrt_pos.2 hlog2
    refine ⟨(((3:ℝ)/4) ^ ((n : ℝ) / 2 + 1) * Real.sqrt (Real.log 2))⁻¹, by positivity, ?_⟩
    intro r h0 hh
    have hb1 : ((3:ℝ)/4) ≤ 1 - r ^ 2 := by nlinarith [sq_nonneg (r - 1/2)]
    have e1 : ((3:ℝ)/4) ^ ((n : ℝ) / 2 + 1) ≤ (1 - r ^ 2) ^ ((n : ℝ) / 2 + 1) :=
      Real.rpow_le_rpow (by norm_num) hb1 (by positivity)
    have e2 : Real.sqrt (Real.log 2) ≤ Real.sqrt (-Real.log r) := by
      refine Real.sqrt_le_sqrt ?_
      have e5 : Real.log r ≤ Real.log (1/2) := Real.log_le_log h0 (by linarith)
      rw [show Real.log (1/2) = -Real.log 2 by rw [one_div, Real.log_inv]] at e5
      linarith
    exact inv_anti₀ (by positivity) (mul_le_mul e1 e2 h2.le (le_trans h1.le e1))
  -- the elementary max-square bound
  have hmaxsq : ∀ t : ℝ, 0 ≤ t → t ^ 2 / 4 - R' ^ 2 ≤ (max (t - R') 0) ^ 2 := by
    intro t ht
    rcases le_or_gt t (2 * R') with h | h
    · have h1 : t ^ 2 / 4 - R' ^ 2 ≤ 0 := by nlinarith
      exact h1.trans (sq_nonneg _)
    · have h1 : t / 2 ≤ t - R' := by linarith
      have h2 : t / 2 ≤ max (t - R') 0 := le_max_of_le_left h1
      nlinarith [le_max_right (t - R') (0:ℝ)]
  -- STEP 2: the pointwise bound on (0, 1/2]
  have hstep2 : ∀ (x y : EuclideanSpace ℝ (Fin n)), ‖x‖ ≤ R' → ∀ r : ℝ, 0 < r → r ≤ 1/2 →
      |(y j - r * x j) / ((1 - r ^ 2) ^ ((n : ℝ) / 2 + 1) * Real.sqrt (-Real.log r)) * Real.exp (-‖x - r • y‖ ^ 2 / (1 - r ^ 2))|
        ≤ K * (‖y‖ + R') * Real.exp (R' ^ 2)
          * Real.exp (-(‖y‖ ^ 2 / 4) * r ^ 2) := by
    intro x y hx r h0 hh
    have h2 : r < 1 := by linarith
    have hP := hPpos r h0 h2
    have hr2 : (0:ℝ) < 1 - r ^ 2 := by
      have := pow_lt_one₀ h0.le h2 (two_ne_zero); linarith
    have hval : |(y j - r * x j) / ((1 - r ^ 2) ^ ((n : ℝ) / 2 + 1) * Real.sqrt (-Real.log r)) * Real.exp (-‖x - r • y‖ ^ 2 / (1 - r ^ 2))|
        = |y j - r * x j| * ((1 - r ^ 2) ^ ((n : ℝ) / 2 + 1) * Real.sqrt (-Real.log r))⁻¹ * Real.exp (-‖x - r • y‖ ^ 2 / (1 - r ^ 2)) := by
      rw [abs_mul, abs_div, abs_of_pos hP, abs_of_pos (Real.exp_pos _), div_eq_mul_inv]
    rw [hval]
    have hd : ‖y‖ * r - R' ≤ ‖x - r • y‖ := by
      have h5 : ‖r • y‖ - ‖x‖ ≤ ‖r • y - x‖ := norm_sub_norm_le _ _
      rw [norm_sub_rev, norm_smul, Real.norm_eq_abs, abs_of_pos h0] at h5
      have h6 : ‖y‖ * r = r * ‖y‖ := by ring
      linarith [hx, h5, h6.le]
    have hexp : Real.exp (-‖x - r • y‖ ^ 2 / (1 - r ^ 2))
        ≤ Real.exp (R' ^ 2) * Real.exp (-(‖y‖ ^ 2 / 4) * r ^ 2) := by
      rw [← Real.exp_add]
      refine Real.exp_le_exp.2 ?_
      have hdm : max (‖y‖ * r - R') 0 ≤ ‖x - r • y‖ := max_le hd (norm_nonneg _)
      have hsq : (max (‖y‖ * r - R') 0) ^ 2 ≤ ‖x - r • y‖ ^ 2 :=
        pow_le_pow_left₀ (le_max_right _ _) hdm 2
      have hlow : (‖y‖ * r) ^ 2 / 4 - R' ^ 2 ≤ ‖x - r • y‖ ^ 2 :=
        le_trans (hmaxsq (‖y‖ * r) (by positivity)) hsq
      have hstep : -‖x - r • y‖ ^ 2 / (1 - r ^ 2) ≤ -‖x - r • y‖ ^ 2 := by
        rw [div_le_iff₀ hr2]
        nlinarith [sq_nonneg ‖x - r • y‖]
      nlinarith [hlow, hstep]
    have hnum' := hnum x y hx r h0.le (by linarith)
    have hya : (0:ℝ) ≤ ‖y‖ + R' := by linarith [norm_nonneg y]
    calc |y j - r * x j| * ((1 - r ^ 2) ^ ((n : ℝ) / 2 + 1) * Real.sqrt (-Real.log r))⁻¹ * Real.exp (-‖x - r • y‖ ^ 2 / (1 - r ^ 2))
        ≤ ((‖y‖ + R') * K) * (Real.exp (R' ^ 2) * Real.exp (-(‖y‖ ^ 2 / 4) * r ^ 2)) := by
          refine mul_le_mul (mul_le_mul hnum' (hK2 r h0 hh) (inv_nonneg.2 hP.le) hya) hexp
            (Real.exp_pos _).le (mul_nonneg hya hK0.le)
      _ = K * (‖y‖ + R') * Real.exp (R' ^ 2) * Real.exp (-(‖y‖ ^ 2 / 4) * r ^ 2) := by ring
  -- STEP 0: the splitting of the exponent
  have hPhiPsi : ∀ (x y : EuclideanSpace ℝ (Fin n)), ∀ r ∈ Set.Ioo (0:ℝ) 1,
      (y j - r * x j) / ((1 - r ^ 2) ^ ((n : ℝ) / 2 + 1) * Real.sqrt (-Real.log r)) * Real.exp (-‖r • x - y‖ ^ 2 / (1 - r ^ 2))
        = Real.exp (‖x‖ ^ 2) * Real.exp (-‖y‖ ^ 2)
          * ((y j - r * x j) / ((1 - r ^ 2) ^ ((n : ℝ) / 2 + 1) * Real.sqrt (-Real.log r)) * Real.exp (-‖x - r • y‖ ^ 2 / (1 - r ^ 2))) := by
    intro x y r hr
    have h0 := hr.1
    have h2 := hr.2
    have hr2 : (0:ℝ) < 1 - r ^ 2 := by
      have := pow_lt_one₀ h0.le h2 (two_ne_zero); linarith
    have e0 := hsplit x y r
    have e2 : -‖r • x - y‖ ^ 2
        = (‖x‖ ^ 2 + -‖y‖ ^ 2) * (1 - r ^ 2) + -‖x - r • y‖ ^ 2 := by
      linear_combination -e0
    have e1 : -‖r • x - y‖ ^ 2 / (1 - r ^ 2)
        = (‖x‖ ^ 2 + -‖y‖ ^ 2) + -‖x - r • y‖ ^ 2 / (1 - r ^ 2) := by
      rw [e2, add_div, mul_div_assoc, div_self hr2.ne', mul_one]
    rw [e1, Real.exp_add, Real.exp_add]
    ring
  -- the assembly
  have hπ : (0:ℝ) < Real.pi ^ (-((n : ℝ) + 1) / 2) := Real.rpow_pos_of_pos Real.pi_pos _
  have hs2 : (0:ℝ) < Real.sqrt 2 := by positivity
  have hsp : (0:ℝ) ≤ Real.sqrt Real.pi := Real.sqrt_nonneg _
  have heR : (0:ℝ) < Real.exp (R' ^ 2) := Real.exp_pos _
  obtain ⟨C₀, hC₀0, hC₀val⟩ : ∃ C₀ : ℝ, 0 < C₀ ∧ C₀ = K * Real.exp (R' ^ 2) * 5 * R' + C₂
      + K * Real.exp (R' ^ 2) * (5 * R' + (5/2) * Real.sqrt Real.pi) := by
    refine ⟨_, ?_, rfl⟩
    have t1 : (0:ℝ) < K * Real.exp (R' ^ 2) * 5 * R' :=
      mul_pos (mul_pos (mul_pos hK0 heR) (by norm_num)) hR'0
    have t3 : (0:ℝ) < K * Real.exp (R' ^ 2) * (5 * R' + (5/2) * Real.sqrt Real.pi) :=
      mul_pos (mul_pos hK0 heR) (by linarith)
    linarith
  obtain ⟨cn, hcn0, hcnval⟩ : ∃ cn : ℝ, 0 < cn
      ∧ cn = Real.sqrt 2 * Real.pi ^ (-((n : ℝ) + 1) / 2) := ⟨_, mul_pos hs2 hπ, rfl⟩
  refine ⟨cn * Real.exp (R' ^ 2) * C₀, mul_pos (mul_pos hcn0 heR) hC₀0, ?_⟩
  intro x y hx hxy
  have hx' : ‖x‖ ≤ R' := hx.trans hRR'
  have hxy' : ρ' ≤ ‖x - y‖ := hρρ'.trans hxy
  have hyn : (0:ℝ) ≤ ‖y‖ := norm_nonneg y
  have hB₂0 : (0:ℝ) ≤ K * (‖y‖ + R') * Real.exp (R' ^ 2) :=
    (mul_pos (mul_pos hK0 (by linarith)) heR).le
  have ht1 : (0:ℝ) < K * Real.exp (R' ^ 2) * 5 * R' :=
    mul_pos (mul_pos (mul_pos hK0 heR) (by norm_num)) hR'0
  have hvol : volume (Set.Ioo (0:ℝ) 1) ≠ ⊤ := by
    rw [Real.volume_Ioo]; exact ENNReal.ofReal_ne_top
  -- the pointwise majorant on (0,1)
  have hbd : ∀ r ∈ Set.Ioo (0:ℝ) 1,
      |(y j - r * x j) / ((1 - r ^ 2) ^ ((n : ℝ) / 2 + 1) * Real.sqrt (-Real.log r)) * Real.exp (-‖x - r • y‖ ^ 2 / (1 - r ^ 2))|
        ≤ (K * Real.exp (R' ^ 2) * 5 * R' + C₂)
          + K * (‖y‖ + R') * Real.exp (R' ^ 2) * Real.exp (-(‖y‖ ^ 2 / 4) * r ^ 2) := by
    intro r hr
    rcases le_or_gt r (1/2) with h | h
    · have := hstep2 x y hx' r hr.1 h
      linarith
    · have := hC₂bd x y hx' hxy' r h.le hr.2
      have hpos : (0:ℝ) ≤ K * (‖y‖ + R') * Real.exp (R' ^ 2)
          * Real.exp (-(‖y‖ ^ 2 / 4) * r ^ 2) :=
        mul_nonneg hB₂0 (Real.exp_pos _).le
      linarith
  have hbdc : ∀ r ∈ Set.Ioo (0:ℝ) 1,
      |(y j - r * x j) / ((1 - r ^ 2) ^ ((n : ℝ) / 2 + 1) * Real.sqrt (-Real.log r)) * Real.exp (-‖x - r • y‖ ^ 2 / (1 - r ^ 2))|
        ≤ (K * Real.exp (R' ^ 2) * 5 * R' + C₂) + K * (‖y‖ + R') * Real.exp (R' ^ 2) := by
    intro r hr
    have h1 := hbd r hr
    have h2 : Real.exp (-(‖y‖ ^ 2 / 4) * r ^ 2) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      have : (0:ℝ) ≤ ‖y‖ ^ 2 / 4 * r ^ 2 := by positivity
      linarith
    nlinarith [hB₂0]
  have hmeasP : Measurable (fun r : ℝ =>
      (y j - r * x j) / ((1 - r ^ 2) ^ ((n : ℝ) / 2 + 1) * Real.sqrt (-Real.log r)) * Real.exp (-‖x - r • y‖ ^ 2 / (1 - r ^ 2))) := by fun_prop
  have hPint : IntegrableOn (fun r : ℝ =>
      (y j - r * x j) / ((1 - r ^ 2) ^ ((n : ℝ) / 2 + 1) * Real.sqrt (-Real.log r)) * Real.exp (-‖x - r • y‖ ^ 2 / (1 - r ^ 2))) (Set.Ioo (0:ℝ) 1) volume := by
    refine Integrable.mono' (integrableOn_const (C := (K * Real.exp (R' ^ 2) * 5 * R' + C₂)
        + K * (‖y‖ + R') * Real.exp (R' ^ 2)) hvol) hmeasP.aestronglyMeasurable ?_
    refine (ae_restrict_iff' measurableSet_Ioo).2 (Filter.Eventually.of_forall fun r hr => ?_)
    rw [Real.norm_eq_abs]
    exact hbdc r hr
  -- the integral of the majorant
  have hg1 : IntegrableOn (fun r : ℝ => K * (‖y‖ + R') * Real.exp (R' ^ 2)
      * Real.exp (-(‖y‖ ^ 2 / 4) * r ^ 2)) (Set.Ioo (0:ℝ) 1) volume := by
    refine Integrable.mono' (integrableOn_const
      (C := K * (‖y‖ + R') * Real.exp (R' ^ 2)) hvol) (by fun_prop) ?_
    refine (ae_restrict_iff' measurableSet_Ioo).2 (Filter.Eventually.of_forall fun r _ => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _),
      abs_of_nonneg hB₂0]
    have h2 : Real.exp (-(‖y‖ ^ 2 / 4) * r ^ 2) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      have : (0:ℝ) ≤ ‖y‖ ^ 2 / 4 * r ^ 2 := by positivity
      linarith
    nlinarith [hB₂0]
  have hgauss : K * (‖y‖ + R') * Real.exp (R' ^ 2)
      * ∫ r in Set.Ioo (0:ℝ) 1, Real.exp (-(‖y‖ ^ 2 / 4) * r ^ 2)
        ≤ K * Real.exp (R' ^ 2) * (5 * R' + (5/2) * Real.sqrt Real.pi) := by
    have h := GaussianUnitIntegralLinearFactorBound ‖y‖ R' (norm_nonneg y) hR'0.le
    calc K * (‖y‖ + R') * Real.exp (R' ^ 2)
            * ∫ r in Set.Ioo (0:ℝ) 1, Real.exp (-(‖y‖ ^ 2 / 4) * r ^ 2)
        = K * Real.exp (R' ^ 2)
            * ((‖y‖ + R') * ∫ r in Set.Ioo (0:ℝ) 1,
                Real.exp (-(‖y‖ ^ 2 / 4) * r ^ 2)) := by ring
      _ ≤ K * Real.exp (R' ^ 2) * (5 * R' + (5/2) * Real.sqrt Real.pi) :=
          mul_le_mul_of_nonneg_left h (mul_pos hK0 heR).le
  have hMval : ∫ r in Set.Ioo (0:ℝ) 1,
        ((K * Real.exp (R' ^ 2) * 5 * R' + C₂)
          + K * (‖y‖ + R') * Real.exp (R' ^ 2) * Real.exp (-(‖y‖ ^ 2 / 4) * r ^ 2))
      ≤ C₀ := by
    rw [hC₀val, integral_add (integrableOn_const (C := K * Real.exp (R' ^ 2) * 5 * R' + C₂) hvol) hg1,
      integral_const_mul, setIntegral_const,
      Real.volume_real_Ioo_of_le (by norm_num : (0:ℝ) ≤ 1)]
    simp only [sub_zero, smul_eq_mul, one_mul]
    linarith [hgauss]
  have habsbd : |∫ r in Set.Ioo (0:ℝ) 1,
        (y j - r * x j) / ((1 - r ^ 2) ^ ((n : ℝ) / 2 + 1) * Real.sqrt (-Real.log r)) * Real.exp (-‖x - r • y‖ ^ 2 / (1 - r ^ 2))|
      ≤ C₀ := by
    have h1 : |∫ r in Set.Ioo (0:ℝ) 1,
          (y j - r * x j) / ((1 - r ^ 2) ^ ((n : ℝ) / 2 + 1) * Real.sqrt (-Real.log r)) * Real.exp (-‖x - r • y‖ ^ 2 / (1 - r ^ 2))|
        ≤ ∫ r in Set.Ioo (0:ℝ) 1,
          |(y j - r * x j) / ((1 - r ^ 2) ^ ((n : ℝ) / 2 + 1) * Real.sqrt (-Real.log r)) * Real.exp (-‖x - r • y‖ ^ 2 / (1 - r ^ 2))| := by
      have h0 := norm_integral_le_integral_norm (μ := volume.restrict (Set.Ioo (0:ℝ) 1))
        (fun r : ℝ => (y j - r * x j) / ((1 - r ^ 2) ^ ((n : ℝ) / 2 + 1) * Real.sqrt (-Real.log r)) * Real.exp (-‖x - r • y‖ ^ 2 / (1 - r ^ 2)))
      simp only [Real.norm_eq_abs] at h0
      exact h0
    refine le_trans h1 (le_trans ?_ hMval)
    refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun r => abs_nonneg _)
      ((integrableOn_const (C := K * Real.exp (R' ^ 2) * 5 * R' + C₂) hvol).add hg1) ?_
    refine (ae_restrict_iff' measurableSet_Ioo).2 (Filter.Eventually.of_forall fun r hr => ?_)
    exact hbd r hr
  -- back to the original integrand
  have hcongr : ∀ r ∈ Set.Ioo (0:ℝ) 1,
      (y j - r * x j) / ((1 - r ^ 2) ^ ((n : ℝ) / 2 + 1) * Real.sqrt (-Real.log r)) * Real.exp (-‖r • x - y‖ ^ 2 / (1 - r ^ 2))
        = Real.exp (‖x‖ ^ 2) * Real.exp (-‖y‖ ^ 2)
          * ((y j - r * x j) / ((1 - r ^ 2) ^ ((n : ℝ) / 2 + 1) * Real.sqrt (-Real.log r)) * Real.exp (-‖x - r • y‖ ^ 2 / (1 - r ^ 2))) := hPhiPsi x y
  refine ⟨?_, ?_⟩
  · refine IntegrableOn.congr_fun ((hPint.const_mul
      (Real.exp (‖x‖ ^ 2) * Real.exp (-‖y‖ ^ 2)))) (fun r hr => (hcongr r hr).symm)
      measurableSet_Ioo
  · have hval : ∫ r in Set.Ioo (0:ℝ) 1,
          (y j - r * x j) / ((1 - r ^ 2) ^ ((n : ℝ) / 2 + 1) * Real.sqrt (-Real.log r)) * Real.exp (-‖r • x - y‖ ^ 2 / (1 - r ^ 2))
        = Real.exp (‖x‖ ^ 2) * Real.exp (-‖y‖ ^ 2)
          * ∫ r in Set.Ioo (0:ℝ) 1,
            (y j - r * x j) / ((1 - r ^ 2) ^ ((n : ℝ) / 2 + 1) * Real.sqrt (-Real.log r)) * Real.exp (-‖x - r • y‖ ^ 2 / (1 - r ^ 2)) := by
      rw [setIntegral_congr_fun measurableSet_Ioo hcongr, integral_const_mul]
    rw [GaussRieszKernel, ← hcnval, hval]
    have hexx : Real.exp (‖x‖ ^ 2) ≤ Real.exp (R' ^ 2) :=
      Real.exp_le_exp.2 (pow_le_pow_left₀ (norm_nonneg x) hx' 2)
    rw [abs_mul, abs_of_pos hcn0, abs_mul, abs_mul,
      abs_of_pos (Real.exp_pos (‖x‖ ^ 2)), abs_of_pos (Real.exp_pos (-‖y‖ ^ 2))]
    have hfin : Real.exp (‖x‖ ^ 2) * |∫ r in Set.Ioo (0:ℝ) 1, (y j - r * x j) / ((1 - r ^ 2) ^ ((n : ℝ) / 2 + 1) * Real.sqrt (-Real.log r)) * Real.exp (-‖x - r • y‖ ^ 2 / (1 - r ^ 2))| ≤ Real.exp (R' ^ 2) * C₀ :=
      mul_le_mul hexx habsbd (abs_nonneg _) heR.le
    calc cn * (Real.exp (‖x‖ ^ 2) * Real.exp (-‖y‖ ^ 2) * |∫ r in Set.Ioo (0:ℝ) 1, (y j - r * x j) / ((1 - r ^ 2) ^ ((n : ℝ) / 2 + 1) * Real.sqrt (-Real.log r)) * Real.exp (-‖x - r • y‖ ^ 2 / (1 - r ^ 2))|)
        = (cn * Real.exp (-‖y‖ ^ 2)) * (Real.exp (‖x‖ ^ 2) * |∫ r in Set.Ioo (0:ℝ) 1, (y j - r * x j) / ((1 - r ^ 2) ^ ((n : ℝ) / 2 + 1) * Real.sqrt (-Real.log r)) * Real.exp (-‖x - r • y‖ ^ 2 / (1 - r ^ 2))|) := by ring
      _ ≤ (cn * Real.exp (-‖y‖ ^ 2)) * (Real.exp (R' ^ 2) * C₀) :=
          mul_le_mul_of_nonneg_left hfin (mul_nonneg hcn0.le (Real.exp_pos _).le)
      _ = cn * Real.exp (R' ^ 2) * C₀ * Real.exp (-‖y‖ ^ 2) := by ring
