import GaussianRiesz.GaussRieszKernelNearSliceBounds
import GaussianRiesz.GaussRieszKernelNearReflectedSliceMajorants
import GaussianRiesz.TauPowerIntegralBounds
import GaussianRiesz.OneSubReflectionIntegralTransfer
open MeasureTheory Filter Topology
theorem GaussRieszKernelNearSliceL1Bound {n : ℕ} (j : Fin n) (M : ℝ) (hM : 3 ≤ M) :
      ∃ A : ℝ, 0 < A ∧ ∀ x y : EuclideanSpace ℝ (Fin n), ‖x‖ ≤ M → ‖y‖ ≤ M →
          0 < ‖x - y‖ → ‖x - y‖ ≤ 2 →
        IntegrableOn (fun r : ℝ =>
              (y j - r * x j) / ((1 - r ^ 2) ^ ((n : ℝ) / 2 + 1) * Real.sqrt (-Real.log r))
                * Real.exp (-‖r • x - y‖ ^ 2 / (1 - r ^ 2))) (Set.Ioo (0:ℝ) 1) volume
          ∧ ∫ r in Set.Ioo (0:ℝ) 1,
                |(y j - r * x j) / ((1 - r ^ 2) ^ ((n : ℝ) / 2 + 1) * Real.sqrt (-Real.log r))
                  * Real.exp (-‖r • x - y‖ ^ 2 / (1 - r ^ 2))|
              ≤ A * ‖x - y‖ ^ (-(n:ℝ))      := by
  classical
  have hn : 0 < n := Fin.pos j
  have hnR : (0:ℝ) < (n:ℝ) := by exact_mod_cast hn
  have hn1 : (1:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn
  obtain ⟨hrefl, hreflint⟩ := OneSubReflectionIntegralTransfer
  -- the `d`-power comparison on `(0,2]`
  have hdpow : ∀ β γ : ℝ, 0 ≤ β + γ → ∀ d : ℝ, 0 < d → d ≤ 2 →
      d ^ β ≤ 2 ^ (β + γ) * d ^ (-γ) := by
    intro β γ hbg d hd0 hd2
    have h1 : d ^ β = d ^ (β + γ) * d ^ (-γ) := by
      rw [← Real.rpow_add hd0]; ring_nf
    have h2 : d ^ (β + γ) ≤ 2 ^ (β + γ) := Real.rpow_le_rpow hd0.le hd2 hbg
    rw [h1]
    exact mul_le_mul_of_nonneg_right h2 (Real.rpow_pos_of_pos hd0 _).le
  obtain ⟨K1, hK1pos, hK1⟩ := TauPowerIntegralBounds.1 ((n:ℝ)/2 + 3/2) (by linarith)
  have h5 := TauPowerIntegralBounds.2
  refine ⟨Real.exp (M ^ 2) * (3 / 2 * K1 * 8 ^ (((n:ℝ) + 1) / 2)
      + 2 ^ (((n:ℝ) + 1) / 2) * (2 * M) ^ (((n:ℝ) + 1) / 2) * (2 / ((n:ℝ) + 1))
      + M * 2 ^ ((n:ℝ) / 2) * (2 * M) ^ ((n:ℝ) / 2) * (2 / (n:ℝ))), by positivity, ?_⟩
  intro x y hxM hyM hd0 hd2
  -- abbreviations used below: a = n/2+3/2, q = (n+2)/2, tau' = d/(2M), b = d^2/8
  have hτ'0 : (0:ℝ) < ‖x - y‖ / (2 * M) := by positivity
  have hτ'3 : ‖x - y‖ / (2 * M) ≤ 1 / 3 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
  have hτ'1 : ‖x - y‖ / (2 * M) ≤ 1 := by linarith
  have hb0 : (0:ℝ) < ‖x - y‖ ^ 2 / 8 := by positivity
  have ha1 : (1:ℝ) < (n:ℝ) / 2 + 3 / 2 := by linarith
  have hq1 : (1:ℝ) < ((n:ℝ) + 2) / 2 := by linarith
  -- continuity of the reflected integrand
  have hcontt : ContinuousOn (fun τ : ℝ =>
      (y j - (1 - τ) * x j)
          / ((1 - (1 - τ) ^ 2) ^ ((n : ℝ) / 2 + 1) * Real.sqrt (-Real.log (1 - τ)))
        * Real.exp (-‖(1 - τ) • x - y‖ ^ 2 / (1 - (1 - τ) ^ 2))) (Set.Ioo (0:ℝ) 1) := by
    intro τ hτ
    obtain ⟨hτ0, hτ1⟩ := hτ
    refine ContinuousAt.continuousWithinAt ?_
    have hr0 : (0:ℝ) < 1 - τ := by linarith
    have hr1 : 1 - τ < 1 := by linarith
    have h1 : (1 - (1 - τ) ^ 2) ≠ 0 := by nlinarith
    have h2 : (1 - τ) ≠ 0 := ne_of_gt hr0
    have hlogr : 0 < -Real.log (1 - τ) := by
      have := Real.log_neg hr0 hr1; linarith
    have h3 : Real.sqrt (-Real.log (1 - τ)) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hlogr)
    have h4 : (1 - (1 - τ) ^ 2) ^ ((n : ℝ) / 2 + 1) ≠ 0 := by
      have : (0:ℝ) < 1 - (1 - τ) ^ 2 := by nlinarith
      positivity
    fun_prop (disch := first | assumption | positivity | simp_all)
  -- the two reflected pointwise majorants, near and far
  obtain ⟨hnearpt, hfarpt⟩ :=
    GaussRieszKernelNearReflectedSliceMajorants j M hM x y hxM hyM hd2
  -- rpow utilities, specialised to `d = ‖x - y‖`
  have hmul1 : ∀ β : ℝ, ‖x - y‖ * ‖x - y‖ ^ β = ‖x - y‖ ^ (β + 1) := by
    intro β
    rw [mul_comm, ← Real.rpow_add_one (ne_of_gt hd0)]
  have hdivrpow : ∀ u s : ℝ, 0 < u →
      (‖x - y‖ / u) ^ (-s) = ‖x - y‖ ^ (-s) * u ^ s := by
    intro u s hu
    rw [Real.div_rpow (norm_nonneg _) hu.le, Real.rpow_neg hu.le s, div_eq_mul_inv, inv_inv]
  have hsqrpow : ∀ s : ℝ, (‖x - y‖ ^ 2 / 8) ^ (-s) = ‖x - y‖ ^ (-(2 * s)) * 8 ^ s := by
    intro s
    rw [Real.div_rpow (by positivity) (by norm_num),
      Real.rpow_neg (by norm_num : (0:ℝ) ≤ 8) s, div_eq_mul_inv, inv_inv]
    congr 1
    rw [← Real.rpow_natCast ‖x - y‖ 2, ← Real.rpow_mul (norm_nonneg _)]
    push_cast
    ring_nf
  -- the three dominating integrals
  obtain ⟨hKint, hKbd⟩ := hK1 (‖x - y‖ ^ 2 / 8) hb0
  obtain ⟨h5aint, h5abd⟩ := h5 ((n:ℝ)/2 + 3/2) (‖x - y‖ / (2 * M)) ha1 hτ'0 hτ'1
  obtain ⟨h5qint, h5qbd⟩ := h5 (((n:ℝ) + 2)/2) (‖x - y‖ / (2 * M)) hq1 hτ'0 hτ'1
  have hsubIoi : Set.Ioc (0:ℝ) (‖x - y‖ / (2 * M)) ⊆ Set.Ioi (0:ℝ) := fun t ht => ht.1
  have hsub1 : Set.Ioc (0:ℝ) (‖x - y‖ / (2 * M)) ⊆ Set.Ioo (0:ℝ) 1 :=
    fun t ht => ⟨ht.1, by linarith [ht.2]⟩
  have hsub2 : Set.Ioo (‖x - y‖ / (2 * M)) 1 ⊆ Set.Ioo (0:ℝ) 1 :=
    fun t ht => ⟨lt_trans hτ'0 ht.1, ht.2⟩
  -- integrability of the reflected integrand on the two pieces
  have hintn : IntegrableOn (fun τ : ℝ =>
      (y j - (1 - τ) * x j)
          / ((1 - (1 - τ) ^ 2) ^ ((n : ℝ) / 2 + 1) * Real.sqrt (-Real.log (1 - τ)))
        * Real.exp (-‖(1 - τ) • x - y‖ ^ 2 / (1 - (1 - τ) ^ 2)))
      (Set.Ioc (0:ℝ) (‖x - y‖ / (2 * M))) volume := by
    refine Integrable.mono' ((hKint.mono_set hsubIoi).const_mul
        (Real.exp (M ^ 2) * (3 / 2 * ‖x - y‖)))
      ((hcontt.mono hsub1).aestronglyMeasurable measurableSet_Ioc) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with τ hτ
    rw [Real.norm_eq_abs]
    exact hnearpt τ hτ.1 hτ.2
  have hintf : IntegrableOn (fun τ : ℝ =>
      (y j - (1 - τ) * x j)
          / ((1 - (1 - τ) ^ 2) ^ ((n : ℝ) / 2 + 1) * Real.sqrt (-Real.log (1 - τ)))
        * Real.exp (-‖(1 - τ) • x - y‖ ^ 2 / (1 - (1 - τ) ^ 2)))
      (Set.Ioo (‖x - y‖ / (2 * M)) 1) volume := by
    refine Integrable.mono' ((h5aint.const_mul (Real.exp (M ^ 2) * ‖x - y‖)).add
        (h5qint.const_mul (Real.exp (M ^ 2) * M)))
      ((hcontt.mono hsub2).aestronglyMeasurable measurableSet_Ioo) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with τ hτ
    rw [Real.norm_eq_abs]
    exact hfarpt τ (lt_trans hτ'0 hτ.1) hτ.2
  have hunion : Set.Ioo (0:ℝ) 1
      = Set.Ioc (0:ℝ) (‖x - y‖ / (2 * M)) ∪ Set.Ioo (‖x - y‖ / (2 * M)) 1 := by
    ext t
    simp only [Set.mem_Ioo, Set.mem_union, Set.mem_Ioc]
    constructor
    · intro ⟨h1, h2⟩
      rcases le_or_gt t (‖x - y‖ / (2 * M)) with h | h
      · exact Or.inl ⟨h1, h⟩
      · exact Or.inr ⟨h, h2⟩
    · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
      · exact ⟨h1, by linarith⟩
      · exact ⟨lt_trans hτ'0 h1, h2⟩
  have hdisj : Disjoint (Set.Ioc (0:ℝ) (‖x - y‖ / (2 * M)))
      (Set.Ioo (‖x - y‖ / (2 * M)) 1) := by
    rw [Set.disjoint_left]
    intro t ht hb
    exact absurd hb.1 (not_lt.2 ht.2)
  have hintt : IntegrableOn (fun τ : ℝ =>
      (y j - (1 - τ) * x j)
          / ((1 - (1 - τ) ^ 2) ^ ((n : ℝ) / 2 + 1) * Real.sqrt (-Real.log (1 - τ)))
        * Real.exp (-‖(1 - τ) • x - y‖ ^ 2 / (1 - (1 - τ) ^ 2)))
      (Set.Ioo (0:ℝ) 1) volume := by
    rw [hunion]; exact hintn.union hintf
  refine ⟨?_, ?_⟩
  · -- clause (1)(a), transported back through the reflection
    have h := hreflint _ 1 (by simpa using hintt)
    simpa [sub_sub_cancel] using h
  · -- the integral bound
    have heq : ∫ r in Set.Ioo (0:ℝ) 1,
          |(y j - r * x j) / ((1 - r ^ 2) ^ ((n : ℝ) / 2 + 1) * Real.sqrt (-Real.log r))
            * Real.exp (-‖r • x - y‖ ^ 2 / (1 - r ^ 2))|
        = ∫ τ in Set.Ioo (0:ℝ) 1,
          |(y j - (1 - τ) * x j)
              / ((1 - (1 - τ) ^ 2) ^ ((n : ℝ) / 2 + 1) * Real.sqrt (-Real.log (1 - τ)))
            * Real.exp (-‖(1 - τ) • x - y‖ ^ 2 / (1 - (1 - τ) ^ 2))| := by
      have h := hrefl (fun t : ℝ =>
        |(y j - t * x j) / ((1 - t ^ 2) ^ ((n : ℝ) / 2 + 1) * Real.sqrt (-Real.log t))
          * Real.exp (-‖t • x - y‖ ^ 2 / (1 - t ^ 2))|) 1
      simpa using h.symm
    rw [heq, hunion, setIntegral_union hdisj measurableSet_Ioo hintn.abs hintf.abs]
    -- the two `d`-power comparisons
    have he1 : (1:ℝ) - ((n:ℝ)/2 + 3/2) = -(((n:ℝ) + 1)/2) := by ring
    have he2 : (1:ℝ) - (((n:ℝ) + 2)/2) = -((n:ℝ)/2) := by ring
    have hd1 : ‖x - y‖ * ‖x - y‖ ^ (-(((n:ℝ) + 1)/2))
        ≤ 2 ^ (((n:ℝ) + 1)/2) * ‖x - y‖ ^ (-(n:ℝ)) := by
      rw [hmul1]
      have h := hdpow (-(((n:ℝ) + 1)/2) + 1) (n:ℝ) (by linarith) ‖x - y‖ hd0 hd2
      have he : -(((n:ℝ) + 1)/2) + 1 + (n:ℝ) = ((n:ℝ) + 1)/2 := by ring
      rwa [he] at h
    have hd2' : ‖x - y‖ ^ (-((n:ℝ)/2)) ≤ 2 ^ ((n:ℝ)/2) * ‖x - y‖ ^ (-(n:ℝ)) := by
      have h := hdpow (-((n:ℝ)/2)) (n:ℝ) (by linarith) ‖x - y‖ hd0 hd2
      have he : -((n:ℝ)/2) + (n:ℝ) = (n:ℝ)/2 := by ring
      rwa [he] at h
    -- the near piece
    have hnn : ∀ᵐ τ ∂(volume.restrict (Set.Ioi (0:ℝ))),
        0 ≤ Real.exp (M ^ 2) * (3 / 2 * ‖x - y‖)
          * (τ ^ (-((n:ℝ)/2 + 3/2)) * Real.exp (-(‖x - y‖ ^ 2 / 8) / τ)) := by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with τ hτ
      have hτ0 : (0:ℝ) < τ := hτ
      positivity
    have hnearbd : ∫ τ in Set.Ioc (0:ℝ) (‖x - y‖ / (2 * M)),
          |(y j - (1 - τ) * x j)
              / ((1 - (1 - τ) ^ 2) ^ ((n : ℝ) / 2 + 1) * Real.sqrt (-Real.log (1 - τ)))
            * Real.exp (-‖(1 - τ) • x - y‖ ^ 2 / (1 - (1 - τ) ^ 2))|
        ≤ Real.exp (M ^ 2) * (3 / 2 * K1 * 8 ^ (((n:ℝ) + 1)/2)) * ‖x - y‖ ^ (-(n:ℝ)) := by
      calc ∫ τ in Set.Ioc (0:ℝ) (‖x - y‖ / (2 * M)),
              |(y j - (1 - τ) * x j)
                  / ((1 - (1 - τ) ^ 2) ^ ((n : ℝ) / 2 + 1) * Real.sqrt (-Real.log (1 - τ)))
                * Real.exp (-‖(1 - τ) • x - y‖ ^ 2 / (1 - (1 - τ) ^ 2))|
          ≤ ∫ τ in Set.Ioc (0:ℝ) (‖x - y‖ / (2 * M)), Real.exp (M ^ 2) * (3 / 2 * ‖x - y‖)
              * (τ ^ (-((n:ℝ)/2 + 3/2)) * Real.exp (-(‖x - y‖ ^ 2 / 8) / τ)) :=
            setIntegral_mono_on hintn.abs ((hKint.mono_set hsubIoi).const_mul _)
              measurableSet_Ioc (fun τ hτ => hnearpt τ hτ.1 hτ.2)
        _ ≤ ∫ τ in Set.Ioi (0:ℝ), Real.exp (M ^ 2) * (3 / 2 * ‖x - y‖)
              * (τ ^ (-((n:ℝ)/2 + 3/2)) * Real.exp (-(‖x - y‖ ^ 2 / 8) / τ)) :=
            setIntegral_mono_set (hKint.const_mul _) hnn hsubIoi.eventuallyLE
        _ = Real.exp (M ^ 2) * (3 / 2 * ‖x - y‖) * (∫ τ in Set.Ioi (0:ℝ),
              (τ ^ (-((n:ℝ)/2 + 3/2)) * Real.exp (-(‖x - y‖ ^ 2 / 8) / τ))) :=
            integral_const_mul _ _
        _ ≤ Real.exp (M ^ 2) * (3 / 2 * ‖x - y‖)
              * (K1 * (‖x - y‖ ^ 2 / 8) ^ (1 - ((n:ℝ)/2 + 3/2))) :=
            mul_le_mul_of_nonneg_left hKbd (by positivity)
        _ = Real.exp (M ^ 2) * (3 / 2 * K1 * 8 ^ (((n:ℝ) + 1)/2)) * ‖x - y‖ ^ (-(n:ℝ)) := by
            rw [he1, hsqrpow, show (2:ℝ) * (((n:ℝ) + 1)/2) = (n:ℝ) + 1 by ring]
            have h3 : ‖x - y‖ * ‖x - y‖ ^ (-((n:ℝ) + 1)) = ‖x - y‖ ^ (-(n:ℝ)) := by
              rw [hmul1]; congr 1; ring
            calc Real.exp (M ^ 2) * (3 / 2 * ‖x - y‖)
                  * (K1 * (‖x - y‖ ^ (-((n:ℝ) + 1)) * 8 ^ (((n:ℝ) + 1)/2)))
                = Real.exp (M ^ 2) * (3 / 2 * K1 * 8 ^ (((n:ℝ) + 1)/2))
                    * (‖x - y‖ * ‖x - y‖ ^ (-((n:ℝ) + 1))) := by ring
              _ = Real.exp (M ^ 2) * (3 / 2 * K1 * 8 ^ (((n:ℝ) + 1)/2))
                    * ‖x - y‖ ^ (-(n:ℝ)) := by rw [h3]
    -- the far piece
    have hfarbd : ∫ τ in Set.Ioo (‖x - y‖ / (2 * M)) 1,
          |(y j - (1 - τ) * x j)
              / ((1 - (1 - τ) ^ 2) ^ ((n : ℝ) / 2 + 1) * Real.sqrt (-Real.log (1 - τ)))
            * Real.exp (-‖(1 - τ) • x - y‖ ^ 2 / (1 - (1 - τ) ^ 2))|
        ≤ Real.exp (M ^ 2)
              * (2 ^ (((n:ℝ) + 1)/2) * (2 * M) ^ (((n:ℝ) + 1)/2) * (2 / ((n:ℝ) + 1)))
              * ‖x - y‖ ^ (-(n:ℝ))
            + Real.exp (M ^ 2) * (M * 2 ^ ((n:ℝ)/2) * (2 * M) ^ ((n:ℝ)/2) * (2 / (n:ℝ)))
              * ‖x - y‖ ^ (-(n:ℝ)) := by
      calc ∫ τ in Set.Ioo (‖x - y‖ / (2 * M)) 1,
              |(y j - (1 - τ) * x j)
                  / ((1 - (1 - τ) ^ 2) ^ ((n : ℝ) / 2 + 1) * Real.sqrt (-Real.log (1 - τ)))
                * Real.exp (-‖(1 - τ) • x - y‖ ^ 2 / (1 - (1 - τ) ^ 2))|
          ≤ ∫ τ in Set.Ioo (‖x - y‖ / (2 * M)) 1,
              (Real.exp (M ^ 2) * ‖x - y‖ * τ ^ (-((n:ℝ)/2 + 3/2))
                + Real.exp (M ^ 2) * M * τ ^ (-(((n:ℝ) + 2)/2))) :=
            setIntegral_mono_on hintf.abs ((h5aint.const_mul _).add (h5qint.const_mul _))
              measurableSet_Ioo (fun τ hτ => hfarpt τ (lt_trans hτ'0 hτ.1) hτ.2)
        _ = Real.exp (M ^ 2) * ‖x - y‖
                * (∫ τ in Set.Ioo (‖x - y‖ / (2 * M)) 1, τ ^ (-((n:ℝ)/2 + 3/2)))
              + Real.exp (M ^ 2) * M
                * (∫ τ in Set.Ioo (‖x - y‖ / (2 * M)) 1, τ ^ (-(((n:ℝ) + 2)/2))) := by
            rw [integral_add (h5aint.const_mul _) (h5qint.const_mul _),
              integral_const_mul, integral_const_mul]
        _ ≤ Real.exp (M ^ 2) * ‖x - y‖
                * ((‖x - y‖ / (2 * M)) ^ (1 - ((n:ℝ)/2 + 3/2)) / (((n:ℝ)/2 + 3/2) - 1))
              + Real.exp (M ^ 2) * M
                * ((‖x - y‖ / (2 * M)) ^ (1 - (((n:ℝ) + 2)/2)) / ((((n:ℝ) + 2)/2) - 1)) :=
            add_le_add (mul_le_mul_of_nonneg_left h5abd (by positivity))
              (mul_le_mul_of_nonneg_left h5qbd (by positivity))
        _ ≤ _ := by
            rw [he1, he2, hdivrpow (2 * M) (((n:ℝ) + 1)/2) (by positivity),
              hdivrpow (2 * M) ((n:ℝ)/2) (by positivity)]
            have hA : Real.exp (M ^ 2) * ‖x - y‖
                  * (‖x - y‖ ^ (-(((n:ℝ) + 1)/2)) * (2 * M) ^ (((n:ℝ) + 1)/2)
                      / (((n:ℝ)/2 + 3/2) - 1))
                ≤ Real.exp (M ^ 2)
                    * (2 ^ (((n:ℝ) + 1)/2) * (2 * M) ^ (((n:ℝ) + 1)/2) * (2 / ((n:ℝ) + 1)))
                    * ‖x - y‖ ^ (-(n:ℝ)) := by
              have hcoef : (0:ℝ) ≤ Real.exp (M ^ 2) * ((2 * M) ^ (((n:ℝ) + 1)/2)
                  / (((n:ℝ)/2 + 3/2) - 1)) := by positivity
              have := mul_le_mul_of_nonneg_left hd1 hcoef
              calc Real.exp (M ^ 2) * ‖x - y‖
                    * (‖x - y‖ ^ (-(((n:ℝ) + 1)/2)) * (2 * M) ^ (((n:ℝ) + 1)/2)
                        / (((n:ℝ)/2 + 3/2) - 1))
                  = Real.exp (M ^ 2) * ((2 * M) ^ (((n:ℝ) + 1)/2) / (((n:ℝ)/2 + 3/2) - 1))
                      * (‖x - y‖ * ‖x - y‖ ^ (-(((n:ℝ) + 1)/2))) := by ring
                _ ≤ Real.exp (M ^ 2) * ((2 * M) ^ (((n:ℝ) + 1)/2) / (((n:ℝ)/2 + 3/2) - 1))
                      * (2 ^ (((n:ℝ) + 1)/2) * ‖x - y‖ ^ (-(n:ℝ))) := by
                    rw [← mul_assoc] at this ⊢; linarith [this]
                _ = Real.exp (M ^ 2)
                      * (2 ^ (((n:ℝ) + 1)/2) * (2 * M) ^ (((n:ℝ) + 1)/2) * (2 / ((n:ℝ) + 1)))
                      * ‖x - y‖ ^ (-(n:ℝ)) := by
                    rw [show ((n:ℝ)/2 + 3/2) - 1 = ((n:ℝ) + 1)/2 by ring]
                    field_simp
            have hB : Real.exp (M ^ 2) * M
                  * (‖x - y‖ ^ (-((n:ℝ)/2)) * (2 * M) ^ ((n:ℝ)/2) / ((((n:ℝ) + 2)/2) - 1))
                ≤ Real.exp (M ^ 2) * (M * 2 ^ ((n:ℝ)/2) * (2 * M) ^ ((n:ℝ)/2) * (2 / (n:ℝ)))
                    * ‖x - y‖ ^ (-(n:ℝ)) := by
              have hcoef : (0:ℝ) ≤ Real.exp (M ^ 2) * M * ((2 * M) ^ ((n:ℝ)/2)
                  / ((((n:ℝ) + 2)/2) - 1)) := by positivity
              have := mul_le_mul_of_nonneg_left hd2' hcoef
              calc Real.exp (M ^ 2) * M
                    * (‖x - y‖ ^ (-((n:ℝ)/2)) * (2 * M) ^ ((n:ℝ)/2) / ((((n:ℝ) + 2)/2) - 1))
                  = Real.exp (M ^ 2) * M * ((2 * M) ^ ((n:ℝ)/2) / ((((n:ℝ) + 2)/2) - 1))
                      * ‖x - y‖ ^ (-((n:ℝ)/2)) := by ring
                _ ≤ Real.exp (M ^ 2) * M * ((2 * M) ^ ((n:ℝ)/2) / ((((n:ℝ) + 2)/2) - 1))
                      * (2 ^ ((n:ℝ)/2) * ‖x - y‖ ^ (-(n:ℝ))) := by linarith [this]
                _ = Real.exp (M ^ 2)
                      * (M * 2 ^ ((n:ℝ)/2) * (2 * M) ^ ((n:ℝ)/2) * (2 / (n:ℝ)))
                      * ‖x - y‖ ^ (-(n:ℝ)) := by
                    rw [show (((n:ℝ) + 2)/2) - 1 = (n:ℝ)/2 by ring]
                    field_simp
            linarith [hA, hB]
    have hdist : Real.exp (M ^ 2) * (3 / 2 * K1 * 8 ^ (((n:ℝ) + 1) / 2)
          + 2 ^ (((n:ℝ) + 1) / 2) * (2 * M) ^ (((n:ℝ) + 1) / 2) * (2 / ((n:ℝ) + 1))
          + M * 2 ^ ((n:ℝ) / 2) * (2 * M) ^ ((n:ℝ) / 2) * (2 / (n:ℝ))) * ‖x - y‖ ^ (-(n:ℝ))
        = Real.exp (M ^ 2) * (3 / 2 * K1 * 8 ^ (((n:ℝ) + 1)/2)) * ‖x - y‖ ^ (-(n:ℝ))
          + (Real.exp (M ^ 2)
              * (2 ^ (((n:ℝ) + 1)/2) * (2 * M) ^ (((n:ℝ) + 1)/2) * (2 / ((n:ℝ) + 1)))
              * ‖x - y‖ ^ (-(n:ℝ))
            + Real.exp (M ^ 2) * (M * 2 ^ ((n:ℝ)/2) * (2 * M) ^ ((n:ℝ)/2) * (2 / (n:ℝ)))
              * ‖x - y‖ ^ (-(n:ℝ))) := by ring
    rw [hdist]
    exact add_le_add hnearbd hfarbd
