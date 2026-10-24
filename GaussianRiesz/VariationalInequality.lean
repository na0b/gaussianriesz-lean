import GaussianRiesz.ObstacleFunctional
import GaussianRiesz.ObstacleCone
import GaussianRiesz.EnergyBil
import GaussianRiesz.EnergyFormBilinear
open MeasureTheory
theorem VariationalInequality {n : ℕ} (F : Lp ℝ 2 (GaussMeasure n)) (a : ℝ)
    (u : Lp ℝ 2 (GaussMeasure n)) (hu : u ∈ ObstacleCone n)
    (hmin : ∀ w ∈ ObstacleCone n, ObstacleFunctional F a u ≤ ObstacleFunctional F a w)
    (v : Lp ℝ 2 (GaussMeasure n)) (hv : v ∈ ObstacleCone n) :
    ∫ x, ((F : EuclideanSpace ℝ (Fin n) → ℝ) x - a)
        * ((v : EuclideanSpace ℝ (Fin n) → ℝ) x - (u : EuclideanSpace ℝ (Fin n) → ℝ) x)
        ∂(GaussMeasure n)
      ≤ EnergyBil u (v - u) := by
  classical
  obtain ⟨hmix, hdiag, hbil, hsub⟩ := EnergyFormBilinear (n := n)
  obtain ⟨huV, hu0⟩ := hu
  obtain ⟨hvV, hv0⟩ := hv
  -- the admissible direction `h = v - u`
  set h : Lp ℝ 2 (GaussMeasure n) := v - u with hhdef
  have hnegu : Energy ((-1 : ℝ) • u) ≠ ⊤ := (hsub u u (-1) huV huV).2
  have hsubadd : h = v + (-1 : ℝ) • u := by
    rw [hhdef, neg_one_smul, sub_eq_add_neg]
  have hhV : Energy h ≠ ⊤ := by
    rw [hsubadd]; exact (hsub v ((-1 : ℝ) • u) 0 hvV hnegu).1
  have hhc : (h : EuclideanSpace ℝ (Fin n) → ℝ) =ᵐ[GaussMeasure n]
      fun x => (v : EuclideanSpace ℝ (Fin n) → ℝ) x
        - (u : EuclideanSpace ℝ (Fin n) → ℝ) x := by
    rw [hhdef]; exact Lp.coeFn_sub v u
  -- the quadratic expansion of the energy along `h`
  have hexp : ∀ θ : ℝ, (Energy (u + θ • h)).toReal
      = (Energy u).toReal + 2 * θ * EnergyBil u h + θ ^ 2 * (Energy h).toReal := by
    intro θ
    have hthV : Energy (θ • h) ≠ ⊤ := (hsub h h θ hhV hhV).2
    have hwV : Energy (u + θ • h) ≠ ⊤ := (hsub u (θ • h) 0 huV hthV).1
    have e1 : EnergyBil (u + θ • h) (u + θ • h)
        = EnergyBil u (u + θ • h) + θ * EnergyBil h (u + θ • h) := by
      rw [(hbil u (θ • h) (u + θ • h) 0 huV hthV hwV).1,
        (hbil h h (u + θ • h) θ hhV hhV hwV).2.1]
    have e2 : EnergyBil u (u + θ • h)
        = (Energy u).toReal + θ * EnergyBil h u := by
      rw [(hbil u u (u + θ • h) 0 huV huV hwV).2.2,
        (hbil u (θ • h) u 0 huV hthV huV).1,
        (hbil h h u θ hhV hhV huV).2.1, hdiag u huV]
    have e3 : EnergyBil h (u + θ • h)
        = EnergyBil u h + θ * (Energy h).toReal := by
      rw [(hbil h h (u + θ • h) 0 hhV hhV hwV).2.2,
        (hbil u (θ • h) h 0 huV hthV hhV).1,
        (hbil h h h θ hhV hhV hhV).2.1, hdiag h hhV]
    have e4 : EnergyBil h u = EnergyBil u h :=
      ((hbil h u u 0 hhV huV huV).2.2)
    rw [← hdiag _ hwV, e1, e2, e3, e4]
    ring
  -- the linear term is linear along `h`
  have hFa : MemLp (fun x => a - (F : EuclideanSpace ℝ (Fin n) → ℝ) x) 2 (GaussMeasure n) :=
    (memLp_const a).sub (Lp.memLp F)
  have hlin : ∀ θ : ℝ,
      (∫ x, (a - (F : EuclideanSpace ℝ (Fin n) → ℝ) x)
          * ((u + θ • h : Lp ℝ 2 (GaussMeasure n)) : EuclideanSpace ℝ (Fin n) → ℝ) x
          ∂(GaussMeasure n))
        = (∫ x, (a - (F : EuclideanSpace ℝ (Fin n) → ℝ) x)
            * (u : EuclideanSpace ℝ (Fin n) → ℝ) x ∂(GaussMeasure n))
          + θ * ∫ x, (a - (F : EuclideanSpace ℝ (Fin n) → ℝ) x)
            * (h : EuclideanSpace ℝ (Fin n) → ℝ) x ∂(GaussMeasure n) := by
    intro θ
    have iu : Integrable (fun x => (a - (F : EuclideanSpace ℝ (Fin n) → ℝ) x)
        * (u : EuclideanSpace ℝ (Fin n) → ℝ) x) (GaussMeasure n) :=
      hFa.integrable_mul (Lp.memLp u)
    have ih : Integrable (fun x => (a - (F : EuclideanSpace ℝ (Fin n) → ℝ) x)
        * (h : EuclideanSpace ℝ (Fin n) → ℝ) x) (GaussMeasure n) :=
      hFa.integrable_mul (Lp.memLp h)
    rw [← integral_const_mul, ← integral_add iu (ih.const_mul θ)]
    refine integral_congr_ae ?_
    filter_upwards [Lp.coeFn_add u (θ • h), Lp.coeFn_smul θ h] with x hadd hsm
    rw [hadd, Pi.add_apply, hsm, Pi.smul_apply, smul_eq_mul]
    ring
  -- admissibility of the competitor `u + θ h` for `0 < θ ≤ 1`
  have hadm : ∀ θ : ℝ, 0 < θ → θ ≤ 1 → (u + θ • h) ∈ ObstacleCone n := by
    intro θ hθ0 hθ1
    refine ⟨(hsub u (θ • h) 0 huV ((hsub h h θ hhV hhV).2)).1, ?_⟩
    filter_upwards [hu0, hv0, hhc, Lp.coeFn_add u (θ • h), Lp.coeFn_smul θ h]
      with x h1 h2 h3 hadd hsm
    rw [hadd, Pi.add_apply, hsm, Pi.smul_apply, smul_eq_mul, h3]
    nlinarith
  -- minimality gives the one-sided difference quotient bound
  have hquot : ∀ θ : ℝ, 0 < θ → θ ≤ 1 →
      0 ≤ (EnergyBil u h + ∫ x, (a - (F : EuclideanSpace ℝ (Fin n) → ℝ) x)
            * (h : EuclideanSpace ℝ (Fin n) → ℝ) x ∂(GaussMeasure n))
          + θ * ((Energy h).toReal / 2) := by
    intro θ hθ0 hθ1
    have hmin' := hmin (u + θ • h) (hadm θ hθ0 hθ1)
    rw [ObstacleFunctional, ObstacleFunctional, hexp θ, hlin θ] at hmin'
    refine le_of_mul_le_mul_left ?_ hθ0
    have hprod : 0 ≤ θ * ((EnergyBil u h
        + ∫ x, (a - (F : EuclideanSpace ℝ (Fin n) → ℝ) x)
            * (h : EuclideanSpace ℝ (Fin n) → ℝ) x ∂(GaussMeasure n))
        + θ * ((Energy h).toReal / 2)) := by nlinarith [hmin']
    simpa using hprod
  -- let θ ↓ 0
  have hC : 0 ≤ EnergyBil u h + ∫ x, (a - (F : EuclideanSpace ℝ (Fin n) → ℝ) x)
      * (h : EuclideanSpace ℝ (Fin n) → ℝ) x ∂(GaussMeasure n) := by
    set C := EnergyBil u h + ∫ x, (a - (F : EuclideanSpace ℝ (Fin n) → ℝ) x)
      * (h : EuclideanSpace ℝ (Fin n) → ℝ) x ∂(GaussMeasure n) with hCdef
    set D := (Energy h).toReal / 2 with hDdef
    have htend : Filter.Tendsto (fun θ : ℝ => C + θ * D)
        (nhdsWithin 0 (Set.Ioi (0:ℝ))) (nhds C) := by
      have ht : Filter.Tendsto (fun θ : ℝ => C + θ * D) (nhds 0) (nhds (C + 0 * D)) :=
        (continuous_const.add (continuous_id.mul continuous_const)).tendsto 0
      simpa using ht.mono_left nhdsWithin_le_nhds
    have hev : ∀ᶠ θ : ℝ in nhdsWithin 0 (Set.Ioi (0:ℝ)), 0 ≤ C + θ * D := by
      have h1 : ∀ᶠ θ : ℝ in nhdsWithin 0 (Set.Ioi (0:ℝ)), θ ≤ 1 := by
        filter_upwards [nhdsWithin_le_nhds (Iio_mem_nhds (by norm_num : (0:ℝ) < 1))]
          with θ hθ using le_of_lt hθ
      filter_upwards [h1, self_mem_nhdsWithin] with θ hθ1 hθ0
      exact hquot θ hθ0 hθ1
    exact ge_of_tendsto htend hev
  -- rewrite the goal through `h`
  have hgoal : (∫ x, ((F : EuclideanSpace ℝ (Fin n) → ℝ) x - a)
      * ((v : EuclideanSpace ℝ (Fin n) → ℝ) x - (u : EuclideanSpace ℝ (Fin n) → ℝ) x)
      ∂(GaussMeasure n))
      = -∫ x, (a - (F : EuclideanSpace ℝ (Fin n) → ℝ) x)
          * (h : EuclideanSpace ℝ (Fin n) → ℝ) x ∂(GaussMeasure n) := by
    rw [← integral_neg]
    refine integral_congr_ae ?_
    filter_upwards [hhc] with x hx
    rw [hx]; ring
  rw [hgoal]
  linarith [hC]
