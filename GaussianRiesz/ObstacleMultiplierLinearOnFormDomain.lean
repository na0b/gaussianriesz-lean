import GaussianRiesz.EnergyFormBilinear
import GaussianRiesz.L2InnerGaussIntegral
import GaussianRiesz.HermiteL2ZeroAEOne
import GaussianRiesz.ObstacleMultiplier
open MeasureTheory
theorem ObstacleMultiplierLinearOnFormDomain {n : ℕ} (F : Lp ℝ 2 (GaussMeasure n)) (a : ℝ)
    (u : Lp ℝ 2 (GaussMeasure n)) (huE : Energy u ≠ ⊤) :
    (∀ φ : Lp ℝ 2 (GaussMeasure n), ObstacleMultiplier F a u φ
        = EnergyBil u φ - (inner ℝ (F - a • HermiteL2 (0 : Fin n → ℕ)) φ : ℝ))
      ∧ (∀ v w : Lp ℝ 2 (GaussMeasure n), Energy v ≠ ⊤ → Energy w ≠ ⊤ →
          ObstacleMultiplier F a u (v + w)
            = ObstacleMultiplier F a u v + ObstacleMultiplier F a u w)
      ∧ (∀ (r : ℝ) (v : Lp ℝ 2 (GaussMeasure n)), Energy v ≠ ⊤ →
          ObstacleMultiplier F a u (r • v) = r * ObstacleMultiplier F a u v) := by
  classical
  obtain ⟨-, -, hbil, hclosed⟩ := EnergyFormBilinear (n := n)
  -- `h₀ = 1` almost everywhere, so the constant `a` is `a • h₀`
  set g : Lp ℝ 2 (GaussMeasure n) := F - a • HermiteL2 (0 : Fin n → ℕ) with hgdef
  have hgc : (g : EuclideanSpace ℝ (Fin n) → ℝ)
      =ᵐ[GaussMeasure n] fun x => (F : EuclideanSpace ℝ (Fin n) → ℝ) x - a := by
    rw [hgdef]
    filter_upwards [Lp.coeFn_sub F (a • HermiteL2 (0 : Fin n → ℕ)),
      Lp.coeFn_smul a (HermiteL2 (0 : Fin n → ℕ)), HermiteL2ZeroAEOne] with x h1 h2 h3
    rw [h1, Pi.sub_apply, h2, Pi.smul_apply, smul_eq_mul, h3, mul_one]
  -- the multiplier, rewritten with an inner product in place of the load integral
  have hT : ∀ φ : Lp ℝ 2 (GaussMeasure n),
      ObstacleMultiplier F a u φ = EnergyBil u φ - (inner ℝ g φ : ℝ) := by
    intro φ
    rw [ObstacleMultiplier, L2InnerGaussIntegral g φ]
    congr 1
    refine integral_congr_ae ?_
    filter_upwards [hgc] with x hx
    rw [hx]
  -- linearity of the multiplier on the form domain
  have hTadd : ∀ v w : Lp ℝ 2 (GaussMeasure n), Energy v ≠ ⊤ → Energy w ≠ ⊤ →
      ObstacleMultiplier F a u (v + w)
        = ObstacleMultiplier F a u v + ObstacleMultiplier F a u w := by
    intro v w hv hw
    have hvw : Energy (v + w) ≠ ⊤ := (hclosed v w 0 hv hw).1
    have e1 : EnergyBil u (v + w) = EnergyBil (v + w) u :=
      (hbil u u (v + w) 0 huE huE hvw).2.2
    have e2 : EnergyBil (v + w) u = EnergyBil v u + EnergyBil w u :=
      (hbil v w u 0 hv hw huE).1
    have e3 : EnergyBil v u = EnergyBil u v := (hbil v v u 0 hv hv huE).2.2
    have e4 : EnergyBil w u = EnergyBil u w := (hbil w w u 0 hw hw huE).2.2
    rw [hT, hT, hT, e1, e2, e3, e4, inner_add_right]
    ring
  have hTsmul : ∀ (r : ℝ) (v : Lp ℝ 2 (GaussMeasure n)), Energy v ≠ ⊤ →
      ObstacleMultiplier F a u (r • v) = r * ObstacleMultiplier F a u v := by
    intro r v hv
    have hrv : Energy (r • v) ≠ ⊤ := (hclosed v v r hv hv).2
    have e1 : EnergyBil u (r • v) = EnergyBil (r • v) u :=
      (hbil u u (r • v) 0 huE huE hrv).2.2
    have e2 : EnergyBil (r • v) u = r * EnergyBil v u := (hbil v v u r hv hv huE).2.1
    have e3 : EnergyBil v u = EnergyBil u v := (hbil v v u 0 hv hv huE).2.2
    rw [hT, hT, e1, e2, e3, real_inner_smul_right]
    ring
  exact ⟨hT, hTadd, hTsmul⟩
