module

public import GaussianRiesz.ObstacleMultiplier
public import GaussianRiesz.EnergyConstantInvariance
public import GaussianRiesz.Hermite1Zero
public import GaussianRiesz.L2IntoL1
public import GaussianRiesz.HermiteZeroModeConstant

@[expose] public section
open MeasureTheory
theorem MassConservation {n : ℕ} (F : Lp ℝ 2 (GaussMeasure n)) (m a : ℝ)
    (hm : m = ∫ x, (F : EuclideanSpace ℝ (Fin n) → ℝ) x ∂(GaussMeasure n))
    (u : Lp ℝ 2 (GaussMeasure n))
    (η : Lp ℝ 2 (GaussMeasure n))
    (hη : ∀ φ : Lp ℝ 2 (GaussMeasure n), Energy φ ≠ ⊤ →
      ObstacleMultiplier F a u φ
        = ∫ x, (η : EuclideanSpace ℝ (Fin n) → ℝ) x
            * (φ : EuclideanSpace ℝ (Fin n) → ℝ) x ∂(GaussMeasure n)) :
    ∫ x, (a - (η : EuclideanSpace ℝ (Fin n) → ℝ) x) ∂(GaussMeasure n) = m := by
  classical
  -- the index-`0` Hermite element is the constant function `1`
  -- its energy vanishes, so it is an admissible test function
  have hcoe : ((HermiteBasis n) : (Fin n → ℕ) → Lp ℝ 2 (GaussMeasure n))
      = HermiteL2 (n := n) := HilbertBasis.coe_mk _ _
  have hzero : ∀ α : Fin n → ℕ, α ≠ 0 →
      (HermiteBasis n).repr (HermiteL2 (0 : Fin n → ℕ)) α = 0 := by
    intro α hα
    have h0 : HermiteL2 (0 : Fin n → ℕ) = (HermiteBasis n) (0 : Fin n → ℕ) := by rw [hcoe]
    rw [h0, HilbertBasis.repr_self, lp.single_apply_ne _ _ _ hα]
  have hE0 : Energy (HermiteL2 (0 : Fin n → ℕ)) = 0 := by
    have hz : ∀ α : {α : Fin n → ℕ // α ≠ 0},
        ENNReal.ofReal ((MultiIndexSum (α : Fin n → ℕ) : ℝ) ^ ((1 : ℝ) / 2)
          * ((HermiteBasis n).repr (HermiteL2 (0 : Fin n → ℕ)) (α : Fin n → ℕ)) ^ 2) = 0 := by
      intro α
      rw [hzero (α : Fin n → ℕ) α.2]
      simp
    rw [Energy, tsum_congr hz, tsum_zero]
  -- integrability of the data
  have hFint : Integrable ((F : Lp ℝ 2 (GaussMeasure n)) :
      EuclideanSpace ℝ (Fin n) → ℝ) (GaussMeasure n) := (Lp.memLp F).integrable (by norm_num)
  have hηint : Integrable ((η : Lp ℝ 2 (GaussMeasure n)) :
      EuclideanSpace ℝ (Fin n) → ℝ) (GaussMeasure n) := (Lp.memLp η).integrable (by norm_num)
  -- test the representation hypothesis against `1`
  have hrep := hη (HermiteL2 (0 : Fin n → ℕ)) (by rw [hE0]; exact ENNReal.zero_ne_top)
  rw [ObstacleMultiplier, (EnergyConstantInvariance u (0 : ℝ)).1] at hrep
  have hmass := (HermiteZeroModeConstant (n := n)).1
  have hL : ∫ x, ((F : EuclideanSpace ℝ (Fin n) → ℝ) x - a)
      * ((HermiteL2 (0 : Fin n → ℕ) : Lp ℝ 2 (GaussMeasure n)) :
          EuclideanSpace ℝ (Fin n) → ℝ) x ∂(GaussMeasure n)
      = m - a := by
    have h1 := hmass (fun x => (F : EuclideanSpace ℝ (Fin n) → ℝ) x - a)
    rw [h1, integral_sub hFint (integrable_const a), integral_const, hm]
    simp [Measure.real]
  have hR := hmass ((η : Lp ℝ 2 (GaussMeasure n)) : EuclideanSpace ℝ (Fin n) → ℝ)
  rw [hL, hR] at hrep
  rw [integral_sub (integrable_const a) hηint, integral_const]
  simp only [Measure.real, measure_univ, ENNReal.toReal_one, one_smul]
  linarith
