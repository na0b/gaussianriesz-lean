import GaussianRiesz.ObstacleFunctional
import GaussianRiesz.ObstacleCone
import GaussianRiesz.FractionalGap
import GaussianRiesz.EnergyConstantInvariance
import GaussianRiesz.L2IntoL1
import GaussianRiesz.L2InnerGaussIntegral
import GaussianRiesz.HermiteZeroModeConstant
open MeasureTheory
theorem ObstacleCoercivity {n : ℕ} (F : Lp ℝ 2 (GaussMeasure n)) (m a : ℝ)
    (hm : m = ∫ x, (F : EuclideanSpace ℝ (Fin n) → ℝ) x ∂(GaussMeasure n)) (ha : m < a) :
    (∀ v ∈ ObstacleCone n,
        (Energy v).toReal / 4
          + (a - m) * (∫ x, (v : EuclideanSpace ℝ (Fin n) → ℝ) x ∂(GaussMeasure n))
          - ‖F - m • HermiteL2 (0 : Fin n → ℕ)‖ ^ 2
        ≤ ObstacleFunctional F a v)
      ∧ -‖F - m • HermiteL2 (0 : Fin n → ℕ)‖ ^ 2
          ≤ sInf (ObstacleFunctional F a '' ObstacleCone n)
      ∧ sInf (ObstacleFunctional F a '' ObstacleCone n) ≤ 0 := by
  classical
  -- `h₀` is the constant function `1`; the inner products against the constant mode
  obtain ⟨-, hvh0, hh0v, hhh, -⟩ := HermiteZeroModeConstant (n := n)
  have hFh : inner ℝ F (HermiteL2 (0 : Fin n → ℕ)) = m := by rw [hvh0 F, ← hm]
  -- clause (1)
  have key : ∀ v ∈ ObstacleCone n,
      (Energy v).toReal / 4
        + (a - m) * (∫ x, (v : EuclideanSpace ℝ (Fin n) → ℝ) x ∂(GaussMeasure n))
        - ‖F - m • HermiteL2 (0 : Fin n → ℕ)‖ ^ 2
      ≤ ObstacleFunctional F a v := by
    intro v hv
    obtain ⟨hvE, hvnn⟩ := hv
    have hvint : Integrable ((v : Lp ℝ 2 (GaussMeasure n)) :
        EuclideanSpace ℝ (Fin n) → ℝ) (GaussMeasure n) := (Lp.memLp v).integrable (by norm_num)
    have hFv : Integrable (fun x => (F : EuclideanSpace ℝ (Fin n) → ℝ) x
        * (v : EuclideanSpace ℝ (Fin n) → ℝ) x) (GaussMeasure n) :=
      (Lp.memLp F).integrable_mul (Lp.memLp v)
    have hhv := hh0v v
    -- the linear term
    have hL : ∫ x, (a - (F : EuclideanSpace ℝ (Fin n) → ℝ) x)
          * (v : EuclideanSpace ℝ (Fin n) → ℝ) x ∂(GaussMeasure n)
        = a * (∫ x, (v : EuclideanSpace ℝ (Fin n) → ℝ) x ∂(GaussMeasure n))
          - inner ℝ F v := by
      rw [L2InnerGaussIntegral F v]
      have hfe : (fun x => (a - (F : EuclideanSpace ℝ (Fin n) → ℝ) x)
            * (v : EuclideanSpace ℝ (Fin n) → ℝ) x)
          = fun x => a * (v : EuclideanSpace ℝ (Fin n) → ℝ) x
              - (F : EuclideanSpace ℝ (Fin n) → ℝ) x
                * (v : EuclideanSpace ℝ (Fin n) → ℝ) x := by
        funext x; ring
      rw [hfe, integral_sub (hvint.const_mul a) hFv, integral_const_mul]
    -- the centred element and its energy bound
    have hw : v - (∫ x, (v : EuclideanSpace ℝ (Fin n) → ℝ) x ∂(GaussMeasure n))
          • HermiteL2 (0 : Fin n → ℕ) = FracPow (0 : ℝ) v := (ProjZeroCentering v).symm
    have hwn : ‖v - (∫ x, (v : EuclideanSpace ℝ (Fin n) → ℝ) x ∂(GaussMeasure n))
          • HermiteL2 (0 : Fin n → ℕ)‖ ^ 2 ≤ (Energy v).toReal := by
      rw [hw]
      exact (ENNReal.ofReal_le_iff_le_toReal hvE).mp (FractionalGap v)
    -- bilinear expansion of the cross term
    have hbil : inner ℝ (F - m • HermiteL2 (0 : Fin n → ℕ))
          (v - (∫ x, (v : EuclideanSpace ℝ (Fin n) → ℝ) x ∂(GaussMeasure n))
            • HermiteL2 (0 : Fin n → ℕ))
        = inner ℝ F v
          - m * (∫ x, (v : EuclideanSpace ℝ (Fin n) → ℝ) x ∂(GaussMeasure n)) := by
      simp only [inner_sub_left, inner_sub_right, real_inner_smul_left, real_inner_smul_right,
        hFh, hhv, hhh]
      ring
    have hCS := abs_real_inner_le_norm (F - m • HermiteL2 (0 : Fin n → ℕ))
      (v - (∫ x, (v : EuclideanSpace ℝ (Fin n) → ℝ) x ∂(GaussMeasure n))
        • HermiteL2 (0 : Fin n → ℕ))
    have h1 : inner ℝ F v
        - m * (∫ x, (v : EuclideanSpace ℝ (Fin n) → ℝ) x ∂(GaussMeasure n))
        ≤ ‖F - m • HermiteL2 (0 : Fin n → ℕ)‖
          * ‖v - (∫ x, (v : EuclideanSpace ℝ (Fin n) → ℝ) x ∂(GaussMeasure n))
            • HermiteL2 (0 : Fin n → ℕ)‖ := by
      rw [← hbil]
      exact (le_abs_self _).trans hCS
    rw [ObstacleFunctional, hL]
    nlinarith [h1, hwn, norm_nonneg (F - m • HermiteL2 (0 : Fin n → ℕ)),
      norm_nonneg (v - (∫ x, (v : EuclideanSpace ℝ (Fin n) → ℝ) x ∂(GaussMeasure n))
        • HermiteL2 (0 : Fin n → ℕ)),
      sq_nonneg (‖F - m • HermiteL2 (0 : Fin n → ℕ)‖
        - ‖v - (∫ x, (v : EuclideanSpace ℝ (Fin n) → ℝ) x ∂(GaussMeasure n))
          • HermiteL2 (0 : Fin n → ℕ)‖ / 2),
      ENNReal.toReal_nonneg (a := Energy v)]
  -- the zero function lies in the cone and `J` vanishes there
  have hE0 : Energy (0 : Lp ℝ 2 (GaussMeasure n)) = 0 := by
    have hz : ∀ α : {α : Fin n → ℕ // α ≠ 0},
        ENNReal.ofReal ((MultiIndexSum (α : Fin n → ℕ) : ℝ) ^ ((1 : ℝ) / 2)
          * ((HermiteBasis n).repr (0 : Lp ℝ 2 (GaussMeasure n)) (α : Fin n → ℕ)) ^ 2) = 0 := by
      intro α; simp
    rw [Energy, tsum_congr hz, tsum_zero]
  have hcone0 : (0 : Lp ℝ 2 (GaussMeasure n)) ∈ ObstacleCone n := by
    refine ⟨by rw [hE0]; exact ENNReal.zero_ne_top, ?_⟩
    filter_upwards [Lp.coeFn_zero (E := ℝ) (p := 2) (μ := GaussMeasure n)] with x hx
    rw [hx]
  have hJ0 : ObstacleFunctional F a (0 : Lp ℝ 2 (GaussMeasure n)) = 0 := by
    rw [ObstacleFunctional, hE0]
    have : ∫ x, (a - (F : EuclideanSpace ℝ (Fin n) → ℝ) x)
        * ((0 : Lp ℝ 2 (GaussMeasure n)) : EuclideanSpace ℝ (Fin n) → ℝ) x
        ∂(GaussMeasure n) = 0 := by
      rw [show (0 : ℝ) = ∫ _x : EuclideanSpace ℝ (Fin n), (0 : ℝ) ∂(GaussMeasure n) from by simp]
      refine integral_congr_ae ?_
      filter_upwards [Lp.coeFn_zero (E := ℝ) (p := 2) (μ := GaussMeasure n)] with x hx
      rw [hx]
      simp
    rw [this]
    simp
  -- the lower bound on the infimum
  have hlb : ∀ y ∈ ObstacleFunctional F a '' ObstacleCone n,
      -‖F - m • HermiteL2 (0 : Fin n → ℕ)‖ ^ 2 ≤ y := by
    rintro y ⟨v, hv, rfl⟩
    have hc0 : 0 ≤ ∫ x, (v : EuclideanSpace ℝ (Fin n) → ℝ) x ∂(GaussMeasure n) :=
      integral_nonneg_of_ae hv.2
    have hk := key v hv
    nlinarith [hk, ENNReal.toReal_nonneg (a := Energy v), hc0, sub_pos.mpr ha]
  refine ⟨key, le_csInf ⟨_, ⟨0, hcone0, rfl⟩⟩ hlb, ?_⟩
  refine (csInf_le ⟨-‖F - m • HermiteL2 (0 : Fin n → ℕ)‖ ^ 2, hlb⟩
    ⟨0, hcone0, rfl⟩).trans ?_
  rw [hJ0]
