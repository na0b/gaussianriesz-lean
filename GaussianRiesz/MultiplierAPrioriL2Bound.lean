import GaussianRiesz.LewyStampacchia
import GaussianRiesz.ObstacleMultiplierLinearOnFormDomain
import GaussianRiesz.LatticeContraction
import GaussianRiesz.L2IntoL1
import GaussianRiesz.MultiplierPositive
import GaussianRiesz.PosPartConstSubMemLp
import GaussianRiesz.EnergyFormBilinear
import GaussianRiesz.L2InnerGaussIntegral
import GaussianRiesz.HermiteL2ZeroAEOne
import GaussianRiesz.GaussIsProb
open MeasureTheory
theorem MultiplierAPrioriL2Bound {n : ℕ} (F : Lp ℝ 2 (GaussMeasure n))
    (hF : 0 ≤ᵐ[GaussMeasure n] (F : EuclideanSpace ℝ (Fin n) → ℝ)) (a : ℝ) (ha : 0 < a)
    (u : Lp ℝ 2 (GaussMeasure n)) (hu : u ∈ ObstacleCone n)
    (hmin : ∀ w ∈ ObstacleCone n, ObstacleFunctional F a u ≤ ObstacleFunctional F a w) :
    ∀ ψ : Lp ℝ 2 (GaussMeasure n), Energy ψ ≠ ⊤ →
      |ObstacleMultiplier F a u ψ| ≤ a * ‖ψ‖ := by
  classical
  have hprob : IsProbabilityMeasure (GaussMeasure n) := GaussIsProb n
  obtain ⟨hmixsum, -, -, hclosed⟩ := EnergyFormBilinear (n := n)
  have huE : Energy u ≠ ⊤ := hu.1
  -- the multiplier as the energy form minus a fixed inner product, hence additive and
  obtain ⟨-, hTadd, hTsmul⟩ := ObstacleMultiplierLinearOnFormDomain F a u huE
  -- the kernel `k = (a - F)⁺` as an `L²` element
  have hk := PosPartConstSubMemLp F a
  have hlip1 : LipschitzWith 1 (fun t : ℝ => max t 0) := by
    have h := (LipschitzWith.id (α := ℝ)).max (LipschitzWith.const (α := ℝ) (0 : ℝ))
    simpa [Function.id_def] using h
  have hlip2 : LipschitzWith 1 (fun t : ℝ => max (-t) 0) := by
    have h := ((LipschitzWith.id (α := ℝ)).neg).max (LipschitzWith.const (α := ℝ) (0 : ℝ))
    simpa [Function.id_def] using h
  intro ψ hψ
  -- positive part
  have hpm : AEStronglyMeasurable
      (fun x => max ((ψ : EuclideanSpace ℝ (Fin n) → ℝ) x) 0) (GaussMeasure n) :=
    (Lp.aestronglyMeasurable ψ).sup aestronglyMeasurable_const
  have hpL : MemLp (fun x => max ((ψ : EuclideanSpace ℝ (Fin n) → ℝ) x) 0) 2
      (GaussMeasure n) := by
    refine MemLp.of_le (Lp.memLp ψ) hpm (Filter.Eventually.of_forall fun x => ?_)
    simp only [Real.norm_eq_abs]
    rw [abs_of_nonneg (le_max_right _ _)]
    exact max_le (le_abs_self _) (abs_nonneg _)
  set ψp : Lp ℝ 2 (GaussMeasure n) := hpL.toLp _ with hψpdef
  have hψpc : (ψp : EuclideanSpace ℝ (Fin n) → ℝ)
      =ᵐ[GaussMeasure n] fun x => max ((ψ : EuclideanSpace ℝ (Fin n) → ℝ) x) 0 :=
    hpL.coeFn_toLp
  -- negative part
  have hmm : AEStronglyMeasurable
      (fun x => max (-((ψ : EuclideanSpace ℝ (Fin n) → ℝ) x)) 0) (GaussMeasure n) :=
    ((Lp.aestronglyMeasurable ψ).neg).sup aestronglyMeasurable_const
  have hmL : MemLp (fun x => max (-((ψ : EuclideanSpace ℝ (Fin n) → ℝ) x)) 0) 2
      (GaussMeasure n) := by
    refine MemLp.of_le (Lp.memLp ψ) hmm (Filter.Eventually.of_forall fun x => ?_)
    simp only [Real.norm_eq_abs]
    rw [abs_of_nonneg (le_max_right _ _)]
    exact max_le (neg_le_abs _) (abs_nonneg _)
  set ψm : Lp ℝ 2 (GaussMeasure n) := hmL.toLp _ with hψmdef
  have hψmc : (ψm : EuclideanSpace ℝ (Fin n) → ℝ)
      =ᵐ[GaussMeasure n] fun x => max (-((ψ : EuclideanSpace ℝ (Fin n) → ℝ) x)) 0 :=
    hmL.coeFn_toLp
  -- both parts lie in the cone
  have hψpV : Energy ψp ≠ ⊤ :=
    (LatticeContraction (fun t : ℝ => max t 0) hlip1 (by simp) ψ ψp hψ hψpc).1
  have hψmV : Energy ψm ≠ ⊤ :=
    (LatticeContraction (fun t : ℝ => max (-t) 0) hlip2 (by simp) ψ ψm hψ hψmc).1
  have hψpnn : 0 ≤ᵐ[GaussMeasure n] (ψp : EuclideanSpace ℝ (Fin n) → ℝ) := by
    filter_upwards [hψpc] with x hx
    rw [hx]
    exact le_max_right _ _
  have hψmnn : 0 ≤ᵐ[GaussMeasure n] (ψm : EuclideanSpace ℝ (Fin n) → ℝ) := by
    filter_upwards [hψmc] with x hx
    rw [hx]
    exact le_max_right _ _
  have hpcone : ψp ∈ ObstacleCone n := ⟨hψpV, hψpnn⟩
  have hmcone : ψm ∈ ObstacleCone n := ⟨hψmV, hψmnn⟩
  -- `ψ = ψ⁺ - ψ⁻`
  have hψeq : ψ = ψp + (-1 : ℝ) • ψm := by
    refine Lp.ext ?_
    filter_upwards [hψpc, hψmc, Lp.coeFn_add ψp ((-1 : ℝ) • ψm),
      Lp.coeFn_smul (-1 : ℝ) ψm] with x hp hm hadd hsm
    rw [hadd, Pi.add_apply, hsm, Pi.smul_apply, smul_eq_mul, hp, hm]
    rcases le_or_gt ((ψ : EuclideanSpace ℝ (Fin n) → ℝ) x) 0 with h | h
    · rw [max_eq_right h, max_eq_left (by linarith)]; ring
    · rw [max_eq_left (le_of_lt h), max_eq_right (by linarith)]; ring
  have hsplit : ObstacleMultiplier F a u ψ
      = ObstacleMultiplier F a u ψp - ObstacleMultiplier F a u ψm := by
    rw [hψeq, hTadd _ _ hψpV ((hclosed ψm ψm (-1) hψmV hψmV).2), hTsmul (-1) ψm hψmV]
    ring
  have hTp : 0 ≤ ObstacleMultiplier F a u ψp := MultiplierPositive F a u hu hmin ψp hpcone
  have hTm : 0 ≤ ObstacleMultiplier F a u ψm := MultiplierPositive F a u hu hmin ψm hmcone
  -- `|ψ| = ψ⁺ + ψ⁻` lies in the cone
  have hsumnn : 0 ≤ᵐ[GaussMeasure n]
      ((ψp + ψm : Lp ℝ 2 (GaussMeasure n)) : EuclideanSpace ℝ (Fin n) → ℝ) := by
    filter_upwards [Lp.coeFn_add ψp ψm, hψpnn, hψmnn] with x hx h1 h2
    simp only [Pi.zero_apply] at h1 h2 ⊢
    rw [hx, Pi.add_apply]
    linarith
  have hsumcone : (ψp + ψm) ∈ ObstacleCone n := ⟨(hclosed ψp ψm 0 hψpV hψmV).1, hsumnn⟩
  have habs : |ObstacleMultiplier F a u ψ| ≤ ObstacleMultiplier F a u (ψp + ψm) := by
    rw [hTadd ψp ψm hψpV hψmV, hsplit, abs_sub_le_iff]
    exact ⟨by linarith, by linarith⟩
  -- the Lewy-Stampacchia bound, then `0 ≤ k ≤ a` and `L² ⊆ L¹`
  have hLS := LewyStampacchia F hF a u hu hmin (ψp + ψm) hsumcone
  have hac : ((ψp + ψm : Lp ℝ 2 (GaussMeasure n)) : EuclideanSpace ℝ (Fin n) → ℝ)
      =ᵐ[GaussMeasure n] fun x => |(ψ : EuclideanSpace ℝ (Fin n) → ℝ) x| := by
    filter_upwards [Lp.coeFn_add ψp ψm, hψpc, hψmc] with x hx h1 h2
    rw [hx, Pi.add_apply, h1, h2]
    rcases le_or_gt ((ψ : EuclideanSpace ℝ (Fin n) → ℝ) x) 0 with h | h
    · rw [max_eq_right h, max_eq_left (by linarith), abs_of_nonpos h]; ring
    · rw [max_eq_left (le_of_lt h), max_eq_right (by linarith), abs_of_pos h]; ring
  have hkle : ∀ᵐ x ∂(GaussMeasure n),
      max (a - (F : EuclideanSpace ℝ (Fin n) → ℝ) x) 0
          * ((ψp + ψm : Lp ℝ 2 (GaussMeasure n)) : EuclideanSpace ℝ (Fin n) → ℝ) x
        ≤ a * |(ψ : EuclideanSpace ℝ (Fin n) → ℝ) x| := by
    filter_upwards [hF, hac] with x hFx hax
    simp only [Pi.zero_apply] at hFx
    rw [hax]
    refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
    rcases le_total (a - (F : EuclideanSpace ℝ (Fin n) → ℝ) x) 0 with h | h
    · rw [max_eq_right h]; linarith
    · rw [max_eq_left h]; linarith
  have hint1 : Integrable (fun x => max (a - (F : EuclideanSpace ℝ (Fin n) → ℝ) x) 0
      * ((ψp + ψm : Lp ℝ 2 (GaussMeasure n)) : EuclideanSpace ℝ (Fin n) → ℝ) x)
      (GaussMeasure n) := hk.integrable_mul (Lp.memLp _)
  have hintψ : Integrable (ψ : EuclideanSpace ℝ (Fin n) → ℝ) (GaussMeasure n) :=
    (Lp.memLp ψ).integrable (by norm_num)
  have hint2 : Integrable (fun x => a * |(ψ : EuclideanSpace ℝ (Fin n) → ℝ) x|)
      (GaussMeasure n) := hintψ.abs.const_mul a
  have hle2 : ∫ x, max (a - (F : EuclideanSpace ℝ (Fin n) → ℝ) x) 0
        * ((ψp + ψm : Lp ℝ 2 (GaussMeasure n)) : EuclideanSpace ℝ (Fin n) → ℝ) x
          ∂(GaussMeasure n)
      ≤ ∫ x, a * |(ψ : EuclideanSpace ℝ (Fin n) → ℝ) x| ∂(GaussMeasure n) :=
    integral_mono_ae hint1 hint2 hkle
  have htoL1 : ((ToL1 ψ : Lp ℝ 1 (GaussMeasure n)) : EuclideanSpace ℝ (Fin n) → ℝ)
      =ᵐ[GaussMeasure n] (ψ : EuclideanSpace ℝ (Fin n) → ℝ) := by
    rw [ToL1]
    exact MemLp.coeFn_toLp _
  have hL1 : ‖ToL1 ψ‖ = ∫ x, |(ψ : EuclideanSpace ℝ (Fin n) → ℝ) x| ∂(GaussMeasure n) := by
    rw [L1.norm_eq_integral_norm]
    refine integral_congr_ae ?_
    filter_upwards [htoL1] with x hx
    rw [hx, Real.norm_eq_abs]
  have hfinal : ∫ x, a * |(ψ : EuclideanSpace ℝ (Fin n) → ℝ) x| ∂(GaussMeasure n)
      ≤ a * ‖ψ‖ := by
    rw [integral_const_mul, ← hL1]
    exact mul_le_mul_of_nonneg_left (L2IntoL1 ψ) ha.le
  calc |ObstacleMultiplier F a u ψ|
      ≤ ObstacleMultiplier F a u (ψp + ψm) := habs
    _ ≤ ∫ x, max (a - (F : EuclideanSpace ℝ (Fin n) → ℝ) x) 0
          * ((ψp + ψm : Lp ℝ 2 (GaussMeasure n)) : EuclideanSpace ℝ (Fin n) → ℝ) x
            ∂(GaussMeasure n) := hLS
    _ ≤ ∫ x, a * |(ψ : EuclideanSpace ℝ (Fin n) → ℝ) x| ∂(GaussMeasure n) := hle2
    _ ≤ a * ‖ψ‖ := hfinal
