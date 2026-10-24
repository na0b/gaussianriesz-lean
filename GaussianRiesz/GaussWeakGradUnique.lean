import GaussianRiesz.HasGaussWeakGrad
import GaussianRiesz.GaussIsProb
import GaussianRiesz.GaussL2LocallyIntegrable
import GaussianRiesz.GaussCoordMemLp
open MeasureTheory
theorem GaussWeakGradUnique {n : ℕ} (v : EuclideanSpace ℝ (Fin n) → ℝ)
    (G H : Lp (EuclideanSpace ℝ (Fin n)) 2 (GaussMeasure n))
    (hG : HasGaussWeakGrad v (G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)))
    (hH : HasGaussWeakGrad v (H : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))) :
    G = H := by
  classical
  -- Step 1: the two defining identities give the same tested integral
  have hkey : ∀ (j : Fin n) (g : EuclideanSpace ℝ (Fin n) → ℝ),
      ContDiff ℝ (⊤ : ℕ∞) g → HasCompactSupport g →
      ∫ x, g x • (G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) x j
        = ∫ x, g x • (H : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) x j := by
    intro j g hg1 hg2
    have h := (hG j g hg1 hg2).symm.trans (hH j g hg1 hg2)
    have h' : (∫ x, (G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) x j * g x)
        = ∫ x, (H : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) x j * g x :=
      neg_inj.mp h
    simpa only [smul_eq_mul, mul_comm] using h'
  -- Step 2-3: local integrability plus du Bois-Reymond, coordinate by coordinate
  have hae : ∀ j : Fin n, ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
      (G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) x j
        = (H : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) x j := by
    intro j
    exact ae_eq_of_integral_contDiff_smul_eq
      (GaussL2LocallyIntegrable _ (GaussCoordMemLp G j)).1
      (GaussL2LocallyIntegrable _ (GaussCoordMemLp H j)).1
      (fun g hg1 hg2 => hkey j g hg1 hg2)
  have haeall : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
      (G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) x
        = (H : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) x := by
    have h := ae_all_iff.mpr hae
    filter_upwards [h] with x hx
    exact PiLp.ext hx
  -- Step 4: transfer the null set from Lebesgue measure to `γₙ`
  have hac : (GaussMeasure n) ≪ (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
    rw [GaussMeasure]
    exact withDensity_absolutelyContinuous _ _
  exact Lp.ext (Filter.Eventually.filter_mono hac.ae_le haeall)
