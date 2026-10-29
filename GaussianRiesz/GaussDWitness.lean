module

public import GaussianRiesz.GaussD
public import GaussianRiesz.GaussWeakGradUnique
public import GaussianRiesz.GaussWeakGradAECongr

@[expose] public section
open MeasureTheory
theorem GaussDWitness {n : ℕ} (v : Lp ℝ 2 (GaussMeasure n))
    (Γ : Lp (EuclideanSpace ℝ (Fin n)) 2 (GaussMeasure n))
    (h : HasGaussWeakGrad (v : EuclideanSpace ℝ (Fin n) → ℝ)
      (fun x => Real.sqrt 2 •
        (Γ : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) x)) :
    v ∈ SobolevW12 n ∧ GaussD v = Γ := by
  classical
  -- the hypothesis witnesses the defining existential of `SobolevW12`
  have hmem : v ∈ SobolevW12 n := ⟨Γ, h⟩
  refine ⟨hmem, ?_⟩
  -- the chosen witness is itself a weak gradient
  have hGD : HasGaussWeakGrad (v : EuclideanSpace ℝ (Fin n) → ℝ)
      (fun x => Real.sqrt 2 •
        (GaussD v : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) x) := by
    have hg : GaussD v = hmem.choose := by simp only [GaussD, dif_pos hmem]
    rw [hg]
    exact hmem.choose_spec
  -- pass from the pointwise scaling to the scaled `L²` element
  have hup : ∀ Δ : Lp (EuclideanSpace ℝ (Fin n)) 2 (GaussMeasure n),
      HasGaussWeakGrad (v : EuclideanSpace ℝ (Fin n) → ℝ)
        (fun x => Real.sqrt 2 •
          (Δ : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) x) →
      HasGaussWeakGrad (v : EuclideanSpace ℝ (Fin n) → ℝ)
        ((Real.sqrt 2 • Δ : Lp (EuclideanSpace ℝ (Fin n)) 2 (GaussMeasure n)) :
          EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) := by
    intro Δ hΔ
    exact GaussWeakGradAECongr _ _ _ _ Filter.EventuallyEq.rfl
      (Lp.coeFn_smul (Real.sqrt 2) Δ).symm hΔ
  -- uniqueness of the weak gradient identifies the two witnesses
  have e1 : Real.sqrt 2 • GaussD v = Real.sqrt 2 • Γ :=
    GaussWeakGradUnique (v : EuclideanSpace ℝ (Fin n) → ℝ) _ _ (hup _ hGD) (hup _ h)
  exact smul_right_injective _ (by positivity : Real.sqrt 2 ≠ 0) e1
