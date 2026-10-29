module

public import GaussianRiesz.ComplexRieszTransform
public import GaussianRiesz.RieszTransformLinear

@[expose] public section
open MeasureTheory
theorem ComplexRieszTransformLinear {n : ℕ} :
    (∀ v w : Lp ℂ 2 (GaussMeasure n),
        ComplexRieszTransform (v + w)
          = ComplexRieszTransform v + ComplexRieszTransform w)
      ∧ (∀ (c : ℂ) (v : Lp ℂ 2 (GaussMeasure n)),
          ComplexRieszTransform (c • v) = c • ComplexRieszTransform v)
      ∧ (∀ (c : ℂ) (v : Lp ℂ 2 (GaussMeasure n)), ‖c‖ = 1 →
          ∀ᵐ x ∂(GaussMeasure n),
            ‖(ComplexRieszTransform (c • v) :
                EuclideanSpace ℝ (Fin n) → EuclideanSpace ℂ (Fin n)) x‖
              = ‖(ComplexRieszTransform v :
                  EuclideanSpace ℝ (Fin n) → EuclideanSpace ℂ (Fin n)) x‖) := by
  -- composing an `Lp` class with a fixed bounded linear map is additive and
  -- real-homogeneous, because `compLpₗ` is the linear map doing exactly that
  have hLadd : ∀ (L : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℂ (Fin n))
      (f g : Lp (EuclideanSpace ℝ (Fin n)) 2 (GaussMeasure n)),
      L.compLp (f + g) = L.compLp f + L.compLp g :=
    fun L f g => (L.compLpₗ 2 (GaussMeasure n)).map_add f g
  have hLsmul : ∀ (L : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℂ (Fin n))
      (r : ℝ) (f : Lp (EuclideanSpace ℝ (Fin n)) 2 (GaussMeasure n)),
      L.compLp (r • f) = r • L.compLp f :=
    fun L r f => (L.compLpₗ 2 (GaussMeasure n)).map_smul r f
  -- the real scalar action on the complex target is the restriction of the complex one
  have hrc : ∀ (r : ℝ) (x : Lp (EuclideanSpace ℂ (Fin n)) 2 (GaussMeasure n)),
      r • x = (r : ℂ) • x := by
    intro r x
    rw [← algebraMap_smul ℂ r x, Complex.coe_algebraMap]
  -- the parts of a sum
  have hre : ∀ v w : Lp ℂ 2 (GaussMeasure n),
      Complex.reCLM.compLp (v + w)
        = Complex.reCLM.compLp v + Complex.reCLM.compLp w :=
    fun v w => (Complex.reCLM.compLpₗ 2 (GaussMeasure n)).map_add v w
  have him : ∀ v w : Lp ℂ 2 (GaussMeasure n),
      Complex.imCLM.compLp (v + w)
        = Complex.imCLM.compLp v + Complex.imCLM.compLp w :=
    fun v w => (Complex.imCLM.compLpₗ 2 (GaussMeasure n)).map_add v w
  -- the parts of a complex scalar multiple: the two parts get mixed
  have hreS : ∀ (c : ℂ) (v : Lp ℂ 2 (GaussMeasure n)),
      Complex.reCLM.compLp (c • v)
        = c.re • Complex.reCLM.compLp v + (-c.im) • Complex.imCLM.compLp v := by
    intro c v
    ext1
    filter_upwards [Lp.coeFn_smul c v,
      ContinuousLinearMap.coeFn_compLp Complex.reCLM (c • v),
      ContinuousLinearMap.coeFn_compLp Complex.reCLM v,
      ContinuousLinearMap.coeFn_compLp Complex.imCLM v,
      Lp.coeFn_add (c.re • Complex.reCLM.compLp v) ((-c.im) • Complex.imCLM.compLp v),
      Lp.coeFn_smul c.re (Complex.reCLM.compLp v),
      Lp.coeFn_smul (-c.im) (Complex.imCLM.compLp v)] with a h1 h2 h3 h4 h5 h6 h7
    simp only [h1, h2, h3, h4, h5, h6, h7, Pi.smul_apply, Pi.add_apply, smul_eq_mul]
    simp [Complex.mul_re]
    ring
  have himS : ∀ (c : ℂ) (v : Lp ℂ 2 (GaussMeasure n)),
      Complex.imCLM.compLp (c • v)
        = c.re • Complex.imCLM.compLp v + c.im • Complex.reCLM.compLp v := by
    intro c v
    ext1
    filter_upwards [Lp.coeFn_smul c v,
      ContinuousLinearMap.coeFn_compLp Complex.imCLM (c • v),
      ContinuousLinearMap.coeFn_compLp Complex.imCLM v,
      ContinuousLinearMap.coeFn_compLp Complex.reCLM v,
      Lp.coeFn_add (c.re • Complex.imCLM.compLp v) (c.im • Complex.reCLM.compLp v),
      Lp.coeFn_smul c.re (Complex.imCLM.compLp v),
      Lp.coeFn_smul c.im (Complex.reCLM.compLp v)] with a h1 h2 h3 h4 h5 h6 h7
    simp only [h1, h2, h3, h4, h5, h6, h7, Pi.smul_apply, Pi.add_apply, smul_eq_mul]
    simp [Complex.mul_im]
  -- clause (2), proved first because clause (3) consumes it
  have hsmul : ∀ (c : ℂ) (v : Lp ℂ 2 (GaussMeasure n)),
      ComplexRieszTransform (c • v) = c • ComplexRieszTransform v := by
    intro c v
    simp only [ComplexRieszTransform, hreS, himS, RieszTransformLinear.1,
      (RieszTransformLinear (n := n)).2, hLadd, hLsmul, hrc]
    push_cast
    match_scalars <;> simp [Complex.ext_iff]
  refine ⟨?_, hsmul, ?_⟩
  · -- clause (1): additivity
    intro v w
    simp only [ComplexRieszTransform, hre, him, RieszTransformLinear.1, hLadd, smul_add]
    abel
  · -- clause (3): unimodular rotations preserve the pointwise size
    intro c v hc
    filter_upwards [Lp.coeFn_smul c (ComplexRieszTransform v)] with x hx
    rw [hsmul c v, hx, Pi.smul_apply, norm_smul, hc, one_mul]
