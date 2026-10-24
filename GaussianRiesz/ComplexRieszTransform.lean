import GaussianRiesz.RieszTransform
open MeasureTheory
noncomputable def ComplexRieszTransform {n : ℕ} (v : Lp ℂ 2 (GaussMeasure n)) :
    Lp (EuclideanSpace ℂ (Fin n)) 2 (GaussMeasure n) :=
  ((PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n => ℂ)).symm.toContinuousLinearMap.comp
      (ContinuousLinearMap.pi fun i => Complex.ofRealCLM.comp (EuclideanSpace.proj i))).compLp
        (RieszTransform (Complex.reCLM.compLp v))
  + Complex.I •
      (((PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n => ℂ)).symm.toContinuousLinearMap.comp
        (ContinuousLinearMap.pi fun i => Complex.ofRealCLM.comp (EuclideanSpace.proj i))).compLp
          (RieszTransform (Complex.imCLM.compLp v)))
