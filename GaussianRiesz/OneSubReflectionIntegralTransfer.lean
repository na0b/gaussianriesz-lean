module

public import GaussianRiesz.Preamble

@[expose] public section
open MeasureTheory
theorem OneSubReflectionIntegralTransfer :
    (∀ (g : ℝ → ℝ) (c : ℝ),
        ∫ r in Set.Ioo (1 - c) 1, g (1 - r) = ∫ τ in Set.Ioo (0:ℝ) c, g τ)
      ∧ (∀ (g : ℝ → ℝ) (c : ℝ), IntegrableOn g (Set.Ioo (0:ℝ) c) volume →
        IntegrableOn (fun r : ℝ => g (1 - r)) (Set.Ioo (1 - c) 1) volume) := by
  have hmp : MeasurePreserving (fun t : ℝ => 1 - t) volume volume :=
    Measure.measurePreserving_sub_left volume 1
  have hme : MeasurableEmbedding (fun t : ℝ => 1 - t) :=
    (Homeomorph.subLeft (1:ℝ)).measurableEmbedding
  have hpre : ∀ c : ℝ,
      (fun t : ℝ => 1 - t) ⁻¹' Set.Ioo (0:ℝ) c = Set.Ioo (1 - c) 1 := by
    intro c
    ext t
    simp only [Set.mem_preimage, Set.mem_Ioo]
    exact ⟨fun ⟨h1, h2⟩ => ⟨by linarith, by linarith⟩,
      fun ⟨h1, h2⟩ => ⟨by linarith, by linarith⟩⟩
  refine ⟨fun g c => ?_, fun g c hg => ?_⟩
  · have h := hmp.setIntegral_preimage_emb hme g (Set.Ioo (0:ℝ) c)
    rwa [hpre c] at h
  · have h2 := (MeasurePreserving.integrableOn_comp_preimage hmp hme).2 hg
    rwa [hpre c] at h2
