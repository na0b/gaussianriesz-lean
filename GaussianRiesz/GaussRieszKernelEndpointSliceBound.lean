module

public import GaussianRiesz.Preamble
public import GaussianRiesz.GaussRieszKernelSingularRangeSliceBound

@[expose] public section
open MeasureTheory
theorem GaussRieszKernelEndpointSliceBound {n : ℕ} (j : Fin n) :
    ∀ R ρ : ℝ, 0 < R → 0 < ρ → ∃ C : ℝ, 0 < C ∧
      ∀ x y : EuclideanSpace ℝ (Fin n), ‖x‖ ≤ R → ρ ≤ ‖x - y‖ →
        ∀ r : ℝ, 1/2 ≤ r → r < 1 →
          |(y j - r * x j) / ((1 - r ^ 2) ^ ((n : ℝ) / 2 + 1) * Real.sqrt (-Real.log r))
            * Real.exp (-‖x - r • y‖ ^ 2 / (1 - r ^ 2))| ≤ C := by
  intro R ρ hR hρ
  obtain ⟨R', hR1, hRR'⟩ : ∃ R' : ℝ, 1 ≤ R' ∧ R ≤ R' :=
    ⟨max R 1, le_max_right _ _, le_max_left _ _⟩
  obtain ⟨ρ', hρ'0, hρ'1, hρρ'⟩ : ∃ ρ' : ℝ, 0 < ρ' ∧ ρ' ≤ 1 ∧ ρ' ≤ ρ :=
    ⟨min ρ 1, lt_min hρ one_pos, min_le_right _ _, min_le_left _ _⟩
  have hR'0 : (0:ℝ) < R' := by linarith
  obtain ⟨τ₀, hτ₀0, hτ₀h, hτ₀ρ⟩ : ∃ τ₀ : ℝ, 0 < τ₀ ∧ τ₀ ≤ 1/2 ∧ τ₀ ≤ ρ' / (8 * R') :=
    ⟨min (1/2) (ρ' / (8 * R')), lt_min (by norm_num) (div_pos hρ'0 (by linarith)),
      min_le_left _ _, min_le_right _ _⟩
  -- the uniform bound on the singular range `r ∈ [1/2, 1)`, at the normalised radii
  obtain ⟨C₂, hC₂0, hC₂bd⟩ :=
    GaussRieszKernelSingularRangeSliceBound j R' ρ' τ₀ hR1 hρ'0 hτ₀0 hτ₀h hτ₀ρ
  refine ⟨C₂, hC₂0, fun x y hx hxy => hC₂bd x y (hx.trans hRR') (hρρ'.trans hxy)⟩
