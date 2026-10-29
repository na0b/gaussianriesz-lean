module

public import GaussianRiesz.ObstacleMinimizerUnique
public import GaussianRiesz.EnergyBilIsOperator
public import GaussianRiesz.EnergyFormBilinear
public import GaussianRiesz.EnergyFiniteOfSqrtDomain
public import GaussianRiesz.L2InnerGaussIntegral
public import GaussianRiesz.GaussIsProb

@[expose] public section
open MeasureTheory
theorem ObstacleDecompositionUnique {n : ℕ} (F : Lp ℝ 2 (GaussMeasure n))
    (hF : 0 ≤ᵐ[GaussMeasure n] (F : EuclideanSpace ℝ (Fin n) → ℝ)) (m a : ℝ)
    (hm : m = ∫ x, (F : EuclideanSpace ℝ (Fin n) → ℝ) x ∂(GaussMeasure n)) (ha : m < a)
    (u₁ u₂ : Lp ℝ 2 (GaussMeasure n))
    (h₁dom : u₁ ∈ FracPowDomain ((1 : ℝ) / 2))
    (h₂dom : u₂ ∈ FracPowDomain ((1 : ℝ) / 2))
    (g₁ g₂ : Lp ℝ 2 (GaussMeasure n))
    (h₁nn : 0 ≤ᵐ[GaussMeasure n] (u₁ : EuclideanSpace ℝ (Fin n) → ℝ))
    (h₂nn : 0 ≤ᵐ[GaussMeasure n] (u₂ : EuclideanSpace ℝ (Fin n) → ℝ))
    (h₁eq : F = g₁ + FracPow ((1 : ℝ) / 2) u₁)
    (h₂eq : F = g₂ + FracPow ((1 : ℝ) / 2) u₂)
    (h₁le : ∀ᵐ x ∂(GaussMeasure n), (g₁ : EuclideanSpace ℝ (Fin n) → ℝ) x ≤ a)
    (h₂le : ∀ᵐ x ∂(GaussMeasure n), (g₂ : EuclideanSpace ℝ (Fin n) → ℝ) x ≤ a)
    (h₁ct : ∀ᵐ x ∂(GaussMeasure n), 0 < (u₁ : EuclideanSpace ℝ (Fin n) → ℝ) x
        → (g₁ : EuclideanSpace ℝ (Fin n) → ℝ) x = a)
    (h₂ct : ∀ᵐ x ∂(GaussMeasure n), 0 < (u₂ : EuclideanSpace ℝ (Fin n) → ℝ) x
        → (g₂ : EuclideanSpace ℝ (Fin n) → ℝ) x = a) :
    u₁ = u₂ ∧ g₁ = g₂ := by
  classical
  obtain ⟨hmix, hdiag, hbil, hsub⟩ := EnergyFormBilinear (n := n)
  have hsym : ∀ z z' : Lp ℝ 2 (GaussMeasure n), Energy z ≠ ⊤ → Energy z' ≠ ⊤ →
      EnergyBil z z' = EnergyBil z' z := fun z z' hz hz' => (hbil z z z' 0 hz hz hz').2.2
  -- the constant `a · 1` as an `L²` element: `γₙ` is a probability measure
  obtain ⟨A, hA⟩ : ∃ A : Lp ℝ 2 (GaussMeasure n),
      (A : EuclideanSpace ℝ (Fin n) → ℝ) =ᵐ[GaussMeasure n] fun _ => a :=
    ⟨MemLp.toLp (fun _ => a) (memLp_const a), MemLp.coeFn_toLp (memLp_const a)⟩
  -- the linear part of `J` is the inner product against `a·1 - F`
  have hlin : ∀ z : Lp ℝ 2 (GaussMeasure n),
      ∫ x, (a - (F : EuclideanSpace ℝ (Fin n) → ℝ) x)
          * (z : EuclideanSpace ℝ (Fin n) → ℝ) x ∂(GaussMeasure n)
        = inner ℝ (A - F) z := by
    intro z
    rw [L2InnerGaussIntegral (A - F) z]
    refine integral_congr_ae ?_
    filter_upwards [Lp.coeFn_sub A F, hA] with x e1 e2
    rw [e1, Pi.sub_apply, e2]
  have hJ : ∀ z : Lp ℝ 2 (GaussMeasure n),
      ObstacleFunctional F a z = (Energy z).toReal / 2 + inner ℝ (A - F) z := by
    intro z
    rw [ObstacleFunctional, hlin z]
  -- Steps 1-6, stated once for a generic admissible pair and applied at both indices
  have key : ∀ (u g : Lp ℝ 2 (GaussMeasure n)), u ∈ FracPowDomain ((1 : ℝ) / 2) →
      0 ≤ᵐ[GaussMeasure n] (u : EuclideanSpace ℝ (Fin n) → ℝ) →
      F = g + FracPow ((1 : ℝ) / 2) u →
      (∀ᵐ x ∂(GaussMeasure n), (g : EuclideanSpace ℝ (Fin n) → ℝ) x ≤ a) →
      (∀ᵐ x ∂(GaussMeasure n), 0 < (u : EuclideanSpace ℝ (Fin n) → ℝ) x
          → (g : EuclideanSpace ℝ (Fin n) → ℝ) x = a) →
      u ∈ ObstacleCone n ∧
        ∀ v ∈ ObstacleCone n, ObstacleFunctional F a u ≤ ObstacleFunctional F a v := by
    intro u g hdom hnn heq hle hct
    -- Step 1: `u ∈ K`
    have hEu : Energy u ≠ ⊤ := EnergyFiniteOfSqrtDomain u hdom
    have huK : u ∈ ObstacleCone n := ⟨hEu, hnn⟩
    refine ⟨huK, ?_⟩
    -- Step 3: `B u = F - g`
    have hBu : FracPow ((1 : ℝ) / 2) u = F - g := by rw [heq]; abel
    -- Step 2: `η = a·1 - g` is nonnegative a.e. and kills `u`
    have hηu : inner ℝ (A - g) u = 0 := by
      rw [L2InnerGaussIntegral (A - g) u]
      refine integral_eq_zero_of_ae ?_
      filter_upwards [Lp.coeFn_sub A g, hA, hnn, hct] with x e1 e2 e3 e5
      have h3 : (0 : ℝ) ≤ (u : EuclideanSpace ℝ (Fin n) → ℝ) x := e3
      show ((A - g : Lp ℝ 2 (GaussMeasure n)) : EuclideanSpace ℝ (Fin n) → ℝ) x
        * (u : EuclideanSpace ℝ (Fin n) → ℝ) x = 0
      rw [e1, Pi.sub_apply, e2]
      rcases eq_or_lt_of_le h3 with h0 | h0
      · rw [← h0]; ring
      · rw [e5 h0]; ring
    intro v hv
    obtain ⟨hEv, hvnn⟩ := hv
    -- the increment `w = v - u`, taken opaquely with the two facts it is used through
    obtain ⟨w, hwdef, hEw⟩ : ∃ w : Lp ℝ 2 (GaussMeasure n), v = u + w ∧ Energy w ≠ ⊤ := by
      refine ⟨v - u, by abel, ?_⟩
      have hEnegu : Energy ((-1 : ℝ) • u) ≠ ⊤ := (hsub u u (-1) hEu hEu).2
      have hrw : v - u = v + (-1 : ℝ) • u := by rw [neg_one_smul, sub_eq_add_neg]
      rw [hrw]
      exact (hsub v ((-1 : ℝ) • u) 0 hEv hEnegu).1
    -- Step 4: the quadratic expansion
    have hexp : (Energy v).toReal
        = (Energy u).toReal + 2 * EnergyBil u w + (Energy w).toReal := by
      have e1 : EnergyBil u v + EnergyBil w v = EnergyBil v v := by
        rw [← (hbil u w v 0 hEu hEw hEv).1, ← hwdef]
      have e2 : EnergyBil u u + EnergyBil w u = EnergyBil u v := by
        rw [← (hbil u w u 0 hEu hEw hEu).1, ← hwdef]
        exact hsym v u hEv hEu
      have e3 : EnergyBil u w + EnergyBil w w = EnergyBil w v := by
        rw [← (hbil u w w 0 hEu hEw hEw).1, ← hwdef]
        exact hsym v w hEv hEw
      have e4 : EnergyBil w u = EnergyBil u w := hsym w u hEw hEu
      rw [← hdiag v hEv, ← hdiag u hEu, ← hdiag w hEw, ← e1, ← e2, ← e3, e4]
      ring
    -- Step 5: the variational inequality
    have hcomb : EnergyBil u w + inner ℝ (A - F) w = inner ℝ (A - g) w := by
      have hadd : (F - g) + (A - F) = A - g := by abel
      rw [EnergyBilIsOperator u w hdom, hBu, ← inner_add_left, hadd]
    have hsplit : inner ℝ (A - g) v = inner ℝ (A - g) u + inner ℝ (A - g) w := by
      rw [hwdef, inner_add_right]
    have hηv : (0 : ℝ) ≤ inner ℝ (A - g) v := by
      rw [L2InnerGaussIntegral (A - g) v]
      refine integral_nonneg_of_ae ?_
      filter_upwards [Lp.coeFn_sub A g, hA, hle, hvnn] with x e1 e2 e3 e4
      have h4 : (0 : ℝ) ≤ (v : EuclideanSpace ℝ (Fin n) → ℝ) x := e4
      show (0 : ℝ) ≤ ((A - g : Lp ℝ 2 (GaussMeasure n)) : EuclideanSpace ℝ (Fin n) → ℝ) x
        * (v : EuclideanSpace ℝ (Fin n) → ℝ) x
      rw [e1, Pi.sub_apply, e2]
      exact mul_nonneg (by linarith) h4
    have hw0 : (0 : ℝ) ≤ inner ℝ (A - g) w := by
      rw [hηu, zero_add] at hsplit
      rw [← hsplit]
      exact hηv
    -- Step 6: conclusion
    have hAFsplit : inner ℝ (A - F) v = inner ℝ (A - F) u + inner ℝ (A - F) w := by
      rw [hwdef, inner_add_right]
    have hEwnn : (0 : ℝ) ≤ (Energy w).toReal := ENNReal.toReal_nonneg
    rw [hJ u, hJ v, hexp, hAFsplit]
    linarith [hcomb, hw0, hEwnn]
  -- Step 7
  obtain ⟨hu₁K, hmin₁⟩ := key u₁ g₁ h₁dom h₁nn h₁eq h₁le h₁ct
  obtain ⟨hu₂K, hmin₂⟩ := key u₂ g₂ h₂dom h₂nn h₂eq h₂le h₂ct
  have hu : u₁ = u₂ := ObstacleMinimizerUnique F m a hm ha u₁ u₂ hu₁K hu₂K hmin₁ hmin₂
  refine ⟨hu, ?_⟩
  have hfg : g₁ + FracPow ((1 : ℝ) / 2) u₁ = g₂ + FracPow ((1 : ℝ) / 2) u₂ := by
    rw [← h₁eq, ← h₂eq]
  rw [hu] at hfg
  exact add_right_cancel hfg
