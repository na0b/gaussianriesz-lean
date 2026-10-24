import GaussianRiesz.Energy
import GaussianRiesz.HermiteBasis
import GaussianRiesz.HermiteL2
import GaussianRiesz.HermiteL2Orthonormal
import GaussianRiesz.HermiteL2Complete
import GaussianRiesz.MultiIndexSum
open MeasureTheory
theorem HermiteBasisVectorFacts (n : ℕ) :
    (∀ β : Fin n → ℕ, (HermiteBasis n) β = HermiteL2 β)
      ∧ (∀ β α : Fin n → ℕ,
          (HermiteBasis n).repr (HermiteL2 β) α = if α = β then 1 else 0)
      ∧ (∀ β : Fin n → ℕ, Energy (HermiteL2 β) ≠ ⊤) := by
  -- the Hermite basis vectors are exactly the `HermiteL2` elements
  have hbasis : ∀ β : Fin n → ℕ, (HermiteBasis n) β = HermiteL2 β := by
    intro β
    rw [HermiteBasis]
    exact congrFun (HilbertBasis.coe_mk (HermiteL2Orthonormal n) (HermiteL2Complete n)) β
  have hreprh : ∀ β α : Fin n → ℕ,
      (HermiteBasis n).repr (HermiteL2 β) α = if α = β then 1 else 0 := by
    intro β α
    rw [← hbasis β, HilbertBasis.repr_self, lp.single_apply]
    simp [Pi.single_apply]
  -- STEP (b1): every `h_β` is an admissible test function
  have hhE : ∀ β : Fin n → ℕ, Energy (HermiteL2 β) ≠ ⊤ := by
    intro β
    have hz : ∀ x : {α : Fin n → ℕ // α ≠ 0}, (x : Fin n → ℕ) ≠ β →
        ENNReal.ofReal ((MultiIndexSum (x : Fin n → ℕ) : ℝ) ^ ((1 : ℝ) / 2)
          * ((HermiteBasis n).repr (HermiteL2 β) (x : Fin n → ℕ)) ^ 2) = 0 := by
      intro x hx
      rw [hreprh β (x : Fin n → ℕ), if_neg hx]
      simp
    by_cases hβ : β = 0
    · rw [Energy, tsum_congr fun x => hz x (by rw [hβ]; exact x.2), tsum_zero]
      exact ENNReal.zero_ne_top
    · rw [Energy, tsum_eq_single (⟨β, hβ⟩ : {α : Fin n → ℕ // α ≠ 0})
        fun x hx => hz x fun hcon => hx (Subtype.ext hcon)]
      exact ENNReal.ofReal_ne_top
  exact ⟨hbasis, hreprh, hhE⟩
