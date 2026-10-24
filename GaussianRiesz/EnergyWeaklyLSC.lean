import GaussianRiesz.Energy
open MeasureTheory
theorem EnergyWeaklyLSC {n : ℕ} (vk : ℕ → Lp ℝ 2 (GaussMeasure n))
    (v : Lp ℝ 2 (GaussMeasure n))
    (hconv : ∀ φ : Lp ℝ 2 (GaussMeasure n),
      Filter.Tendsto (fun k => inner ℝ (vk k) φ) Filter.atTop (nhds (inner ℝ v φ))) :
    Energy v ≤ Filter.liminf (fun k => Energy (vk k)) Filter.atTop := by
  classical
  -- weak convergence gives convergence of every Hermite coefficient
  have e1 : ∀ (z : Lp ℝ 2 (GaussMeasure n)) (α : Fin n → ℕ),
      (HermiteBasis n).repr z α = inner ℝ z ((HermiteBasis n) α) := by
    intro z α
    rw [HilbertBasis.repr_apply_apply, real_inner_comm]
  have hcoef : ∀ α : Fin n → ℕ, Filter.Tendsto
      (fun k => (HermiteBasis n).repr (vk k) α) Filter.atTop
      (nhds ((HermiteBasis n).repr v α)) := by
    intro α
    simpa only [e1] using hconv ((HermiteBasis n) α)
  -- the energy is the supremum of its finite partial sums
  rw [Energy, ENNReal.tsum_eq_iSup_sum]
  refine iSup_le fun S => ?_
  -- each partial sum is weakly continuous in the argument
  have hS : Filter.Tendsto
      (fun k => ∑ α ∈ S, ENNReal.ofReal
        ((MultiIndexSum (α : Fin n → ℕ) : ℝ) ^ ((1 : ℝ) / 2)
          * ((HermiteBasis n).repr (vk k) (α : Fin n → ℕ)) ^ 2)) Filter.atTop
      (nhds (∑ α ∈ S, ENNReal.ofReal
        ((MultiIndexSum (α : Fin n → ℕ) : ℝ) ^ ((1 : ℝ) / 2)
          * ((HermiteBasis n).repr v (α : Fin n → ℕ)) ^ 2))) := by
    refine tendsto_finsetSum _ fun α _ => ?_
    exact (ENNReal.continuous_ofReal.tendsto _).comp
      (Filter.Tendsto.const_mul _ ((hcoef (α : Fin n → ℕ)).pow 2))
  -- and dominated by the full energy at every index
  have hdom : ∀ k, (∑ α ∈ S, ENNReal.ofReal
      ((MultiIndexSum (α : Fin n → ℕ) : ℝ) ^ ((1 : ℝ) / 2)
        * ((HermiteBasis n).repr (vk k) (α : Fin n → ℕ)) ^ 2)) ≤ Energy (vk k) := by
    intro k
    rw [Energy]
    exact ENNReal.sum_le_tsum S
  calc (∑ α ∈ S, ENNReal.ofReal
        ((MultiIndexSum (α : Fin n → ℕ) : ℝ) ^ ((1 : ℝ) / 2)
          * ((HermiteBasis n).repr v (α : Fin n → ℕ)) ^ 2))
      = Filter.liminf (fun k => ∑ α ∈ S, ENNReal.ofReal
          ((MultiIndexSum (α : Fin n → ℕ) : ℝ) ^ ((1 : ℝ) / 2)
            * ((HermiteBasis n).repr (vk k) (α : Fin n → ℕ)) ^ 2)) Filter.atTop :=
        hS.liminf_eq.symm
    _ ≤ Filter.liminf (fun k => Energy (vk k)) Filter.atTop :=
        Filter.liminf_le_liminf (Filter.Eventually.of_forall hdom)
