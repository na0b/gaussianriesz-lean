import GaussianRiesz.HermiteFun
import GaussianRiesz.HermiteDerivative
import GaussianRiesz.Hermite1Zero
import GaussianRiesz.HermiteFunContDiff
theorem HermiteFunDeriv {n : ℕ} (α : Fin n → ℕ) (j : Fin n) (x : EuclideanSpace ℝ (Fin n)) :
    DifferentiableAt ℝ (HermiteFun α) x
      ∧ fderiv ℝ (HermiteFun α) x (EuclideanSpace.single j 1)
          = Real.sqrt 2 * Real.sqrt (α j) * HermiteFun (Function.update α j (α j - 1)) x := by
  -- (0) differentiating `aeval` in the evaluation point
  have hd : ∀ (p : Polynomial ℤ) (y : ℝ),
      HasDerivAt (fun z : ℝ => Polynomial.aeval z p)
        (Polynomial.aeval y (Polynomial.derivative p)) y :=
    fun p y => p.hasDerivAt_aeval y
  -- (1) the one-variable identity `h_k' = √2 √k h_{k-1}`
  have h1d : ∀ (k : ℕ) (s : ℝ),
      HasDerivAt (Hermite1 k) (Real.sqrt 2 * Real.sqrt k * Hermite1 (k - 1) s) s := by
    intro k s
    cases k with
    | zero =>
        have hfn : Hermite1 0 = fun _ : ℝ => (1:ℝ) := funext Hermite1Zero
        rw [hfn]
        simpa using hasDerivAt_const s (1:ℝ)
    | succ m =>
        have hin : HasDerivAt (fun s : ℝ => Real.sqrt 2 * s) (Real.sqrt 2) s := by
          simpa using (hasDerivAt_id s).const_mul (Real.sqrt 2)
        have hcomp : HasDerivAt
            (fun s : ℝ => Polynomial.aeval (Real.sqrt 2 * s) (Polynomial.hermite (m+1)))
            (Polynomial.aeval (Real.sqrt 2 * s)
              (Polynomial.derivative (Polynomial.hermite (m+1))) * Real.sqrt 2) s :=
          (hd _ (Real.sqrt 2 * s)).comp s hin
        have hdiv := hcomp.div_const (Real.sqrt (Nat.factorial (m+1)))
        have hfn : Hermite1 (m+1)
            = fun s : ℝ => Polynomial.aeval (Real.sqrt 2 * s) (Polynomial.hermite (m+1))
                / Real.sqrt (Nat.factorial (m+1)) := rfl
        rw [hfn]
        refine hdiv.congr_deriv ?_
        rw [HermiteDerivative m]
        simp only [Hermite1, Nat.add_sub_cancel, nsmul_eq_mul, map_mul, map_natCast]
        have e2 : Real.sqrt ((Nat.factorial (m+1) : ℝ))
            = Real.sqrt ((m:ℝ)+1) * Real.sqrt ((Nat.factorial m : ℝ)) := by
          rw [← Real.sqrt_mul (by positivity)]
          congr 1
          rw [Nat.factorial_succ m]
          push_cast
          ring
        have hs : Real.sqrt ((m:ℝ)+1) * Real.sqrt ((m:ℝ)+1) = (m:ℝ)+1 :=
          Real.mul_self_sqrt (by positivity)
        push_cast
        rw [e2]
        field_simp
        linear_combination
          (-(Polynomial.aeval (Real.sqrt 2 * s) (Polynomial.hermite m))) * hs
  -- (2) differentiability at `x`, from smoothness
  have hdiffAt : DifferentiableAt ℝ (HermiteFun α) x :=
    ((HermiteFunContDiff α).differentiable (by norm_num)) x
  refine ⟨hdiffAt, ?_⟩
  -- (3) read the directional derivative off the line through `x` in direction `e_j`
  have hg : HasDerivAt (fun t : ℝ => x + t • EuclideanSpace.single j (1:ℝ))
      (EuclideanSpace.single j (1:ℝ)) 0 := by
    simpa using
      ((hasDerivAt_id (0:ℝ)).smul_const (EuclideanSpace.single j (1:ℝ))).const_add x
  have hfd : HasFDerivAt (HermiteFun α) (fderiv ℝ (HermiteFun α) x)
      ((fun t : ℝ => x + t • EuclideanSpace.single j (1:ℝ)) 0) := by
    simpa using hdiffAt.hasFDerivAt
  have hline := hfd.comp_hasDerivAt (0:ℝ) hg
  -- (4) only the `j`-th factor moves along that line
  have hrep : (HermiteFun α ∘ (fun t : ℝ => x + t • EuclideanSpace.single j (1:ℝ)))
      = fun t : ℝ => Hermite1 (α j) (x j + t)
          * ∏ i ∈ Finset.univ.erase j, Hermite1 (α i) (x i) := by
    funext t
    simp only [Function.comp_apply, HermiteFun]
    rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ j)]
    congr 1
    · congr 1
      simp
    · refine Finset.prod_congr rfl fun i hi => ?_
      congr 1
      simp [Finset.ne_of_mem_erase hi]
  rw [hrep] at hline
  have hinner : HasDerivAt (fun t : ℝ => Hermite1 (α j) (x j + t))
      (Real.sqrt 2 * Real.sqrt (α j) * Hermite1 (α j - 1) (x j)) 0 := by
    have hid : HasDerivAt (fun t : ℝ => x j + t) 1 (0:ℝ) := by
      simpa using (hasDerivAt_id (0:ℝ)).const_add (x j)
    have hb : HasDerivAt (Hermite1 (α j))
        (Real.sqrt 2 * Real.sqrt (α j) * Hermite1 (α j - 1) (x j)) (x j + 0) := by
      simpa using h1d (α j) (x j)
    have hcc : HasDerivAt (fun t : ℝ => Hermite1 (α j) (x j + t))
        (Real.sqrt 2 * Real.sqrt (α j) * Hermite1 (α j - 1) (x j) * 1) 0 :=
      hb.comp (0:ℝ) hid
    simpa using hcc
  have hcomp2 := hinner.mul_const (∏ i ∈ Finset.univ.erase j, Hermite1 (α i) (x i))
  have huniq := hcomp2.unique hline
  rw [← huniq]
  -- (5) reassemble the shifted multi-index
  have hsplit : HermiteFun (Function.update α j (α j - 1)) x
      = Hermite1 (α j - 1) (x j) * ∏ i ∈ Finset.univ.erase j, Hermite1 (α i) (x i) := by
    rw [HermiteFun, ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ j),
      Function.update_self]
    congr 1
    refine Finset.prod_congr rfl fun i hi => ?_
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hi)]
  rw [hsplit]
  ring
