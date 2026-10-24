import GaussianRiesz.LebesgueDilation
import GaussianRiesz.LocalMaximalFunction
import Mathlib.MeasureTheory.Covering.Vitali
open MeasureTheory Metric
open scoped ENNReal
theorem LocalMaximalWeakType {n : ℕ} (w : EuclideanSpace ℝ (Fin n) → ℝ)
    (hw : AEMeasurable w volume) (t : ℝ≥0∞) (ht : t ≠ 0) :
    volume {x : EuclideanSpace ℝ (Fin n) | t < LocalMaximalFunction w x}
      ≤ 4 ^ n * (∫⁻ y, ‖w y‖ₑ) / t := by
  classical
  -- STEP 2, first half: at `t = ⊤` the level set is empty
  rcases eq_or_ne t ⊤ with rfl | htop
  · have hempty : {x : EuclideanSpace ℝ (Fin n)
        | (⊤ : ℝ≥0∞) < LocalMaximalFunction w x} = ∅ := by
      ext x
      simp
    rw [hempty]
    simp
  set S : Set (EuclideanSpace ℝ (Fin n)) := {x | t < LocalMaximalFunction w x} with hSdef
  -- STEP 1: closed balls have positive finite volume, and the `4^n` dilation rule.
  -- Both hold for every `n : ℕ`, `n = 0` included (pm-0015): the `closedBall` forms of
  -- the Haar scaling lemmas carry no `Nontrivial` hypothesis, so there is no case split.
  have hpos : ∀ (x : EuclideanSpace ℝ (Fin n)) {r : ℝ}, 0 < r →
      volume (closedBall x r) ≠ 0 := fun x _ hr => (measure_closedBall_pos volume x hr).ne'
  have hfinball : ∀ (x : EuclideanSpace ℝ (Fin n)) (r : ℝ),
      volume (closedBall x r) ≠ ⊤ := fun _ _ => measure_closedBall_lt_top.ne
  have hdil : ∀ (b : EuclideanSpace ℝ (Fin n)) {r : ℝ}, 0 ≤ r →
      volume (closedBall b (4 * r)) = 4 ^ n * volume (closedBall b r) := by
    intro b r hr
    rw [Measure.addHaar_closedBall_mul volume b (by norm_num : (0 : ℝ) ≤ 4) hr,
      Measure.addHaar_closedBall_center volume b, finrank_euclideanSpace_fin]
    congr 1
    rw [ENNReal.ofReal_pow (by norm_num : (0 : ℝ) ≤ 4)]
    norm_num
  -- STEP 2, second half: select a radius in `(0,2]` at each point of the level set
  have hchoice : ∀ x ∈ S, ∃ r : ℝ, r ∈ Set.Ioc (0 : ℝ) 2 ∧
      t < (volume (closedBall x r))⁻¹ * ∫⁻ y in closedBall x r, ‖w y‖ₑ := by
    intro x hx
    have hx' : t < LocalMaximalFunction w x := hx
    rw [LocalMaximalFunction] at hx'
    simpa only [lt_iSup_iff, exists_prop] using hx'
  choose! ρ hρmem hρlt using hchoice
  -- each selected ball is controlled by its own mass
  have hball : ∀ x ∈ S, volume (closedBall x (ρ x))
      ≤ (∫⁻ y in closedBall x (ρ x), ‖w y‖ₑ) / t := by
    intro x hx
    refine (ENNReal.le_div_iff_mul_le (Or.inl ht) (Or.inl htop)).mpr ?_
    calc volume (closedBall x (ρ x)) * t
        ≤ volume (closedBall x (ρ x))
            * ((volume (closedBall x (ρ x)))⁻¹ * ∫⁻ y in closedBall x (ρ x), ‖w y‖ₑ) :=
          mul_le_mul' le_rfl (hρlt x hx).le
      _ = ∫⁻ y in closedBall x (ρ x), ‖w y‖ₑ := by
          rw [← mul_assoc,
            ENNReal.mul_inv_cancel (hpos x (hρmem x hx).1) (hfinball x (ρ x)), one_mul]
  -- STEP 3: Vitali at `τ = 4`.  The uniform radius bound `2` is exactly
  -- `LocalMaximalFunction`'s cap, which is what makes the wrapper applicable.
  obtain ⟨U, hUsub, hUdisj, hUcov⟩ :=
    Vitali.exists_disjoint_subfamily_covering_enlargement_closedBall S (fun x => x) ρ 2
      (fun a ha => (hρmem a ha).2) 4 (by norm_num)
  have hdisj : Pairwise (Function.onFun Disjoint
      (fun b : ↥U => closedBall (b : EuclideanSpace ℝ (Fin n)) (ρ b))) :=
    fun b c hbc => hUdisj b.2 c.2 fun h => hbc (Subtype.ext h)
  -- STEP 4: the selected subfamily is countable
  have hUcount : U.Countable := by
    have hc := Measure.countable_meas_pos_of_disjoint_iUnion
      (μ := (volume : Measure (EuclideanSpace ℝ (Fin n))))
      (As := fun b : ↥U => closedBall (b : EuclideanSpace ℝ (Fin n)) (ρ b))
      (fun _ => measurableSet_closedBall) hdisj
    have heq : {b : ↥U | 0 < volume (closedBall (b : EuclideanSpace ℝ (Fin n)) (ρ b))}
        = Set.univ := by
      ext b
      simp only [Set.mem_ofPred_eq, Set.mem_univ, iff_true]
      exact measure_closedBall_pos volume _ (hρmem _ (hUsub b.2)).1
    rw [heq] at hc
    exact Set.countable_coe_iff.mp (Set.countable_univ_iff.mp hc)
  have : Countable ↥U := hUcount.to_subtype
  -- STEP 5: summation.  Only monotonicity and countable subadditivity of the outer
  -- measure are used on `S`; no measurability of the level set is needed.
  have hcover : S ⊆ ⋃ b : ↥U, closedBall (b : EuclideanSpace ℝ (Fin n)) (4 * ρ b) := by
    intro x hx
    obtain ⟨b, hbU, hsub⟩ := hUcov x hx
    exact Set.mem_iUnion.mpr ⟨⟨b, hbU⟩, hsub (mem_closedBall_self (hρmem x hx).1.le)⟩
  calc volume S
      ≤ volume (⋃ b : ↥U, closedBall (b : EuclideanSpace ℝ (Fin n)) (4 * ρ b)) :=
        measure_mono hcover
    _ ≤ ∑' b : ↥U, volume (closedBall (b : EuclideanSpace ℝ (Fin n)) (4 * ρ b)) :=
        measure_iUnion_le _
    _ = ∑' b : ↥U, 4 ^ n * volume (closedBall (b : EuclideanSpace ℝ (Fin n)) (ρ b)) :=
        tsum_congr fun b => hdil _ (hρmem _ (hUsub b.2)).1.le
    _ = 4 ^ n * ∑' b : ↥U, volume (closedBall (b : EuclideanSpace ℝ (Fin n)) (ρ b)) :=
        ENNReal.tsum_mul_left
    _ ≤ 4 ^ n * ∑' b : ↥U,
          ((∫⁻ y in closedBall (b : EuclideanSpace ℝ (Fin n)) (ρ b), ‖w y‖ₑ) / t) :=
        mul_le_mul' le_rfl (ENNReal.tsum_le_tsum fun b => hball _ (hUsub b.2))
    _ = 4 ^ n * ((∑' b : ↥U,
          ∫⁻ y in closedBall (b : EuclideanSpace ℝ (Fin n)) (ρ b), ‖w y‖ₑ) / t) := by
        simp only [div_eq_mul_inv]
        rw [ENNReal.tsum_mul_right]
    _ = 4 ^ n * ((∫⁻ y in ⋃ b : ↥U, closedBall (b : EuclideanSpace ℝ (Fin n)) (ρ b),
          ‖w y‖ₑ) / t) := by
        rw [lintegral_iUnion (fun _ => measurableSet_closedBall) hdisj]
    _ ≤ 4 ^ n * ((∫⁻ y, ‖w y‖ₑ) / t) := by
        gcongr
        exact Measure.restrict_le_self
    _ = 4 ^ n * (∫⁻ y, ‖w y‖ₑ) / t := (mul_div_assoc _ _ _).symm
