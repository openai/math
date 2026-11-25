import OAI.Optimization.LinearProgramming.Lattice.LLLLoopNative

/-! Gram determinant invariants at every cursor reachable in the actual LLL execution. -/

open scoped BigOperators
open Hex.Internal

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Lattice

/-- Reflexive and transitive reachability by individual native loop passes. -/
inductive ReductionCursor.Reaches {n m : ℕ} (c : ReductionCursor n m) : ReductionCursor n m → Prop
  | refl : Reaches c c
  | step {d e} : Reaches c d → d.next = some e → Reaches c e

theorem ReductionCursor.Reaches.trans {n m : ℕ} {c d e : ReductionCursor n m}
    (h : c.Reaches d) (g : d.Reaches e) : c.Reaches e := by
  induction g with
  | refl => exact h
  | step _ hs ih => exact ih.step hs

theorem ReductionCursor.reaches_trace {n m : ℕ} (c : ReductionCursor n m) (fuel : ℕ) :
    c.Reaches (c.trace fuel).1 := by
  induction fuel generalizing c with
  | zero => exact .refl
  | succ f ih =>
    rw [ReductionCursor.trace]
    cases hn : c.next with
    | none => exact .refl
    | some d => exact ((Reaches.refl (c := c)).step hn).trans (ih d)

/-- The product of all positive-dimensional prefix Gram determinants, including
the invariant full determinant in the final slot. -/
def fullGramProduct {n m : ℕ} (s : LLLState n m) : ℕ := s.potential * s.d.get (Fin.last n)

private theorem next_storage {n m : ℕ} (c d : ReductionCursor n m) (hn : c.next = some d) :
    d.state.potential ≤ c.state.potential ∧
      d.state.d.get (Fin.last n) = c.state.d.get (Fin.last n) := by
  unfold ReductionCursor.next at hn
  split at hn <;> rename_i hk
  · have he := LLLState.sizeReduce_potential c.state c.index
    have hlast := congrArg (fun v : Vector ℕ (n+1) => v.get (Fin.last n))
      (LLLState.sizeReduce_d c.state c.index)
    dsimp only at hn
    split at hn <;> rename_i ht
    · cases hn
      exact ⟨he.le, hlast⟩
    · cases hn
      let r := c.state.sizeReduce c.index
      have hdrop := native_swapStep_potential_three_quarters r c.index c.positive hk (by
        have hneg := lt_of_not_ge ht
        rw [show (3/4 : ℚ).num = 3 by norm_num, show (3/4 : ℚ).den = 4 by norm_num] at hneg
        exact hneg)
      constructor
      · change (r.swapStep c.index).potential ≤ _
        change r.potential = _ at he
        omega
      · change (r.swapStep c.index).d.get (Fin.last n) = _
        apply Eq.trans _ hlast
        unfold LLLState.swapStep
        have hk0 : 0 < c.index := c.positive
        rw [dite_eq_left hk, dite_eq_left hk0]
        exact Vector.getElem_set_ne (Nat.lt_succ_of_lt hk) (Fin.last n).isLt (Nat.ne_of_lt hk)
  · simp at hn

/-- Validity, row independence and monotonicity of the full Gram product are
invariants of the native loop, including every intermediate cursor. -/
theorem nativeReach_invariants {n m : ℕ} {c d : ReductionCursor n m} (h : c.Reaches d)
    (hv : c.state.Valid) (hi : c.state.b.independent) :
    d.state.Valid ∧ d.state.b.independent ∧ fullGramProduct d.state ≤ fullGramProduct c.state := by
  induction h with
  | refl => exact ⟨hv, hi, le_rfl⟩
  | @step a b _ hnext ih =>
    obtain ⟨ha, hai, hp⟩ := ih
    have hb := cursor_step_rank a b hnext ha hai
    obtain ⟨hpot, hlast⟩ := next_storage a b hnext
    refine ⟨hb.1, hb.2.1, le_trans ?_ hp⟩
    unfold fullGramProduct
    rw [hlast]
    exact Nat.mul_le_mul_right _ hpot

theorem fullGramProduct_eq_prod {n m : ℕ} (s : LLLState n m) (hn : 0 < n) :
    fullGramProduct s = ∏ i : Fin n, s.d.get i.succ := by
  cases n with
  | zero => omega
  | succ n =>
    rw [Fin.prod_univ_castSucc]
    change interiorGramPotential s.d * _ = _
    rw [interiorGramPotential_eq_prod]
    rfl

private theorem gramSlot_pos {n m : ℕ} (s : LLLState n m) (hv : s.Valid)
    (hi : s.b.independent) (j : Fin (n+1)) : 0 < s.d.get j := by
  obtain ⟨t, ht⟩ := j
  rw [hv.d_eq]
  cases t with
  | zero => simp [Hex.GramSchmidt.Int.gramDet_zero]
  | succ t => exact hi ⟨t, by omega⟩

private theorem gramSlot_le_full {n m : ℕ} (s : LLLState n m) (hn : 0 < n) (hv : s.Valid)
    (hi : s.b.independent) (j : Fin (n+1)) : s.d.get j ≤ fullGramProduct s := by
  rw [fullGramProduct_eq_prod s hn]
  obtain ⟨j, hj⟩ := j
  cases j with
  | zero =>
    rw [hv.d_eq, Hex.GramSchmidt.Int.gramDet_zero]
    exact Finset.one_le_prod (fun i _ => gramSlot_pos s hv hi i.succ)
  | succ j =>
    have hjn : j < n := by omega
    exact Finset.single_le_prod (f := fun i : Fin n => s.d.get i.succ)
      (fun i _ => gramSlot_pos s hv hi i.succ) (Finset.mem_univ (⟨j,hjn⟩ : Fin n))

/-- Each stored leading determinant at any reachable cursor is bounded by the
full Gram product in the original state. -/
theorem nativeReach_gramSlot_le {n m : ℕ} {c d : ReductionCursor n m} (h : c.Reaches d)
    (hv : c.state.Valid) (hi : c.state.b.independent) (j : Fin (n+1)) :
    0 < d.state.d.get j ∧ d.state.d.get j ≤ fullGramProduct c.state := by
  obtain ⟨hd, hdi, hp⟩ := nativeReach_invariants h hv hi
  exact ⟨gramSlot_pos _ hd hdi _, (gramSlot_le_full _ (d.positive.trans d.bounded) hd hdi _).trans hp⟩

/-- The initial full product equals the integer matrix potential obtained from the input rows. -/
theorem initialFullGramProduct_eq {n m : ℕ} (b : Hex.Matrix Int n m) (hn : 1 ≤ n) :
    fullGramProduct (LLLState.ofBasis b) = reductionPotential (HexMatrixMathlib.matrixEquiv b) := by
  rw [fullGramProduct_eq_prod _ hn]
  unfold reductionPotential
  apply Finset.prod_congr rfl
  intro i _
  rw [(HexLLLMathlib.LLLState.ofBasis_valid b).d_eq]
  exact nativePrefixGram b i.succ

/-- All stored Gram determinants throughout the actual native reduction have
polynomial bit length in the input. -/
theorem nativeReach_gramSlot_size {n m L : ℕ} (b : Hex.Matrix Int n m) (hn : 1 ≤ n)
    (hi : b.independent) (hB : ∀ i j, ((HexMatrixMathlib.matrixEquiv b) i j).natAbs ≤ 2^L)
    {c : ReductionCursor n m} (h : (initialReductionCursor b hn).Reaches c) (j : Fin (n+1)) :
    (c.state.d.get j).size ≤ (n+m+2*L)*n*n+1 := by
  have hh := (nativeReach_gramSlot_le h (HexLLLMathlib.LLLState.ofBasis_valid b) hi j).2
  change c.state.d.get j ≤ fullGramProduct (LLLState.ofBasis b) at hh
  rw [initialFullGramProduct_eq b hn] at hh
  exact (Nat.size_le_size hh).trans (reductionPotential_size_le _ hB)

end Lattice
end LinearProgramming
end Optimization
end OAI
