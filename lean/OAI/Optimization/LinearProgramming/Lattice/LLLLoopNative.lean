import OAI.Optimization.LinearProgramming.Lattice.LLLSwapNative
import OAI.Optimization.LinearProgramming.Lattice.LLLStateNative
import OAI.Optimization.LinearProgramming.Lattice.LoopBudget
import OAI.Optimization.LinearProgramming.Lattice.LLLComplexity
import Mathlib.Tactic.NormNum.GCD
import HexLLLMathlib.ReductionInvariant
import HexMatrixMathlib.Gram

/-! Count the advance and swap iterations of the classical Hex integer reducer using
Kim Morrison's [reduction invariants](https://github.com/leanprover/hex-lll-theory/blob/761108380d7bdae23181785d52703b4883388da1/HexLLLMathlib/ReductionInvariant.lean)
(© 2026 Lean FRO, LLC, Apache-2.0). -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Lattice

open Hex.Internal

/-- The native state and its valid outer-loop cursor. -/
structure ReductionCursor (n m : ℕ) where
  state : LLLState n m
  index : ℕ
  positive : 1 ≤ index
  bounded : index ≤ n

private def swapNumerator {n m : ℕ} (s : LLLState n m) (k : ℕ) (hk : k < n) : ℤ :=
  (s.d.get ⟨k+1, by omega⟩ : ℤ) * (s.d.get ⟨k-1, by omega⟩ : ℤ) +
    ((s.ν.getRow ⟨k, hk⟩).get ⟨k-1, by omega⟩) ^ 2

/-- One native size-reduction pass followed by its actual integer Lovász comparison. -/
def ReductionCursor.next {n m : ℕ} (c : ReductionCursor n m) : Option (ReductionCursor n m) :=
  if hk : c.index < n then
    let s := c.state.sizeReduce c.index
    let dk : ℤ := s.d.get ⟨c.index, by omega⟩
    if (3/4 : ℚ).num * dk^2 ≤ ((3/4 : ℚ).den : ℤ) * swapNumerator s c.index hk then
      some ⟨s, c.index + 1, Nat.succ_pos _, Nat.succ_le_of_lt hk⟩
    else
      some ⟨s.swapStep c.index, max (c.index-1) 1, Nat.le_max_right ..,
        max_le (by have := c.bounded; omega) (c.positive.trans c.bounded)⟩
  else none

/-- The call to Hex from this very cursor, at the chosen fuel. -/
def ReductionCursor.nativeAt {n m : ℕ} (c : ReductionCursor n m) (fuel : ℕ) : Hex.Matrix Int n m :=
  lllLoop c.state c.index (3/4) (by norm_num) (by norm_num) c.positive c.bounded fuel

private theorem nativeAt_succ {n m : ℕ} (c : ReductionCursor n m) (fuel : ℕ) :
    c.nativeAt (fuel+1) = match c.next with
      | none => c.state.b
      | some d => d.nativeAt fuel := by
  obtain ⟨s, k, hpos, hkn⟩ := c
  by_cases hdone : k = n
  · subst k
    simp [ReductionCursor.nativeAt, ReductionCursor.next, lllLoop]
  · have hk : k < n := lt_of_le_of_ne hkn hdone
    dsimp only [ReductionCursor.nativeAt, ReductionCursor.next]
    rw [lllLoop, dite_eq_right hdone, dite_eq_left hk]
    let t : Prop := (3/4 : ℚ).num * ((s.sizeReduce k).d.get ⟨k, by omega⟩ : ℤ)^2 ≤
      ((3/4 : ℚ).den : ℤ) * swapNumerator (s.sizeReduce k) k hk
    let ca : ReductionCursor n m := ⟨s.sizeReduce k, k+1, by omega, by omega⟩
    let cb : ReductionCursor n m := ⟨(s.sizeReduce k).swapStep k, max (k-1) 1, by omega, by omega⟩
    let result (o : Option (ReductionCursor n m)) := match o with
      | none => s.b
      | some d => d.nativeAt fuel
    change (if t then ca.nativeAt fuel else cb.nativeAt fuel) = result (if t then some ca else some cb)
    by_cases h : t <;> simp [h, result]

/-- The executable cursor trace reports the final state and the precise number of
size-reduction passes, stopping as soon as the native cursor reaches the row count. -/
def ReductionCursor.trace {n m : ℕ} (fuel : ℕ) (c : ReductionCursor n m) :
    ReductionCursor n m × ℕ :=
  match fuel with
  | 0 => (c, 0)
  | f+1 => match c.next with
    | none => (c, 0)
    | some d => let t := d.trace f; (t.1, t.2+1)

theorem reductionTrace_native {n m : ℕ} (c : ReductionCursor n m) (fuel : ℕ) :
    (c.trace fuel).1.state.b = c.nativeAt fuel := by
  induction fuel generalizing c with
  | zero => rfl
  | succ f ih =>
    rw [nativeAt_succ, ReductionCursor.trace]
    cases hn : c.next with
    | none => rfl
    | some d => exact ih d

private theorem foldl_positive {n : ℕ} (f : Fin n → ℕ) (hf : ∀ i, 0 < f i)
    (a : ℕ) (ha : 0 < a) : 0 < Fin.foldl n (fun b i => b*f i) a := by
  induction n generalizing a with
  | zero => simpa using ha
  | succ n ih =>
    rw [Fin.foldl_succ]
    exact ih _ (fun i => hf i.succ) _ (Nat.mul_pos ha (hf 0))

theorem validPotential_pos {n m : ℕ} (s : LLLState n m) (hv : s.Valid)
    (hi : s.b.independent) : 0 < s.potential := by
  unfold LLLState.potential
  apply foldl_positive _ _ _ (by decide)
  intro i
  rw [hv.d_eq]
  exact hi ⟨i.val, (Nat.lt_of_lt_of_le i.isLt (Nat.sub_le n 1))⟩

theorem cursor_step_rank {n m : ℕ} (c d : ReductionCursor n m) (hn : c.next = some d)
    (hc : c.state.Valid) (hi : c.state.b.independent) :
    d.state.Valid ∧ d.state.b.independent ∧
      indexedReductionRank n d.state.potential d.index <
        indexedReductionRank n c.state.potential c.index := by
  unfold ReductionCursor.next at hn
  split at hn <;> rename_i hlt
  · have hr := Hex.Internal.LLLState.sizeReduce_valid c.state c.index hc
    have hri := Hex.Internal.LLLState.sizeReduce_independent c.state c.index hi hc hr
    have he := Hex.Internal.LLLState.sizeReduce_potential c.state c.index
    dsimp only at hn
    split at hn <;> rename_i ht
    · cases hn
      refine ⟨hr, hri, ?_⟩
      dsimp only
      rw [he]
      exact indexedReductionRank_advance hlt
    · cases hn
      let r := c.state.sizeReduce c.index
      have hv := native_swap_preserves_valid r c.index hri hr
      have hi' := Hex.Internal.LLLState.swapStep_independent r c.index hri hr c.positive hlt
      refine ⟨hv, hi', ?_⟩
      dsimp only
      apply indexedReductionRank_swap (validPotential_pos _ hv hi') _ (Nat.le_max_left ..)
      rw [← he]
      have hfail := lt_of_not_ge ht
      rw [show (3/4 : ℚ).num = 3 by norm_num, show (3/4 : ℚ).den = 4 by norm_num] at hfail
      exact native_swapStep_potential_three_quarters r c.index c.positive hlt hfail
  · simp at hn

/-- This counts iterations in the native trace for every supplied fuel, including
Hex's own possibly large fuel. A fuel at least the initial rank reaches the halting cursor. -/
theorem reductionTrace_bound {n m : ℕ} (c : ReductionCursor n m) (fuel : ℕ)
    (hv : c.state.Valid) (hi : c.state.b.independent) :
    (c.trace fuel).2 ≤ indexedReductionRank n c.state.potential c.index ∧
      (indexedReductionRank n c.state.potential c.index ≤ fuel → (c.trace fuel).1.next = none) := by
  induction fuel generalizing c with
  | zero =>
    refine ⟨Nat.zero_le _, ?_⟩
    intro h
    cases hd : c.next with
    | none => exact hd
    | some d =>
      have := (cursor_step_rank c d hd hv hi).2.2
      omega
  | succ f ih =>
    rw [ReductionCursor.trace]
    cases hd : c.next with
    | none => exact ⟨Nat.zero_le _, fun _ => hd⟩
    | some d =>
      obtain ⟨hdv, hdi, hlt⟩ := cursor_step_rank c d hd hv hi
      obtain ⟨hb, ht⟩ := ih d hdv hdi
      exact ⟨by dsimp; omega, fun hf => ht (by omega)⟩


theorem nativePrefixGram {n m : ℕ} (b : Hex.Matrix Int n m) (j : Fin (n+1)) :
    Hex.GramSchmidt.Int.gramDet b j.val (Nat.le_of_lt_succ j.isLt) =
      prefixGramMagnitude (HexMatrixMathlib.matrixEquiv b) j := by
  let h := Nat.le_of_lt_succ j.isLt
  have he := Hex.GramSchmidt.Int.leadingGramMatrixInt_det_eq_gramDet_int b j.val h
  rw [Hex.GramSchmidt.leadingGramMatrixInt_eq_principalSubmatrix_gram] at he
  have hmatrix := HexMatrixMathlib.det_principalSubmatrix_eq_submatrix_det b.gramMatrix j.val h
  rw [HexMatrixMathlib.matrixEquiv_gramMatrix] at hmatrix
  have he' := congrArg Int.natAbs (hmatrix.symm.trans he)
  let B := HexMatrixMathlib.matrixEquiv b
  let f := Fin.castLE h
  have hrows : (B * B.transpose).submatrix f f = (B.submatrix f id) * (B.submatrix f id).transpose := by
    ext i l
    rfl
  exact he'.symm.trans (congrArg (fun M => M.det.natAbs) hrows)

private theorem foldl_mul_bounded {k C : ℕ} (f : Fin k → ℕ) (hf : ∀ i, f i ≤ C)
    (a : ℕ) : Fin.foldl k (fun acc i => acc * f i) a ≤ a * C ^ k := by
  induction k generalizing a with
  | zero => simp
  | succ k ih =>
    rw [Fin.foldl_succ, Nat.pow_succ']
    calc
      _ ≤ a * f 0 * C ^ k := ih _ (fun i => hf i.succ) _
      _ ≤ (a*C) * C^k := Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (hf 0))
      _ = _ := by ring

theorem nativeInitialPotential_le {n m L : ℕ} (b : Hex.Matrix Int n m)
    (hB : ∀ i j, ((HexMatrixMathlib.matrixEquiv b) i j).natAbs ≤ 2^L) :
    (LLLState.ofBasis b).potential ≤ 2 ^ ((n+m+2*L)*n*n) := by
  let a := (n+m+2*L)*n
  have hv := HexLLLMathlib.LLLState.ofBasis_valid b
  unfold LLLState.potential
  calc
    _ ≤ 1 * (2^a)^(n-1) := by
      apply foldl_mul_bounded
      intro i
      let j : Fin (n+1) := ⟨i.val + 1, by have := i.isLt; omega⟩
      rw [hv.d_eq]
      exact (nativePrefixGram b j).le.trans (prefixGramMagnitude_le _ hB j)
    _ ≤ 2 ^ (a*n) := by
      rw [Nat.one_mul, ← pow_mul]
      exact Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_left _ (Nat.sub_le ..))

/-- The native public reduction starts at the first adjacent pair. -/
def initialReductionCursor {n m : ℕ} (b : Hex.Matrix Int n m) (hn : 1 ≤ n) : ReductionCursor n m :=
  ⟨LLLState.ofBasis b, 1, by decide, hn⟩

/-- The counted trace of the public native reducer, using its actual fuel and input matrix. -/
def nativeReductionTrace {n m : ℕ} (b : Hex.Matrix Int n m) (hn : 1 ≤ n) :
    ReductionCursor n m × ℕ :=
  (initialReductionCursor b hn).trace (lllFuel (LLLState.ofBasis b))

theorem nativeReductionTrace_result {n m : ℕ} (b : Hex.Matrix Int n m) (hn : 1 ≤ n) :
    (nativeReductionTrace b hn).1.state.b = Hex.lllNative b (3/4) (hn := hn) :=
  reductionTrace_native (initialReductionCursor b hn) _

/-- A polynomial in the row count, coordinate count, and input coefficient bit length
bounds every size-reduction pass of the actual public integer algorithm. -/
theorem nativeReductionTrace_count {n m L : ℕ} (b : Hex.Matrix Int n m) (hn : 1 ≤ n)
    (hI : b.independent) (hB : ∀ i j, ((HexMatrixMathlib.matrixEquiv b) i j).natAbs ≤ 2^L) :
    (nativeReductionTrace b hn).2 ≤ 2 * (3*((n+m+2*L)*n*n) + 1) + n := by
  let P := (LLLState.ofBasis b).potential
  let L' := (n+m+2*L)*n*n
  have hP : P ≤ 2^L' := nativeInitialPotential_le b hB
  have hcube : P^3 ≤ 2^(3*L') := by
    calc
      _ ≤ (2^L')^3 := Nat.pow_le_pow_left hP _
      _ = _ := by rw [← pow_mul, Nat.mul_comm L' 3]
  have hs := Nat.size_le_size hcube
  rw [Nat.size_pow] at hs
  have ht := (reductionTrace_bound (initialReductionCursor b hn) (lllFuel (LLLState.ofBasis b))
    (HexLLLMathlib.LLLState.ofBasis_valid b) hI).1
  change (nativeReductionTrace b hn).2 ≤ 2*(P^3).size+(n-1) at ht
  change _ ≤ 2*(3*L'+1)+n
  omega

end Lattice
end LinearProgramming
end Optimization
end OAI
