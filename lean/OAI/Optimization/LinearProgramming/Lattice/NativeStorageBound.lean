import OAI.Optimization.LinearProgramming.Lattice.NativeInnerBits
import OAI.Optimization.LinearProgramming.Lattice.NativeReachHeight
import OAI.Optimization.LinearProgramming.Lattice.BitInitCorrespondence
import OAI.Optimization.LinearProgramming.Lattice.LLLSwapCost

/-! One polynomial bounds every serialized entry of the native LLL controller,
at all outer boundaries and at all partially completed size-reduction passes. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Lattice

open Hex.Internal Hex.GramSchmidtMathlib

theorem nativeReach_upper_frame {n m : ℕ} {c d : ReductionCursor n m} (h : c.Reaches d)
    (i j : Fin n) (hij : i ≤ j) :
    (d.state.ν.getRow i).get j = (c.state.ν.getRow i).get j := by
  induction h with
  | refl => rfl
  | @step d e _ hn ih =>
    apply Eq.trans _ ih
    unfold ReductionCursor.next at hn
    split at hn <;> rename_i hk
    · let r := d.state.sizeReduce d.index
      have hr : (r.ν.getRow i).get j = (d.state.ν.getRow i).get j :=
        native_sizeReduce_upper_frame d.state ⟨d.index,hk⟩ i j hij
      dsimp only at hn
      split at hn
      · cases hn
        exact hr
      · cases hn
        exact (native_swap_upper_frame r d.index i j hij).trans hr
    · simp at hn

def nativePassH (n m L : ℕ) : ℕ := m+1+nativeRowBitBound n m L+1

def nativePassB (n m L : ℕ) : ℕ := (2*nativePassH n m L+2)*n+nativePassH n m L

def nativePassWidth (n m L : ℕ) : ℕ :=
  (n+m+2*nativePassB n m L)*n + ((n+m+2*L)*n+1) +
    nativePassB n m L + nativePassH n m L + n+m+1

theorem nativePassWidth_mono {n m L n' m' L' : ℕ} (hn : n ≤ n') (hm : m ≤ m')
    (hL : L ≤ L') : nativePassWidth n m L ≤ nativePassWidth n' m' L' := by
  unfold nativePassWidth nativePassB nativePassH nativeRowBitBound
  gcongr

private theorem nativeRow_norm_pow {n m C : ℕ} (b : Hex.Matrix ℤ n m)
    (hb : ∀ i j, ((HexMatrixMathlib.matrixEquiv b) i j).natAbs ≤ 2^C) (i : Fin n) :
    ‖intRowFamily b i‖ + 1 ≤ (2:ℝ)^(m+1+C+1) := by
  have hs : ‖intRowFamily b i‖ ≤ (((m+1)*2^C : ℕ):ℝ) := by
    rw [hexRow_real]
    have hh := integerRow_norm_sq_bound (HexMatrixMathlib.matrixEquiv b i) (hb i)
    apply le_of_sq_le_sq _ (by positivity)
    apply hh.trans
    push_cast
    rw [mul_pow]
    exact mul_le_mul_of_nonneg_right (by nlinarith [sq_nonneg (m:ℝ)]) (by positivity)
  have hb' : (m+1)*2^C ≤ 2^(m+1+C) := by
    rw [pow_add]
    exact Nat.mul_le_mul_right _ Nat.lt_two_pow_self.le
  have hreal : (((m+1)*2^C : ℕ):ℝ) ≤ (2:ℝ)^(m+1+C) := by exact_mod_cast hb'
  rw [pow_succ]
  linarith [one_le_pow₀ (show 1 ≤ (2:ℝ) by norm_num) (n := m+1+C)]

/-- All three components of every actual inner packet are bounded simultaneously.
The statement includes every pre-column state and the state returned after the last column. -/
theorem native_pass_storage_bits {n m L : ℕ} (b : Hex.Matrix ℤ (n+1) m) (hi : b.independent)
    (hB : ∀ i j, ((HexMatrixMathlib.matrixEquiv b) i j).natAbs ≤ 2^L)
    {c : ReductionCursor (n+1) m} (hc : (initialReductionCursor b (by omega)).Reaches c)
    {k : Fin (n+1)} {t : LLLState (n+1) m} (ht : IsPassState c.state k t) :
    (∀ i j, ((t.b.getRow i).get j).natAbs.size ≤ nativePassWidth (n+1) m L) ∧
    (∀ i j, ((t.ν.getRow i).get j).natAbs.size ≤ nativePassWidth (n+1) m L) ∧
    (∀ j, (t.d.get j).size ≤ nativePassWidth (n+1) m L) := by
  let p := n+1
  let H := nativePassH p m L
  let B := nativePassB p m L
  obtain ⟨hv,hi',_⟩ := nativeReach_invariants hc (HexLLLMathlib.LLLState.ofBasis_valid b) hi
  have hstart i j :
      ((HexMatrixMathlib.matrixEquiv c.state.b) i j).natAbs ≤ 2^(nativeRowBitBound p m L) :=
    (Nat.size_le.mp (nativeReach_basis_entry_size b hi hB hc i j)).le
  have hrow i : ‖intRowFamily c.state.b i‖+1 ≤ (2:ℝ)^H := nativeRow_norm_pow _ hstart i
  have hdsize j : (c.state.d.get j).size ≤ H := by
    apply (nativeReach_gramSlot_size b (by omega) hi hB hc j).trans
    dsimp [H,nativePassH,nativeRowBitBound,p]
    omega
  have hb (i : Fin (n+1)) (j : Fin m) : (t.b[i][j]).natAbs.size ≤ B := by
    apply (native_pass_basis_bits c.state hv hi' (fun j => (Nat.size_le.mp (hdsize j)).le)
      hrow k ht i j).trans
    exact Nat.add_le_add_right (Nat.mul_le_mul_left _ (Nat.le_succ n)) H
  obtain ⟨htv, _, htd, hupper⟩ := native_pass_frame ht hv hi'
  refine ⟨fun i j => (hb i j).trans ?_, ?_, ?_⟩
  · dsimp only [B,p,nativePassWidth]
    omega
  · intro i j
    by_cases hji : j < i
    · have hh (a : Fin (n+1)) (x : Fin m) : |t.b[a][x]| ≤ (2:ℤ)^B := by
        rw [Int.abs_eq_natAbs]
        exact_mod_cast (Nat.size_le.mp (hb a x)).le
      apply (native_scaled_coefficient_bits t htv hh i j hji).trans
      dsimp only [B,p,nativePassWidth]
      omega
    · have hij : i ≤ j := le_of_not_gt hji
      rw [hupper i j hij, nativeReach_upper_frame hc i j hij]
      apply (Bit.initial_nu_entry_size b hB i j).trans
      unfold nativePassWidth
      omega
  · intro j
    rw [htd]
    apply (hdsize j).trans
    dsimp only [H,p,nativePassWidth]
    omega

/-- The same cap at every complete cursor, including the initial and terminal cursors. -/
theorem native_outer_storage_bits {n m L : ℕ} (b : Hex.Matrix ℤ (n+1) m) (hi : b.independent)
    (hB : ∀ i j, ((HexMatrixMathlib.matrixEquiv b) i j).natAbs ≤ 2^L)
    {c : ReductionCursor (n+1) m} (hc : (initialReductionCursor b (by omega)).Reaches c) :
    (∀ i j, ((c.state.b.getRow i).get j).natAbs.size ≤ nativePassWidth (n+1) m L) ∧
    (∀ i j, ((c.state.ν.getRow i).get j).natAbs.size ≤ nativePassWidth (n+1) m L) ∧
    (∀ j, (c.state.d.get j).size ≤ nativePassWidth (n+1) m L) :=
  native_pass_storage_bits b hi hB hc (k:=⟨0,Nat.zero_lt_succ n⟩) (Or.inl rfl)

end Lattice
end LinearProgramming
end Optimization
end OAI
