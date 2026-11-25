import OAI.Optimization.LinearProgramming.Lattice.LLLBitWidth
import OAI.Optimization.LinearProgramming.Lattice.NativeStorageBound

/-! The actual polynomial width budget used by the bit-stack LLL program. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Lattice
namespace Bit

open Hex.Internal
open ExactQuantumFactoring.BitStackProgram

/-- One polynomial specializes the native register estimate to three copies of the
physical input length, which bounds both dimensions and the input entry length. -/
noncomputable def lllWidth : Polynomial ℕ :=
  let x := Polynomial.X
  let row := (x+x+2*x)*x*x+x+x+x+3
  let h := x+1+row+1
  let b := (2*h+2)*x+h
  (x+x+2*b)*x+((x+x+2*x)*x+1)+b+h+x+x+1

noncomputable def lllSpace : Polynomial ℕ := Polynomial.C 100 * (lllWidth+1)^3

@[simp] theorem lllWidth_eval (z : ℕ) : lllWidth.eval z = nativePassWidth z z z := by
  simp [lllWidth,nativePassWidth,nativePassB,nativePassH,nativeRowBitBound]

@[simp] theorem lllSpace_eval (z : ℕ) : lllSpace.eval z = 100*(nativePassWidth z z z+1)^3 := by
  simp [lllSpace]

/-- The complete physical sweep frame fits the chosen budget for every actual native
visit, its return state, and every reachable boundary. -/
theorem passFrame_fits {n m : ℕ} (b : Hex.Matrix ℤ (n+1) m) (hi : b.independent)
    {c : ReductionCursor (n+1) m} (hc : (initialReductionCursor b (by omega)).Reaches c)
    (k : Fin (n+1)) (t : LLLState (n+1) m) (ht : IsPassState c.state k t)
    (j r : ℕ) (hj : j ≤ n+1) (hr : r ≤ n+1) :
    (sweepCode stateCode (j,r,packState t)).length ≤ lllSpace.eval (intMatrixCode (packMatrix b)).length := by
  let L := (intMatrixCode (packMatrix b)).length
  obtain ⟨hnL,hmL,he⟩ := packedMatrix_input_bounds b (by omega)
  have hb (i : Fin (n+1)) (l : Fin m) : (HexMatrixMathlib.matrixEquiv b i l).natAbs ≤ 2^L := by
    rw [HexMatrixMathlib.matrixEquiv_apply]
    exact (Nat.size_le.mp (he i l)).le
  obtain ⟨hb',hν,hd⟩ := native_pass_storage_bits b hi hb hc ht
  have hmono : nativePassWidth (n+1) m L ≤ nativePassWidth L L L :=
    nativePassWidth_mono hnL hmL le_rfl
  have hLW : L ≤ nativePassWidth L L L := by unfold nativePassWidth; omega
  have hbits (u : ℕ) : u.size ≤ u := Nat.size_le.mpr Nat.lt_two_pow_self
  rw [lllSpace_eval]
  exact packedSweep_length t j r (nativePassWidth L L L) (hnL.trans hLW) (hmL.trans hLW)
    ((hbits j).trans (hj.trans (hnL.trans hLW))) ((hbits r).trans (hr.trans (hnL.trans hLW)))
    (fun i l => (hb' i l).trans hmono) (fun i l => (hν i l).trans hmono) (fun i => (hd i).trans hmono)

/-- Cursors absorb the full table plus one binary index. The outer guard grants extra
space for the repeated unary cap. -/
theorem reachableCursor_fits {n m : ℕ} (b : Hex.Matrix ℤ (n+1) m) (hi : b.independent)
    {c : ReductionCursor (n+1) m} (hc : (initialReductionCursor b (by omega)).Reaches c) :
    (cursorCode (c.index,packState c.state)).length ≤ lllSpace.eval (intMatrixCode (packMatrix b)).length := by
  have ht : IsPassState c.state 0 c.state := Or.inl rfl
  have hh := passFrame_fits b hi hc 0 c.state ht 0 c.index (Nat.zero_le _) c.bounded
  simp only [sweepCode,prodCode,pairBits_length] at hh
  change (pairBits (Nat.bits c.index) (stateCode (packState c.state))).length ≤ _
  rw [pairBits_length]
  omega

end Bit
end Lattice
end LinearProgramming
end Optimization
end OAI
