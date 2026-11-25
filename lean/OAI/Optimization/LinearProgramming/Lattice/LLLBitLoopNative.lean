import OAI.Optimization.LinearProgramming.Lattice.LLLBitLoop
import OAI.Optimization.LinearProgramming.Lattice.LLLBitSweepNative
import OAI.Optimization.LinearProgramming.Lattice.LLLBitTime
import OAI.Optimization.LinearProgramming.Lattice.BitGramRead
import OAI.Optimization.LinearProgramming.Lattice.BitArithmeticBridge

/-! Simulation of the signed row-major bit-stack loop by the native LLL trajectory. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Lattice
namespace Bit

open ExactQuantumFactoring.BitStackProgram
open ExactQuantumFactoring.BitStackProgram.Procedure
open Hex.Internal

def cursorActive (c : Cursor) : Bool := decide (c.1 < c.2.1.length)

noncomputable def cursorActiveP : Procedure cursorCode boolCode cursorActive :=
  binaryLt.comp ((first Nat.bits stateCode).pair
    ((listLength intRowCode []).comp (basisP.comp (second Nat.bits stateCode))))

def cursorAccept (c : Cursor) : Bool := lovasz (gramQuad c.1 c.2)

noncomputable def cursorAcceptP : Procedure cursorCode boolCode cursorAccept := lovaszP.comp gramQuadP

def packedOuter (exchange : Cursor → State) := outerStep cursorActive packedSweep cursorAccept exchange

noncomputable def packedOuterP {exchange : Cursor → State} (swap : Procedure cursorCode stateCode exchange) :
    Procedure (outerCode stateCode) (outerCode stateCode) (packedOuter exchange) :=
  outerStepP cursorActiveP packedSweepP cursorAcceptP swap

def packCursor {n m : ℕ} (cap : ℕ) (c : ReductionCursor n m) : OuterState State :=
  (cap,c.index,packState c.state)

private theorem cursorAccept_native {n m : ℕ} (s : LLLState n m) (k : Fin n) (hk : 0 < k.val) :
    cursorAccept (k.val,packState s) = true ↔
      (3/4 : ℚ).num * (s.d.get ⟨k.val,by omega⟩ : ℤ)^2 ≤
        ((3/4 : ℚ).den : ℤ) * ((s.d.get ⟨k.val+1,by omega⟩ : ℤ) *
          (s.d.get ⟨k.val-1,by omega⟩ : ℤ) + ((s.ν.getRow k).get ⟨k.val-1,by omega⟩)^2) := by
  rw [cursorAccept,gramQuad_packState s k hk,lovasz_true_iff]
  conv_lhs => rhs; rhs; lhs; rw [mul_comm]
  rfl

/-- Agreement of a single literal outer step, under the exact agreements of the
size-reduction and row-swap subroutines on the state where they are called. -/
theorem packedOuter_hold {n m : ℕ} (c : ReductionCursor n m) (cap : ℕ) (exchange : Cursor → State)
    (hsweep : c.index < n → packedSweep (cap,c.index,packState c.state) =
      packState (c.state.sizeReduce c.index))
    (hswap : c.index < n → exchange (c.index,packState (c.state.sizeReduce c.index)) =
      packState ((c.state.sizeReduce c.index).swapStep c.index)) :
    packedOuter exchange (packCursor cap c) = packCursor cap (hold c) := by
  by_cases hk : c.index < n
  · let k : Fin n := ⟨c.index,hk⟩
    let r := c.state.sizeReduce c.index
    have hactive : cursorActive (c.index,packState c.state) = true := by simp [cursorActive,packState,hk]
    by_cases ha : cursorAccept (c.index,packState r) = true
    · let out : ReductionCursor n m := ⟨r,c.index+1,by omega,by omega⟩
      have hn : c.next = some out := by
        unfold ReductionCursor.next
        simp only [hk, ↓reduceDIte]
        split
        · rfl
        · rename_i hbad
          exact (hbad ((cursorAccept_native r k c.positive).mp ha)).elim
      have he : hold c = out := by simp [hold,hn]
      simp only [packedOuter,packCursor,outerStep,hactive,↓reduceIte,hsweep hk,he]
      change (cap,advanceOrSwap cursorAccept exchange (c.index,packState r)) = _
      simp [advanceOrSwap,ha,out]
    · let out : ReductionCursor n m := ⟨r.swapStep c.index,max (c.index-1) 1,Nat.le_max_right ..,
        max_le (by have := c.bounded; omega) (c.positive.trans c.bounded)⟩
      have hn : c.next = some out := by
        unfold ReductionCursor.next
        simp only [hk, ↓reduceDIte]
        split
        · rename_i hgood
          exact (ha ((cursorAccept_native r k c.positive).mpr hgood)).elim
        · rfl
      have he : hold c = out := by simp [hold,hn]
      simp only [packedOuter,packCursor,outerStep,hactive,↓reduceIte,hsweep hk,he]
      change (cap,advanceOrSwap cursorAccept exchange (c.index,packState r)) = _
      simp [advanceOrSwap,ha,out,show exchange (c.index,packState r) = packState (r.swapStep c.index) from hswap hk]
  · have hn : c.next = none := by simp [ReductionCursor.next,hk]
    simp [packedOuter,packCursor,outerStep,cursorActive,packState,hk,hold,hn]

/-- A simulation restricted to precisely the native reachable states. -/
theorem packedOuter_iterate {n m : ℕ} (c : ReductionCursor n m) (cap : ℕ) (exchange : Cursor → State)
    (hsweep : ∀ d, c.Reaches d → d.index < n → packedSweep (cap,d.index,packState d.state) =
      packState (d.state.sizeReduce d.index))
    (hswap : ∀ (d : ReductionCursor n m), d.index < n → exchange (d.index,packState (d.state.sizeReduce d.index)) =
      packState ((d.state.sizeReduce d.index).swapStep d.index)) (t : ℕ) :
    (packedOuter exchange)^[t] (packCursor cap c) = packCursor cap (hold^[t] c) := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [Function.iterate_succ_apply',ih,Function.iterate_succ_apply']
    exact packedOuter_hold _ _ _ (hsweep _ (initial_reaches_hold c t)) (hswap _)

end Bit
end Lattice
end LinearProgramming
end Optimization
end OAI
