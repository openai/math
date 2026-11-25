import OAI.Optimization.LinearProgramming.RAM.CallableReentrant
import OAI.Optimization.LinearProgramming.RAM.CallableOddCalls
import OAI.Optimization.LinearProgramming.RAM.CallableWindow
import OAI.Optimization.LinearProgramming.Geometry.GramEncoding

/-! Stage a dynamic dense matrix and run its normal ROM while preserving the logical LP caller. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Recovery
namespace PairBuilder

open RAM RAM.Block RAM.Callable Matrix
open _root_.OAI.Optimization.LinearProgramming.Geometry

def normalCall (b : Block) : Fragment := Fragment.stage (.invoke (b.compile 0 ++ [.halt 0]) 1 (Odd.sink (.index 1)))

theorem normalCall_run {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K] {h n : ℕ} (A : Matrix (Fin h) (Fin n) K) (b : Block) (native caller : Memory K)
    (P Q : K→Prop) (src dims cap oldCap : ℕ) (raw : RawTapes caller src dims cap (encodedGramInput A) [h,n])
    (old : Footprint oldCap (native.atPC 0)) (fit : oldCap < cap) (words : h*n ≤ cap) (pair : 2 ≤ cap)
    (hn : native.AllData P) (hc : caller.AllData P) (zero : P 0) (widen : ∀ x,Q x → P x)
    {c : ℕ} {t : Memory K} (work : Eval (Memory.AllData Q) b (start [h,n] (encodedGramInput A)).memory c t) :
    (normalCall b).Run P (Odd.memory native caller) (19*cap+225+(2*(c+1)+2)) (Odd.memory t (caller.putIndex 1 0)) ∧
      Footprint (nativeWindow (b.compile 0 ++ [.halt 0]) [h,n] (encodedGramInput A)+(c+1)) (t.atPC 0) := by
  obtain ⟨tr,steps,halt,mem,bits⟩:=work.halted_trace (tag:=0)
  have exec := Odd.invoke_packed 1 (.index 1) P caller [h,n] (encodedGramInput A) tr
    (show 0<1 by decide) hc steps (fun i j => widen _ (bits i j)) halt (show (caller.putIndex 1 0).AllData P from hc)
  rw [mem] at exec
  have call := Fragment.stage_of_run (native.atPC 0) caller src dims oldCap cap (encodedGramInput A) [h,n]
    raw hc hn zero old fit (by simpa using words) (by simpa using pair) exec
  have fp := nativeWindow_trace steps le_rfl
  rw [mem] at fp
  exact ⟨call,fp⟩
end PairBuilder
end Recovery
end LinearProgramming
end Optimization
end OAI
