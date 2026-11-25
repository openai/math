import OAI.Optimization.LinearProgramming.Geometry.MinorExactPacket
import OAI.Optimization.LinearProgramming.Geometry.MinorDirectPark
import OAI.Optimization.LinearProgramming.Geometry.MinorDirectBody

/-! Exact in-place refinement of the geometric scalar query request. The input and every
odd caller register are restored before entering the persistent even-bank service. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Geometry
namespace MinorInstall

open RAM RAM.Block RAM.Callable OracleSpec OracleSpec.MinorLog Contraction.Machine

def directBranch (tag : ℕ) : Block := .seq (Odd.block parkCode)
  (.seq (directBody tag) (Odd.block (restoreCode tag)))

def exactStage : Block := .seq (Odd.block readTag) (.branch (.scalarLT (Odd.slot 29) (Odd.slot 2))
  (directBranch 1) (directBranch 0))

/-- The native state is the precise frozen resume state and the entire geometric state
is the input state again. Its counting cost uses only matrix dimensions. -/
theorem exactStage_eval {r s n : ℕ} (u : RawIndex r s n) (native : State ℚ) (caller : Memory ℚ)
    (H : ℕ) (sourceHigh : 35 ≤ caller.index 80) (c2 : caller.data 2=0) (c29 : caller.data 29=0)
    (request : registerPacket (caller.atPC 0) 80 81=BorderBatch.packet u)
    (hc : ∀i,ratBits (caller.data i) ≤ H) (hn : ∀i,ratBits (native.data i) ≤ H) :
    ∃ cost ≤ directClock r s n,
      Eval (Memory.AllData (fun q => ratBits q ≤ directWidth H r s n)) exactStage
        (Odd.memory native.memory caller) cost (Odd.memory (MinorLog.resume native (words u)).memory caller) := by
  let P := fun q : ℚ => ratBits q ≤ directWidth H r s n
  let B := r+s+n+1
  obtain ⟨length,source,tagged⟩ := scalar_packet u caller request
  have callerSafe : caller.AllData P := fun i => (hc i).trans (le_max_left ..)
  have nativeSafe : native.memory.AllData P := fun i => (hn i).trans (le_max_left ..)
  have restoredSafe : (MinorLog.resume native (words u)).memory.AllData P := nativeSafe
  have small (i : ℕ) (hi : i ≤ B) : P (i:ℚ) := (nat_word_bits i).trans
    (le_trans (by dsimp only [B] at hi; omega : i+3 ≤ r+s+n+4) (le_max_right ..))
  have one : P 1 := by simpa using small 1 (by dsimp [B]; omega)
  have granted : P (matrixTag u:ℚ) := tagged ▸ callerSafe _
  obtain ⟨a,ha,read⟩ := Odd.block_eval P native.memory nativeSafe
    (readTag_eval caller P (matrixTag u) tagged callerSafe)
  obtain ⟨b,hb,park⟩ := Odd.block_eval P native.memory nativeSafe
    (park_eval caller P (matrixTag u) callerSafe granted c2 one)
  have rawSource (j : ℕ) (hj : 1 ≤ j) (hi : j < (words u).length) :
      (parked caller).data (caller.index 80+j)=(((words u)[j]?.getD 0:ℕ):ℚ) :=
    (parked_source caller sourceHigh _ hj).trans (source j hi)
  have PS := parked_safe caller P callerSafe one
  have body : ∃ c ≤ (words u).length*(5*B+32)+50,
      Eval (Memory.AllData P) (directBody (matrixTag u)) (Odd.memory native.memory (parked caller)) c
        (Odd.memory (MinorLog.resume native (words u)).memory (parked caller)) :=
    directBody_eval native (parked caller) P (matrixTag u) (caller.index 80) B (words u)
      (words_shape u) (words_first u) rfl length rawSource
      (parked_zero_two caller sourceHigh c2) (parked_zero_29 caller sourceHigh c29) (parked_one caller)
      (fun _ h => word_bound u h) small nativeSafe PS
  obtain ⟨c,hc',work⟩ := body
  obtain ⟨d,hd,restore⟩ := Odd.block_eval P _ restoredSafe
    (restore_eval caller P (matrixTag u) callerSafe one sourceHigh c2 tagged)
  have phase := park.seq (work.seq restore)
  let start := Odd.memory native.memory (caller.putData 2 (matrixTag u:ℚ))
  let stop := Odd.memory (MinorLog.resume native (words u)).memory caller
  have go : ∃ k ≤ 2, Eval (Memory.AllData P)
      (.branch (.scalarLT (Odd.slot 29) (Odd.slot 2)) (directBranch 1) (directBranch 0))
      start (k+(b+(c+d))) stop := by
    rcases matrixTag_cases u with zero | one
    · have test : (Cond.scalarLT (Odd.slot 29) (Odd.slot 2)).test start=false := by simp [Cond.test,start,c29,zero]
      refine ⟨1,by decide,?_⟩
      apply Eval.branchFalse test
      simpa only [directBranch,zero,start,stop] using phase
    · have test : (Cond.scalarLT (Odd.slot 29) (Odd.slot 2)).test start=true := by simp [Cond.test,start,c29,one]
      refine ⟨2,by decide,?_⟩
      have go := Eval.branchTrue (b := directBranch 0) test (a := directBranch 1)
        (show Eval (Memory.AllData P) (directBranch 1) start (b+(c+d)) stop by
          simpa only [directBranch,one,start,stop] using phase)
      exact (show 1+(b+(c+d))+1=2+(b+(c+d)) by omega) ▸ go
  obtain ⟨e,he,branch⟩ := go
  have lengthBound := Nat.mul_le_mul_right (5*B+32) (words_short u)
  refine ⟨a+(e+(b+(c+d))),by unfold directClock; dsimp only [B] at hc' lengthBound; omega,read.seq branch⟩

end MinorInstall
end Geometry
end LinearProgramming
end Optimization
end OAI
