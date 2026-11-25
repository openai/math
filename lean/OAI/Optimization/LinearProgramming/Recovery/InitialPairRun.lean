import OAI.Optimization.LinearProgramming.Recovery.InitialPairShared
import OAI.Optimization.LinearProgramming.Recovery.PairBuilder

/-! Specialize the physical row/complement ROM to the first public LP tableau. The
stored column and kernel bases describe both branches of the original decision. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Recovery
namespace InitialPair

open RAM RAM.Call RAM.Callable RAM.Tape Matrix Geometry
open scoped Matrix

theorem blank_within {H : ℕ} (h : 3 ≤ H) : PairBuilder.Within H blank := by
  intro p
  have z : ratBits (0 : ℚ) ≤ H := (by decide : ratBits (0 : ℚ) ≤ 3).trans h
  simpa [blank,start,State.memory] using z

/-- The exact physical first ROM call. The blank even/native bank has an empty previous
footprint, and the odd caller contains the public initializer's retained data. -/
theorem run_from_ready {m d : ℕ} (A : Matrix (Fin m) (Fin d) ℚ) (b : Fin m → ℚ)
    (caller : Memory ℚ) (H e : ℕ) (ready : Ready A b caller) (hH : 3 ≤ H)
    (hc : PairBuilder.Within H caller) (entries : ∀ i j, ratBits ((slackColumns A b)ᵀ i j) ≤ e) :
    let l := layout m d
    let W := max H (PairBuilder.pairWidth (d+1) (m+1) e)
    ∃ (front back : Memory ℚ) (k s : ℕ) (F : Matrix (Fin k) (Fin (m+1)) ℚ) (R : Matrix (Fin s) (Fin (m+1)) ℚ),
      (PairBuilder.program false).Run (fun x => ratBits x ≤ W) (Odd.memory blank caller)
        (PairBuilder.time l) (Odd.memory front back) ∧
      PairBuilder.Within W front ∧ PairBuilder.Within W back ∧
      Footprint (PairBuilder.capacity (d+1) (m+1) 0-1) (front.atPC 0) ∧
      PairBuilder.SourceFrame l caller back ∧ PairBuilder.Prepared false l (slackColumns A b)ᵀ F R back ∧
      k ≤ d+1 ∧ (∀ i j, ratBits (F i j) ≤ PairBuilder.rowWidth (d+1) (m+1) e) ∧
      ∀ i j, ratBits (R i j) ≤ PairBuilder.rowWidth (m+1) (m+1)
        (PairBuilder.residualWidth (m+1) (m+1) (PairBuilder.rowWidth (d+1) (m+1) e)) := by
  have clean : Footprint 0 (blank.atPC 0) :=
    Footprint.initial [] ([] : List ℚ) (by simp) (by simp) (by simp)
  exact PairBuilder.program_run false (layout m d) (slackColumns A b)ᵀ blank caller H e
    ready.inputRegs ready.transpose entries (blank_within hH) hc clean

end InitialPair
end Recovery
end LinearProgramming
end Optimization
end OAI
