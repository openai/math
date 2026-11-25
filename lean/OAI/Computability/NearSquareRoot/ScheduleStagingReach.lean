import OAI.Computability.NearSquareRoot.ScheduleStagingOuterOutput

/-! # Publishing at the same radius as the digit workspace

The source stream ends at the bottom of the controller's original input
register. Both this address and the end of the fresh output word fit inside
the radius used for resetting the digit tapes.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace StagingOuterOutput

open IntegerMultiplication TM Code Bits ChunkTask ChunkLoop ChunkPhases
open ChunkControl (Driver)
open StagingOuter (Axis Letter)

variable {I D : Type} (d : Driver)

theorem final_source_pos (C : ℕ) (p : Input) (w : Word) :
    ((StagingOuter.final (I:=I) (D:=D) d C p (w.map Ltr.bit)).tape (source d)).pos =
      ((input p).length : ℤ) - w.length := by
  rw [source,StagingOuter.final_register]
  simp [StagingReset.markedTape,StagingControl.tape]

theorem source_room (C : ℕ) (p : Input) (w : Word) :
    ((StagingOuter.final (I:=I) (D:=D) d C p (w.map Ltr.bit)).tape (source d)).pos +
      w.length ≤ (StagingOuter.radius C p.n : ℤ) := by
  rw [final_source_pos,sub_add_cancel]
  exact_mod_cast (input_length p).trans (Nat.mul_le_mul_right (p.n+1)
    (show 32 ≤ 4*(C+50) by omega))

theorem output_room (C : ℕ) (p : Input) (w : Word) (hw : w.length = 2*p.n) :
    w.length ≤ StagingOuter.radius C p.n := by
  rw [hw]
  exact Nat.mul_le_mul (show 2 ≤ 4*(C+50) by omega) (Nat.le_succ _)

/-- The clean publication phase fits exactly the radius used throughout the
staged digit loop, including the two heads' positions after the final bit. -/
theorem run_fixed_radius [DecidableEq I] (C : ℕ) (m : Operands → Word) (p : Input)
    (w : Word) (hw : w.length = 2*p.n)
    (digit : Rule (Letter d) D (Axis d I)) (start : D) {T : ℕ}
    (ctl : StagingPhases.Calls d.load d.test d.prepare d.collect d.emit C m p (w.map Ltr.bit))
    (width : ∀ i < p.count, (digitReply m p i).length = 2*p.u)
    (call : ∀ i < p.count, StagingOuter.Call d C m p digit start T i) :
    let R := StagingOuter.radius C p.n
    ∃ t ≤ (p.count+1)*(6*(C*(p.n+1))+T+8)+1+w.length, ∃ z,
      FencedRun (rule d digit start) (fun _ => -(R : ℤ)) (fun _ => (R : ℤ))
        (initial d C p) t z ∧
      advance (rule d digit start) z = none ∧ whole (blank d) (w.map (bit d)) (z.tape none) := by
  obtain ⟨t,ht,run,stop⟩ := StagingOuter.outer d C m p digit start ctl width call
  obtain ⟨z,tr,halt,out⟩ := StagingPublish.publish_fixed_fence _ (source d) (decode d) (bit d) (blank d)
    run stop w (final_read d C p w) (source_room d C p w) (output_room C p w hw)
  exact ⟨_,by omega,z,tr,halt,out⟩

end StagingOuterOutput

end NearSquareRoot
end Computability
end OAI
