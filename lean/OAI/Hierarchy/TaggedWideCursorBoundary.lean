import OAI.Hierarchy.TaggedWireCursorReplay
import OAI.Hierarchy.TaggedWideTimeOccupancy

namespace OAI
/-! # Native memories and calendar dates of the replayed prefix cursors -/
noncomputable section
namespace Hierarchy.WireTelescope.CalendarTape.Prefix
open ProtocolRAM.Calendar
variable {X : Type} {slot : Event→Slot X} {events : List Event} {start : X}
local notation "P" => Prefix slot events start
local notation "C" => cursorSlot (slot:=slot) (events:=events) (x₀:=start)

/-- The next replayed boundary is the original advanced cursor at its suffix boundary. -/
theorem replay_boundary_succ {e tail x} (p : P (e::tail) x) (c : (slot e).choice x)
    (j : Path slot tail ((slot e).next x c)) (i : Fin (tail.length+1)) :
    boundaryState C (e::tail) (atCursor p) (replay p ⟨c,j⟩) i.succ =
      boundaryState C tail (atCursor (advance p c)) (replay (advance p c) j) i := by
  simpa only [boundaryState, Fin.cases_succ] using
    replay_tail_apply p c j (fun v path=>boundaryState C tail v path i)

theorem replay_boundary : ∀{tail x}(p : P tail x)(j : Path slot tail x)(i : Fin (tail.length+1)),
    let atTime:=boundaryState C tail (atCursor p) (replay p j) i
    atTime.todo=tail.drop i.val ∧ atTime.mem=boundaryState slot tail x j i
  | [],_,p,_,i=>by
    have bounded : i.val<1:=i.isLt
    have zero : i=0:=Fin.ext (by change i.val=0; omega)
    subst i
    exact ⟨rfl,rfl⟩
  | e::tail,x,p,⟨c,rest⟩,i=>by
    induction i using Fin.cases with
    | zero=>exact ⟨rfl,rfl⟩
    | succ i=>
      have same := replay_boundary_succ p c rest i
      have previous := replay_boundary (advance p c) rest i
      constructor
      · simpa only [Fin.val_succ,List.drop_succ_cons] using
          (congrArg Cursor.todo same).trans previous.1
      · exact (congrArg Cursor.mem same).trans previous.2

theorem start_boundary (j : Path slot events start) (i : Fin (events.length+1)) :
    let init : P events start:=Prefix.start
    let here:=boundaryState C events (atCursor init) (histories init j) i
    events.length-here.todo.length=i.val ∧ here.mem=boundaryState slot events start j i := by
  have atTime:=replay_boundary (Prefix.start : P events start) j i
  obtain ⟨todo,memory⟩:=atTime
  refine ⟨?_,memory⟩
  change events.length-(boundaryState C events (atCursor (Prefix.start : P events start)) (replay _ j) i).todo.length=i.val
  rw [todo,List.length_drop]
  have hi:=i.isLt
  omega

end Hierarchy.WireTelescope.CalendarTape.Prefix

end
end OAI
