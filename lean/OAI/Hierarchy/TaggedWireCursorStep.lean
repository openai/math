import OAI.Hierarchy.TaggedWirePrefixCursor
import Batteries.Tactic.OpenPrivate

namespace OAI
/-! # The physical matrix at the first edge of a replayed calendar path -/
noncomputable section
namespace Hierarchy.WireTelescope.CalendarTape.Prefix
open ProtocolRAM.Calendar Tagged LinearAlgebra.SpectralBooks ChordGraph
open scoped Classical BigOperators
open private FrameAction FrameAction.mk FrameAction.matrix cursorAction StepLaw
  from OAI.Hierarchy.TaggedWirePrefixCursor

private theorem matrix_transport {F : Type*} [Field F] {Y : Type} {S n : ℕ}
    (W : Y→Widths S) (v : Y) (law : Prop) (Q : Y→Type) {D T : Frame Y n}
    (same : D=T) (A : FrameAction F W v T law) (c : T.choice) (rest : Q (T.next c)) :
    HEq (FrameAction.matrix ((congrArg (fun f=>FrameAction F W v f law) same).mpr A)
      (framePair Q same c rest).1) (FrameAction.matrix A c) := by
  cases same
  rfl

variable {X : Type} {slot : Event→Slot X} {events : List Event} {x₀ : X} {S : ℕ} {F : Type*} [Field F]
variable (width : ∀{tail x},Prefix slot events x₀ tail x→Widths S)
    (M : ∀{e tail x}(p : Prefix slot events x₀ (e::tail) x) (c : (slot e).choice x),
      SiteMatrix (State (width p)) (State (width (advance p c))) F)

theorem atStep_live_replay {e tail x} (p : Prefix slot events x₀ (e::tail) x)
    (c : (slot e).choice x) (rest : Path slot tail ((slot e).next x c)) :
    HEq (atStep @width @M e (atCursor p) (replay p ⟨c,rest⟩).1) (M p c) := by
  let A : FrameAction F (atWidth @width) (atCursor p) (liveFrame p) (StepLaw (slot:=slot) (events:=events) (x₀:=x₀) @width @M) :=
    FrameAction.mk (fun a=>M p a) (fun h v=>h p v)
  have cap:=matrix_transport (atWidth @width) (atCursor p) (StepLaw (slot:=slot) (events:=events) (x₀:=x₀) @width @M) (Path cursorSlot tail)
    (frame_live e tail x p) A c (replay (advance p c) rest)
  simpa only [atStep,cursorAction,replay,atCursor,dite_eq_left rfl,ite_eq_left rfl,dite_true,ite_true,id_eq,A,
    cursorSlot,move,atWidth,liveFrame,nextAt] using! cap

end Hierarchy.WireTelescope.CalendarTape.Prefix
end

end OAI
