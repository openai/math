import OAI.Hierarchy.TaggedWideCalendarReceipt
import OAI.Hierarchy.TaggedWideCursorReportRows

namespace OAI
/-! # The common purchase data at the selected calendar rank -/
noncomputable section
namespace Hierarchy.ProbeStage.CoreBoard.PhysicalTerm.CalendarTerms
open ThreeFlat Routing
open AdaptiveProbe TaggedPrune Tagged WireTelescope WireTelescope.CalendarTape ProtocolRAM.Calendar
open ProtocolStackContraction TaggedShorterFields TaggedShorterBudget ProtocolRAMReportedPorts
open WideStack WideStack.Leaf WideCalendarSites WideControlJoin
open scoped Classical BigOperators
set_option quotPrecheck false

abbrev RowBoard := (q : ℕ) × (Fin q→ProtocolRAMEmit.Row)

variable {F : Type} [Field F] {L : ℕ} (key : Fin L ↪ ℕ×ℕ) (S : Type)
    (groups ports lanes w m n view : ℕ)

/-- These are the five row-dependent data fields of the fixed calendar receipt.
They move together when the selected path is read at its cursor rank. -/
structure RankedRows (board : RowBoard) where
  positive : Fin board.1→Prop
  stage : Fin board.1→ℕ
  installed : ∀t,Installed F groups ports lanes w m (key t).2 (atScale positive stage (key t).1 board.2)
  cap : {i : Fin board.1 // ¬positive i}→ℕ
  numbering : Pin (banks installed) cap (Fin n) ((Fin groups×Fin ports)×Fin view) ≃ S

namespace RankedRows
variable {key S groups ports lanes w m n view}
local notation "Rows" => RankedRows (F:=F) key S groups ports lanes w m n view

/-- All receipt fields, including dependent fields such as the data pin
numbering, are transported along precisely the same equality. -/
def move {old new : RowBoard} (same : new=old) (r : Rows old) : Rows new := same.symm ▸ r

theorem move_property {old new : RowBoard} (same : new=old) (r : Rows old)
    (test : ∀o,Rows o→Prop) (valid : test old r) : test new (move same r) := by
  cases same
  exact valid

structure Bounds {board : RowBoard} (r : Rows board) : Prop where
  room : ∀e,(board.2 e.val).width≤r.cap e
  cover : ∀i,r.positive i→0<(board.2 i).width→
    ∃t,key t=(r.stage i,widthIndex m ((board.2 i).width/(w:ℝ))) ∧ (board.2 i).group<groups

variable {Ex Se : Type} [Fintype Ex] [Fintype Se] [Fintype S] (G : Gate)
local notation "V" => SitePins Ex Se S G
structure PrivatePlane {board : RowBoard} (r : Rows board) (freeNet planeNet : Net F V)
    (ex : Ex→Bool) (sel : Se→Bool) (seen : G.Seen→Bool) : Prop where
  free : ∀a y h p,TypedWiring.value freeNet (readPins r.numbering ex sel seen
    (write (banks r.installed) r.cap a y h p)) =
      if EndsPadded (fun e=>(board.2 e.val).width) r.cap y then privateWeight board.2 r.positive r.cap y else 0
  output : ∀a y h p,TypedWiring.value planeNet (readPins r.numbering ex sel seen
    (write (banks r.installed) r.cap a y h p)) =
      TypedWiring.value (decoder (F:=F) (groups:=groups) (ports:=ports) (lanes:=lanes)
        (view:=view) (w:=w) key) (Sum.elim (voltage (banks r.installed) a) p)

variable {X : Type} {z d k W R M den : ℕ}
    {slots : Event→Slot X} {es : List Event} {state : Equiv.Perm (Row z)→X}
    (Z : CalendarTerms F z d k W R M den slots es state)
    (p : Equiv.Perm (Row z)) (i : Fin ((Z.nativeRouting S).count p))
local notation "boot" => (Prefix.start : Prefix slots es (state p) es (state p))
local notation "path" => (Fintype.equivFin (Path slots es (state p))).symm i
local notation "native" => Z.reported p path
local notation "replay" => cursorReport p (Z.width p) (Z.reported p) (Prefix.histories boot path)
local notation "cur" => (⟨(replay).edges,(replay).rows⟩ : RowBoard)
local notation "src" => (⟨(native).edges,(native).rows⟩ : RowBoard)

def onBranch {board : RowBoard} (reported : src=board) (r : Rows board) : Rows cur :=
  move ((cursor_report_rows p (Z.width p) (Z.reported p) path).trans reported) r

theorem onBranch_property {board : RowBoard} (reported : src=board) (r : Rows board)
    (test : ∀o,Rows o→Prop) (valid : test board r) :
    test cur (onBranch Z p i reported r) :=
  move_property _ _ test valid

end RankedRows
end Hierarchy.ProbeStage.CoreBoard.PhysicalTerm.CalendarTerms

end
end OAI
