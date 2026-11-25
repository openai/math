import OAI.Hierarchy.TaggedWideDatedRange
import OAI.Hierarchy.TaggedWideTimeGuard
import OAI.Hierarchy.TaggedWideDatedPages
import OAI.Hierarchy.TaggedWideCalendarFrame
import OAI.Hierarchy.TaggedWideSwitchTariff

namespace OAI
/-! # Fixed observed bit positions of the chronological role-width bank -/
noncomputable section
set_option quotPrecheck false
namespace Hierarchy
open LinearAlgebra.SpectralBooks ChordGraph
open ThreeFlat Routing Diagonal TraceWords
open Computability.VPVNP.BurstRAM PrivateRAM ProbeStage CoreBoard HistoryRoles ProtocolRAM.Calendar
open Tagged Tagged.WideControlJoin WireTelescope CalendarTape
open scoped Classical BigOperators Fin.CommRing

namespace ProtocolRAM.Calendar.WideCPU.Dated
variable {T : ℕ} (g : Dated T)
theorem width_before_workEnd (work : ℕ) (j : Fin (T+1)) (i : Fin g.roleWords) :
    g.roleStart work j+1+i.val<g.workEnd work := by
  have block : 1+i.val<3*g.roleSpan:=by
    unfold roleSpan DatedRoleSheets.span;have inside:=i.isLt;omega
  have after:=Nat.mul_le_mul_right (3*g.roleSpan) (show j.val+1≤T+1 from j.isLt)
  have extent : g.roleStart work j+1+i.val<g.rolesEnd work:=by
    dsimp [roleStart,rolesEnd]
    rw [Nat.add_mul,Nat.one_mul] at after
    omega
  unfold workEnd slotStart maskStart controlStart WideCPU.endOf
  omega
end ProtocolRAM.Calendar.WideCPU.Dated

namespace WireTelescope.CalendarTape
variable {F Ex Se Data Role X : Type} [Field F] [Fintype Ex] [Fintype Se] [Fintype Data] [Fintype Role]
variable (es : List Event) (cap : Role→ℕ) (maximum : ℕ) (covers : ∀p,cap p≤ maximum)
  (g : WideCPU.Dated es.length) (work : ℕ) (G : Gate) (inside : g.workEnd work≤G.u)
  (shelf : Role → Fin g.roleWords) (narrow : WideParent.columnBits maximum≤G.W+1)
local notation "Q" => (r:Role) × Fin (cap r)
local notation "N" => (es.length+1)*Fintype.card Q
local notation "V" => SitePins Ex Se Data G
local notation "W" => WideParent.columnBits maximum
local notation "fits" => fun r=>(covers r).trans (WideParent.column_lt maximum).le

def observedWidthRow (j : Fin (es.length+1)) (r:Role) : Fin G.u :=
  ⟨g.roleStart work j+1+(shelf r).val,(g.width_before_workEnd work j (shelf r)).trans_le inside⟩

local notation "row" => observedWidthRow es g work G inside shelf

def observedWidthPin (j : Fin (es.length+1)) (r:Role) (b : Fin W) : V :=
  .inr (.inr (.inr (row j r,b.castLE narrow)))

local notation "pin" => observedWidthPin (Ex:=Ex) (Se:=Se) (Data:=Data) es maximum g work G inside shelf narrow

def observedTimeGuard (data : Fin N→V) := timeGuard (F:=F) cap es fits pin data

/-- True native words, measured for the signed calendar state at each date,
are read at their dense original slots. This equality holds on all common
data assignments, including a positive bit attempted on an unused role. -/
theorem observedTimeGuard_value {K : ℕ} (slot : Event→Slot X) (wire:X→Widths K)
    (cells:∀x,((s:Fin K)×SiteBit (wire x) s)↪Q) (start:X) (path:Path slot es start)
    (final : Memory G.W) (data : Fin N→V) (volts : V→Bool) (history : Fin N→Bool)
    (dense : ∀j r,(G.addr (row j r)).val=g.roleStart work j+1+(shelf r).val)
    (control : ∀j r b,volts (pin j r b)=G.terminal final (row j r,b.castLE narrow))
    (datum : ∀i,volts (data i)=history i)
    (bound : ∀j r,(final (g.roleStart work j+1+(shelf r).val)).val≤ maximum)
    (state : ∀j (q:Q),q∈Set.range (cells (boundaryState slot es start path j)) ↔
      q.2.val<(final (g.roleStart work j+1+(shelf q.1).val)).val) :
    TypedWiring.value (observedTimeGuard (F:=F) es cap maximum covers g work G inside shelf narrow data) volts =
      if ∀i,history i=true→i∈Set.range (timelineFin slot wire cells es start path) then 1 else 0 := by
  let words (j:Fin (es.length+1)) (r:Role):Word W :=
    WideParent.column maximum (final (g.roleStart work j+1+(shelf r).val))
  have shape (j) (r): (words j r).val=(final (g.roleStart work j+1+(shelf r).val)).val:=
    WideParent.column_read _ _ (bound j r)
  have read (j) (r) (b : Fin W) : volts (pin j r b) = TraceWords.bits (words j r) b := by
    rw [control]
    change (final (G.addr (row j r)).val).val.testBit b.val=(words j r).val.testBit b.val
    rw [dense,shape]
  rw [observedTimeGuard,timeGuard_value cap es fits pin data slot wire cells start path volts words read
    (fun j q=>(state j q).trans (by rw [shape]))]
  simp_rw [datum]

end WireTelescope.CalendarTape
end Hierarchy

end
end OAI
