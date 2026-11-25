import OAI.Hierarchy.DescentResetTerminalRegisterLayout
import OAI.Hierarchy.DescentPhysicalResetDateVenue
import OAI.Hierarchy.DescentTerminalPreflightPointerPages

namespace OAI
/-! # Terminal pointer and token banks at the physical reset's actual endpoints -/
namespace Hierarchy.DescentDatedAddressBook
open DescentSixParty DescentSIMDLookup DescentPackedColony DescentColonies ProtocolRAM
open Computability.VPVNP.BurstRAM PrivateRAM
noncomputable section
set_option quotPrecheck false

namespace ResetOutput
variable (v : ResetOutput) (base : ℕ)

def terminalRole (x : Fin v.primitive.chart.blocks) : Bank := v.primitive.bank (v.birthEnd base) x

theorem terminal_role_room {w : ℕ} (space : v.metadataEnd base<2^w) (x : Fin v.primitive.chart.blocks) :
    (v.terminalRole base x).Fits w (v.primitiveEnd base) ∧
    v.primitive.chart.rows≤(v.terminalRole base x).size :=
  v.primitive.bank_fits (v.birthEnd base) ((v.terminal_order base).2.2.trans_lt space) x
end ResetOutput

namespace PhysicalReset
variable {a : PhysicalReset} {floor w : ℕ} {u : a.DateInputs floor w} (z : u.FinalInputs)
local notation "v" => a.successor
local notation "b" => a.rebased floor
local notation "V" => (v).venue
local notation "next" => (V).next
local notation "fund" => (v).fundedEnd b
local notation "args" => (next).operands ((V).sources (FinalInputs.predecessor u) fund) ((V).venueStart fund)

/-- These are the written venue pages, with the old-block and signed slot coordinates retained. -/
def terminalWing (u : a.DateInputs floor w) (x : Block (next).k) (j : Fin (2*(next).cap)) : Bank :=
  ((next).operands ((V).sources (FinalInputs.predecessor u) fund) ((V).venueStart fund)).wire x.val j.val

theorem wing_room (room : z.Room) (x : Block (next).k) (j : Fin (2*(next).cap)) :
    (terminalWing u x j).Fits w ((v).fullEnd b) ∧
      (next).hosts*chunks (next).groups (next).lanes <= (terminalWing u x j).size :=
  (next).wire_room _ _ w x j room.successor.return_.roof

variable {F Pin : Type} [Field F] {d : ℕ} {sz : Pin→ℕ} {W : MarkedWorld F d Pin sz}
    {G : PoweredGadget F} {q ε : ℝ} {S : DescentCompiler.AtomSchedule} {age grain wire hist : ℕ}
    (r : Reached W G q ε S a.successor.venue.next.k age grain a.successor.venue.next.degree wire hist)
    (wide : Fintype.card r.V ≤ a.successor.venue.next.hosts)
local notation "hosts" => r.vertex.trans (Fin.castLEEmb wide)

theorem terminal_signed (room : z.Room) {m mid dst : Memory w}
    («prefix» : u.throughOperandDate.Runs m mid) (run : (date z).Runs m dst)
    (groups : S.groupCount age=(next).groups) (cap : r.placement.cap=(next).cap)
    (issued : stageVenue r wide args (next).lanes (next).paidBits ((v).fullEnd b) (r.venueRoster wide) (z.venueImage mid))
    (lanes : (next).lanes=S.groupCount age) (x : Block (next).k) (j : Fin (2*r.placement.cap)) :
    Reads (terminalWing u x (j.cast (congrArg (2*·) cap))) (fun h g=>
      DescentSignedCableCodec.encode (DescentPacking.PackedMatch.Local.Stage.Prepare.signed r.placement
        (r.order.trans Fin.valEmbedding) S r.valid (Function.Embedding.refl _) hosts x j h g))
      (S.groupCount age) dst := by
  have receipt:=date_venue z r wide room «prefix» run groups cap issued
  simpa [terminalWing, lanes] using receipt.2.2.2.1 x j

/-- The tail writes above the packed raw operand array. Thus every genuine pre-tail
source survives even if an unrelated field on the same page has an arbitrary value. -/
theorem terminal_operand (room : z.Room) {m mid dst : Memory w}
    («prefix» : u.throughOperandDate.Runs m mid) (run : (date z).Runs m dst)
    (f : Fin 7) (j : Fin (v).argumentSlots) (x : Fin (v).receiver.blocks) {s : ℕ}
    (words : Fin (v).receiver.hosts→Fin (v).receiver.groups→Cell s)
    (posted : Reads ((v).terminalField b f j x) words (v).receiver.lanes mid) :
    Reads ((v).terminalField b f j x) words (v).receiver.lanes dst := by
  obtain ⟨end_,tail,_,same,_⟩:=z.tail_visible room mid
  have eq:=exec_unique _ m dst end_ run («prefix».then tail)
  obtain ⟨fits,size⟩:=(v).terminal_field_room b room.endFits f j x
  intro p
  have i:= (row _ _ _ p).isLt
  have lo:=fits.2.2
  have idx:((v).terminalField b f j x).base + (row _ _ _ p).val < (v).finalEnd b := by omega
  exact (congrFun eq _).trans ((same _ (.inl idx)).trans (posted p))

end PhysicalReset
end
end Hierarchy.DescentDatedAddressBook

end OAI
