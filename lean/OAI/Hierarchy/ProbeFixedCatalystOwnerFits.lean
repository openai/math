import OAI.Hierarchy.ProbeFixedCatalystBirth
import OAI.Hierarchy.ProtocolRAMCatalystLedgerFit
import OAI.Hierarchy.ProtocolRAMCoreRouteSafe

namespace OAI
/-! # Bounds on the native owner expression at every chronological event -/

noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage CoreBoard StripChart StripDirectory CatalogueRows
open BoughtSockets CoreRoute
open scoped Classical Fin.CommRing

variable {F : Type*} [Field F] {k : ℕ} {p q Q σ Λ : ℝ} (v : FixedProtocolFormat F k p q Q σ Λ)
variable (z width K G H R : ℕ) (b : JointHeader.Board) (cat : CatalogueRows.Board)
set_option quotPrecheck false
local notation "n" => (v.mesh.inject+v.mesh.cool)*v.mesh.outerFuel
variable (sockets : BoughtSockets.Directory ((v.mesh.inject+v.mesh.cool)*v.mesh.outerFuel))
local notation "P" => v.catalystPlacement z K G H R b cat sockets
local notation "s" => v.nativeBoards P z width
local notation "A" => v.privateArena P z width
local notation "bits" => Native.wordBits z (2^v.W) Native.copies
local notation "endCore" => CoreRoute.stop v.sampler z v.W k n v.depth K G H R

/-- The original ROM and shelf bank arguments are below the actual landing
address of their own event. A feed instruction's owner is the literal zero. -/
theorem catalyst_owner_fits (ownerArea : Arena) (core : endCore≤b.initial)
    (room : (A).endAddress v.mesh<2^bits) (e : Event) (occurs : e∈events v.mesh) :
    ((ownerLedger s v.mesh cat (P).routes F ownerArea).term e).Fits bits ((A).base v.mesh e) := by
  cases e with
  | feed i => trivial
  | attempt a =>
    let landing:=(A).base v.mesh (.attempt a)
    have first : (A).first≤landing := Nat.le_add_right ..
    have coreRoom : endCore≤landing := core.trans ((v.catalyst_initial_le_first P z width).trans first)
    have word : landing<2^bits := (Nat.le_add_right ..).trans_lt (((A).within v.mesh _ occurs).trans_lt room)
    obtain ⟨columns,cover⟩:=CoreRoute.column_bounds v.sampler z v.W k n v.depth K G H R landing coreRoom
    apply ledger_attempt_fits s v.mesh cat (P).routes F ownerArea a landing word columns cover
    · have headerEnd := congrArg StockCommit.PortHeader.stop (v.catalyst_header P z width a).symm
      exact headerEnd.le.trans (((v.publicHeader P z width).ports.end_le 0).trans
        ((v.catalyst_ports_le_first P z width).trans first))
    · cases a with
      | outer phase trial => trivial
      | inner phase trial layer tick =>
        have keys : (Public.keyHead v.sampler (P).routes.column z v.W k v.depth).stop≤endCore :=
          (Public.borders v.sampler (P).routes.column z v.W k n v.depth).2.trans (Nat.le_add_right ..)
        exact ⟨keys.trans coreRoom,v.catalyst_bought_stage_room P z width phase trial layer tick⟩

/-- The argument expected by the counted owner extraction loop, in its native clock order. -/
theorem catalyst_owner_args (ownerArea : Arena) (core : endCore≤b.initial) (room : (A).endAddress v.mesh<2^bits)
    (i : Fin (events v.mesh).length) :
    ((ownerLedger s v.mesh cat (P).routes F ownerArea).term ((events v.mesh).get i)).Fits bits
      ((A).base v.mesh ((events v.mesh).get i)) :=
  v.catalyst_owner_fits z width K G H R b cat sockets ownerArea core room _ (List.get_mem ..)

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
