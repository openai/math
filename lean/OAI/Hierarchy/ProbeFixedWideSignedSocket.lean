import OAI.Hierarchy.ProbeFixedWidePacketFields
import OAI.Hierarchy.TaggedWireSignedSocketKey
import OAI.Hierarchy.TaggedWidePacketWantedRead

namespace OAI
/-! # The actual emitted neighbor key on a signed packet input half-chord -/
noncomputable section
set_option quotPrecheck false
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open LinearAlgebra.SpectralBooks SiteTensor ChordGraph
open Computability.VPVNP.BurstRAM PrivateRAM ProbeStage CoreBoard HistoryRoles WireTelescope PacketNeighbor PacketTurns Tagged
open scoped Classical Fin.CommRing
variable {F : Type} [Field F] {k : ℕ} {p q Q σ Λ : ℝ} (v : FixedProtocolFormat F k p q Q σ Λ)
    (h width bits : ℕ) (a : Attempt) (siteROM : ℕ) (stride : Bank) (preStart postStart : ℕ)
local notation "P" => v.widePlacement h width
local notation "party" => v.wideBallotSite P h width siteROM a
local notation "L" => v.wideBallotParties h a
local notation "D" => v.widePacketDegree
local notation "D0" => (v.wideBallotShape P h width (.attempt a)).columns+((v.widePacketRoles h*3)*5+(D+D))
local notation "fields" => v.widePacketFields h width bits (.attempt a) siteROM stride preStart postStart
local notation "sheet" => DatedRoleSheets.bank (v.widePacketPhysical h width) preStart (v.widePacketShelf h) bits

variable {S cap W : ℕ} (place : Fin (v.wideBallotParties h a) ↪ Fin S)
    (i : Fin (v.wideBallotParties h a)) {total : (portGraph S).Port (place i) → ℕ}
    (parts : PassiveWindow.Parts ((portGraph S).Port (place i)) (Fin v.widePacketDegree) cap total)
    (mem : Memory W) (reg : Word W)
    (measured : ∀ j, (v.wideBallotSite (v.widePlacement h width) h width siteROM a j).eval mem reg =
      ((place j).val : Word W)) (room : S ≤ 2^W)
    (actual : NeighborReads mem reg parts
      (pageRead (DatedRoleSheets.bank (v.widePacketPhysical h width) preStart (v.widePacketShelf h) bits 0) stride
        (v.wideBallotSite (v.widePlacement h width) h width siteROM a i))
      (pageRead (DatedRoleSheets.bank (v.widePacketPhysical h width) preStart (v.widePacketShelf h) bits 2) stride
        (v.wideBallotSite (v.widePlacement h width) h width siteROM a i)))

include measured room actual

/-- The same native key covers each alias of the opposite party. If it has no
active lane in the original bank, the numeric result is the public sentinel D. -/
theorem wide_socket_at (socket : (portGraph L).Port i) :
    ((fields).value i ((Fin.natAdd D0 (other socket)).castAdd (PacketTurns.middleColumns (v.widePacketRoles h)))).eval mem reg=
      (index parts (other (liftPort place socket)):Word W) := by
  have socketKey := congrArg (fun e : Expr => e.eval mem reg)
    (v.widePacket_socket h width bits siteROM stride preStart postStart a i (other socket))
  rw [lift_other]
  exact socketKey.trans (key_read parts _ _ mem reg actual _ _ room (measured (other socket)))

theorem wide_socket_live (socket : (portGraph L).Port i) (live : 0<total (liftPort place socket)) :
    ∃q:Fin D,((fields).value i ((Fin.natAdd D0 (other socket)).castAdd (PacketTurns.middleColumns (v.widePacketRoles h)))).eval mem reg=(q.val:Word W) ∧
      parts.owner q=some (liftPort place socket) ∧ 0<parts.width q := by
  obtain ⟨q,key,own,on⟩:=found_live parts _ live
  exact ⟨q,(v.wide_socket_at h width bits a siteROM stride preStart postStart place i parts mem reg measured room actual socket).trans
    (congrArg (fun n:ℕ=>(n:Word W)) key.symm),own,on⟩

theorem wide_socket_empty (socket : (portGraph L).Port i) (off : total (liftPort place socket)=0) :
    ((fields).value i ((Fin.natAdd D0 (other socket)).castAdd (PacketTurns.middleColumns (v.widePacketRoles h)))).eval mem reg=(D:Word W) := by
  rw [v.wide_socket_at h width bits a siteROM stride preStart postStart place i parts mem reg measured room actual,
    key_empty parts _ off]

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat

end
end OAI
