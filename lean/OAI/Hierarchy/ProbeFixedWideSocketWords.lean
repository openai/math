import OAI.Hierarchy.ProbeFixedWideSignedSocket
import OAI.Hierarchy.TaggedWideSelectedSocket

namespace OAI
/-! # Each native signed key field is exactly the selected original chord bucket -/
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

include measured room actual in
theorem wide_signed_key {digits : ℕ} (wide : D<2^digits) (j : Fin L) :
    ((fields).value i ((Fin.natAdd D0 j).castAdd (PacketTurns.middleColumns (v.widePacketRoles h)))).eval mem reg=
      ((signedKey place i parts wide j).val:Word W) := by
  have socketKey := congrArg (fun e : Expr => e.eval mem reg)
    (v.widePacket_socket h width bits siteROM stride preStart postStart a i j)
  exact socketKey.trans (key_read parts _ _ mem reg actual _ (place j) room (measured j))

include measured room actual in
theorem wide_signed_key_bit {digits : ℕ} (wide : D<2^digits) (full : D<2^W) (j : Fin L) (b : Fin digits) :
    (((fields).value i ((Fin.natAdd D0 j).castAdd (PacketTurns.middleColumns (v.widePacketRoles h)))).eval mem reg).val.testBit b.val=
      (signedKey place i parts wide j).val.testBit b.val := by
  rw [v.wide_signed_key h width bits a siteROM stride preStart postStart place i parts mem reg measured room actual wide j]
  change ((index parts (place j) : Word W).val).testBit b.val =
    (index parts (place j)).testBit b.val
  rw [Fin.val_cast_of_lt ((index_le parts (place j)).trans_lt full)]

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
