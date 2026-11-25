import OAI.Hierarchy.DescentPreparedPrivateRoots

namespace OAI
/-! # The physically saved reset permutation word remains addressable past all root pages -/
namespace Hierarchy.DescentFallbackPeriod.Projected.Receiver
open DescentSIMDLookup DescentSixParty.Chronology DescentSixParty.Chronology.Shelf
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
noncomputable section
variable {D cap N n r c H G K R M h l t field Ht w : ℕ}
    (a : Receiver D cap N n r c H G K R M h l t field Ht w) (b : RootBook n r D (2^r) cap field)

theorem saved_register_room (room : a.PreparedFits b) : a.saved.Fits w (a.preparedEnd b) :=by
  have join:a.retileEnd≤a.signedOrigin:=Nat.le_add_right ..
  have sign:a.signedOrigin≤a.signedEnd:=DescentGLPacked.BankImage.Dated.origin_le_endAddress _ _ _ _ _
  have proj:a.signedEnd≤a.projectionEnd:=Nat.le_add_right ..
  have h:=b.limits a.projectionEnd H (2^c) M
  have head:a.projectionEnd≤a.headerEnd b:=h.1.trans (h.2.1.trans h.2.2)
  have endAt:a.headerEnd b≤a.preparedEnd b:=Nat.le_add_right ..
  exact ⟨room.key.1,room.key.2.1,room.key.2.2.trans (join.trans (sign.trans (proj.trans (head.trans endAt))))⟩

end
end Hierarchy.DescentFallbackPeriod.Projected.Receiver

end OAI
