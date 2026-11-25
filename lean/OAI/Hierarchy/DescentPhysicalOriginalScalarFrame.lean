import OAI.Hierarchy.DescentPhysicalPrivatePanelCapture

namespace OAI
/-! # Compact auxiliary words survive the private, mixed and stem-coordinate scans -/
namespace Hierarchy.DescentDatedAddressBook.PhysicalReset.DateInputs
open DescentSixParty.Chronology DescentPackedZip ProtocolRAM
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
noncomputable section
set_option quotPrecheck false
variable {a : PhysicalReset} {floor w : ℕ} (u : a.DateInputs floor w)
local notation "v₀" => a.successor
local notation "b₀" => a.rebased floor
local notation "s₀" => (v₀).sheets
local notation "base₀" => ((v₀).remap b₀).endAddress

def coordinateResult (m : Memory w) : Memory w :=
  (s₀).stemSources.image ((s₀).metaEnd base₀) (u.masked.image (u.privateResult m))

theorem coordinateResult_frame (m : Memory w) (ok : u.Ready)
    (space : (s₀).coordinateEnd base₀<2^w) (z : ℕ) (hz : z<(v₀).jointEnd b₀) :
    u.coordinateResult m z=u.privateStart m z:=by
  have fit:=(v₀).private_inputs_fit b₀ u.earlier ok.pages ok.privates
  have keep:=(v₀).private_any b₀ u.earlier (u.privateStart m) ok.projectionLanes ok.projectionBlocks fit ok.privates
  have mixed:=u.masked.any (u.privateResult m) (u.genuine_mask_previous ok.joints ok.masked) ok.masked
  have root:=((v₀).privateShape.cuts ((v₀).jointEnd b₀))
  have left : z<u.masked.first:=hz.trans_le (root.1.trans root.2)
  have small : z<(s₀).metaEnd base₀:=by
    rw [←u.masks_end]
    exact left.trans_le (u.masked.ordered.1.trans u.masked.ordered.2)
  exact (((s₀).stemSources.any ((s₀).metaEnd base₀) _ space).2.2 z (.inl small)).trans
    ((mixed.2.2 z (.inl left)).trans (keep.2 z (.inl hz)))

end
end Hierarchy.DescentDatedAddressBook.PhysicalReset.DateInputs

end OAI
