import OAI.Hierarchy.DescentRetainedSevenChart
import OAI.Hierarchy.DescentOperandPublicCasts
import OAI.Hierarchy.DescentOperandPreparedPacketPhase
import OAI.Hierarchy.DescentResetRetainedChart
import OAI.Hierarchy.DescentResetRetainedPlacementChart

namespace OAI
/-! # Public addresses of the reset operand preparation passes -/
namespace Hierarchy.DescentResetOperandSetup
noncomputable section
structure Chart where
  retained : DescentResetRetainedSetup.Layout
  placement : DescentResetRetainedPlacement.Chart
  packets : DescentOperandRootPull.Pair
  publicCasts : DescentOperandPublicCasts.Plan
  oldDegree : ℕ
  oldCap : ℕ
  oldPieces : ℕ
  signedBits : ℕ
  signedLanes : ℕ
  ticketBits : ℕ
  fieldBits : ℕ
  queryBits : ℕ
  rotorBits : ℕ
  fallbackBits : ℕ
  fallbackInputs : ℕ

namespace Chart
variable (C : Chart)
def lanes := C.placement.lanes
def members := C.retained.args*C.retained.nodes
def strip := C.retained.donors*(2*C.oldCap)
def inputs := 6+2*C.strip
def seven : DescentRetainedSeven.Chart :=
  ⟨C.retained,C.placement,C.oldDegree,C.oldCap,C.packets.oldBits,C.packets.beforeLanes⟩
def retainedFields : DescentResetRetainedPlacement.Batch := C.seven.batch
def signedFields : DescentResetRetainedPlacement.Batch :=⟨C.strip,C.signedBits,C.signedLanes⟩
/-- Both the previous-node data and the earlier signed panel are moved into
the current compact host and block order before they are read together. -/
def placed (base : ℕ) := C.placement.endAddress C.signedFields (C.seven.endAddress base)
theorem placed_shift (base : ℕ) : C.placed base=base+C.placed 0 :=by
  rw [placed,placed,C.placement.affine _ (C.seven.endAddress base),C.placement.affine _ (C.seven.endAddress 0),
    C.seven.affine base]
  omega
def packetEnd (base : ℕ) := C.packets.endAddress (C.placed base)
def publicEnd (base : ℕ) :=C.publicCasts.endAddress (C.packetEnd base)
def sourceWidth := max C.retained.bits (max 1 (max C.signedBits C.ticketBits))
def casts (base : ℕ) :=C.publicEnd base+C.inputs*(2*2^(C.sourceWidth*C.lanes))
def words (K n a M : ℕ) := (n+K)*(2*2^((a*n+a)*M))
def find (base : ℕ) :=C.casts base+words 1 C.inputs C.fieldBits C.lanes
def slices (base : ℕ) :=C.find base+words 2 C.inputs C.fieldBits C.lanes
def rotorQuery (base : ℕ) :=C.slices base+10*2^((C.fieldBits+2)*C.lanes)
def rotorFields (base : ℕ) :=C.rotorQuery base+words C.members 4 C.rotorBits C.lanes
def fallbackQuery (base : ℕ) :=C.rotorFields base+words (7*C.members) 4 C.rotorBits C.lanes
def fallbackFields (base : ℕ) :=C.fallbackQuery base+words C.members C.fallbackInputs C.fallbackBits C.lanes
def endAddress (base : ℕ) :=C.fallbackFields base+words (7*C.members) C.fallbackInputs C.fallbackBits C.lanes

theorem affine (base : ℕ) : C.endAddress base=base+C.endAddress 0 :=by
  change C.packets.endAddress (C.placed base)+C.publicCasts.words+_+_+_+_+_+_+_+_=
    base+(C.packets.endAddress (C.placed 0)+C.publicCasts.words+_+_+_+_+_+_+_+_)
  rw [C.packets.extent (C.placed base),C.packets.extent (C.placed 0),C.placed_shift base]
  omega

theorem order (base : ℕ) :
    C.publicEnd base≤C.casts base ∧ C.casts base≤C.find base ∧ C.find base≤C.slices base ∧
    C.slices base≤C.rotorQuery base ∧ C.rotorQuery base≤C.rotorFields base ∧
    C.rotorFields base≤C.fallbackQuery base ∧ C.fallbackQuery base≤C.fallbackFields base ∧
    C.fallbackFields base≤C.endAddress base := ⟨Nat.le_add_right ..,Nat.le_add_right ..,Nat.le_add_right ..,
      Nat.le_add_right ..,Nat.le_add_right ..,Nat.le_add_right ..,Nat.le_add_right ..,Nat.le_add_right ..⟩

end Chart
end
end Hierarchy.DescentResetOperandSetup

end OAI
