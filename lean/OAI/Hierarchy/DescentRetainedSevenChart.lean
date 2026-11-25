import OAI.Hierarchy.DescentResetRetainedChart
import OAI.Hierarchy.DescentRetainedControlChart
import OAI.Hierarchy.DescentRetainedTargetPlacementChart

namespace OAI
/-! # Shared address chart of the filtered, chronologically ordered reset argument books -/
namespace Hierarchy.DescentRetainedSeven
open DescentResetRetainedSetup DescentResetRetainedPlacement
structure Chart where
  retained : Layout
  placement : DescentResetRetainedPlacement.Chart
  degree : ℕ
  capacity : ℕ
  packetBits : ℕ
  packetLanes : ℕ

namespace Chart
noncomputable section
variable (c : Chart)
def control : DescentRetainedControl.Layout:=
  ⟨c.retained.hosts,c.retained.grouped,c.placement.shapes,c.retained.donors,c.degree,c.capacity,
    c.packetBits,c.retained.bits,c.packetLanes,c.retained.decodedLanes⟩
def seen (floor : ℕ) := c.retained.tables floor
def tabs (floor : ℕ) :=c.control.endAddress (c.seen floor)
def lookup (floor : ℕ) := c.tabs floor+
  (c.retained.channels+1)*2^((c.retained.siteWord+c.retained.stripWord)*c.retained.decodedLanes)
def place (floor : ℕ) :=c.lookup floor+c.retained.outputs*2^(c.retained.siteWord*c.retained.decodedLanes)
def batch : Batch:=⟨c.retained.outputs,c.retained.bits,c.retained.decodedLanes⟩
def endAddress (floor : ℕ) :=DescentRetainedTargetPlacement.Chart.endAddress c.placement c.batch (c.place floor)
def bank (floor : ℕ) (f : Fin c.retained.outputs) (x : Fin c.placement.blocks) :=
  DescentRetainedTargetPlacement.Chart.bank c.placement c.batch (c.place floor) f x

theorem affine (floor : ℕ) : c.endAddress floor=floor+c.endAddress 0:=by
  have moved : c.retained.tables floor=floor+c.retained.tables 0:=by
    simp only [DescentResetRetainedSetup.Layout.tables,DescentResetRetainedSetup.Layout.mixed,DescentGLPacked.BankImage.SignedFields.stop,
      DescentGLPacked.BankImage.Dated.extent,DescentResetRetainedSetup.Layout.matrix,DescentResetRetainedSetup.Layout.slots,
      DescentResetRetainedSetup.Layout.digits,Nat.zero_add,Nat.add_assoc]
  unfold endAddress
  rw [DescentRetainedTargetPlacement.Chart.affine c.placement c.batch (c.place floor),
    DescentRetainedTargetPlacement.Chart.affine c.placement c.batch (c.place 0)]
  unfold place lookup tabs seen
  rw [c.control.translate (c.retained.tables floor), c.control.translate (c.retained.tables 0), moved]
  omega
end
end Chart
end Hierarchy.DescentRetainedSeven

end OAI
