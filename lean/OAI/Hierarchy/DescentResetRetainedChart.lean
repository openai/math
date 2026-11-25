import OAI.Hierarchy.DescentRetainedOverlapSize
import OAI.Hierarchy.DescentResetRetainedDimensions
import OAI.Hierarchy.DescentDatedSignedArea
import OAI.Hierarchy.DescentOverlapTables

namespace OAI
/-! # Fiscal and physical layout for the retained reset operand decoder -/
namespace Hierarchy.DescentResetRetainedSetup
open DescentSIMDLookup DescentGLPacked.BankImage ProtocolRAM
noncomputable section

namespace Layout
variable (v : Layout)
def firstStep := counts v.hosts v.groups v.previousLanes v.gatherLanes v.wholeWord
def digits (base : ℕ) := base+v.sources*v.firstStep
def slots (base : ℕ) := v.digits base+v.previousNodes*2^(v.wholeWord*v.gatherLanes)
def matrix (base : ℕ) := v.slots base+v.blocks*(2*2^((v.bits*v.blocks+v.bits)*v.gatherLanes))
def mixed (base : ℕ) := SignedFields.stop (v.matrix base) v.channels v.hosts v.high v.low v.bits
def nextStep := counts v.hosts v.grouped v.matrixLanes v.decodedLanes v.stripWord
def tables (base : ℕ) := v.mixed base+v.channels*v.nextStep
/-- One SIMD join dictionary per original channel, sharing its shift page. -/
def decode (base : ℕ) := v.tables base+(v.channels+1)*2^((v.siteWord+v.stripWord)*v.decodedLanes)
def out (base : ℕ) := v.decode base+v.outputs*2^(v.siteWord*v.decodedLanes)
def reissue (base : ℕ) := v.out base+v.outputs*v.rows+2^Nat.clog 2 (v.rows+1)
def lastStep := counts v.hosts v.grouped v.decodedLanes v.emitLanes v.bits
def endAddress (base : ℕ) := v.reissue base+v.outputs*v.lastStep

theorem order (base : ℕ) : base≤v.digits base ∧ v.digits base≤v.slots base ∧
    v.slots base≤v.matrix base ∧ v.matrix base≤v.mixed base ∧ v.mixed base≤v.tables base ∧
    v.tables base≤v.decode base ∧ v.decode base≤v.out base ∧ v.out base≤v.reissue base ∧
    v.reissue base≤v.endAddress base := by
  refine ⟨Nat.le_add_right ..,Nat.le_add_right ..,Nat.le_add_right ..,?_,Nat.le_add_right ..,
    Nat.le_add_right ..,Nat.le_add_right ..,(Nat.le_add_right ..).trans (Nat.le_add_right ..),Nat.le_add_right ..⟩
  exact Dated.origin_le_endAddress ..

theorem affine (base : ℕ) : v.endAddress base=base+v.endAddress 0 :=by
  simp only [endAddress,reissue,out,decode,tables,mixed,SignedFields.stop,Dated.extent,matrix,slots,digits,Nat.zero_add,Nat.add_assoc]

theorem overlap_stop (base H G A B a : ℕ) : Overlap.endAddress base H G A B a=base+counts H G A B a :=by
  simp only [counts,Overlap.endAddress,Overlap.dest,Overlap.dictBase,Nat.zero_add,Nat.add_assoc]

end Layout
end
end Hierarchy.DescentResetRetainedSetup

end OAI
