import OAI.Hierarchy.DescentOriginalPeerRegions
import OAI.Hierarchy.DescentDatedReturnMetadata
import OAI.Hierarchy.DescentPrimitiveCheckpointShape
import OAI.Hierarchy.DescentPrimitiveBirthLayout

namespace OAI
/-! # Paid widths and dimensions of the returned node, role, and argument fields -/
namespace Hierarchy.DescentDatedAddressBook.ResetOutput
open DescentCompiler DescentCompiler.TerminalScale DescentSixParty Filter
noncomputable section
set_option quotPrecheck false
variable {ι : ℕ→Type*}
structure PublishedRegisters (p : ∀h,ι h→ResetOutput) : Prop where
  primitive : DescentResetPrimitiveCheckpoint.Shape.ScalarRoom (fun h i=>(p h i).primitive)
  birth : DescentPrimitiveBirth.Layout.ScalarRoom (fun h i=>(p h i).birth)
  metadata : MetadataReturn.ScalarRoom (fun h i=>(p h i).metadata)
  «arguments» : Bounded (fun h i=>(p h i).argumentSlots)
  «fields» : Bounded (fun h i=>(p h i).receiver.fields)
  cap : Bounded (fun h i=>(p h i).receiver.capacity)
  keepDigits : ∀ᶠ h:ℕ in atTop,∀i,(p h i).setup.fieldBits*(p h i).receiver.lanes≤h
  jointDigits : Bounded (fun h i=>2^(p h i).sheets.metaBits)
  controlDigits : ∀ᶠ h:ℕ in atTop,∀i,let c:=(p h i).controlRegisters;c.bits+c.dims.lanes≤h
  rankKey : ∀ᶠ h:ℕ in atTop,∀i,let v:=p h i;(v.assemblerBits*5+v.assemblerBits*5)*v.receiver.lanes≤h
  dictionaries : ∀ᶠ h:ℕ in atTop,∀i,let v:=p h i;let m:=v.middle;let a:=v.receiver
    (m.signedBits*m.oldBlocks+m.signedBits)*m.signedLanes≤h ∧ m.projectBits*m.rootLanes≤h ∧
    (8*a.signedBits+a.signedBits)*a.lanes≤h ∧ (a.queryBits+a.signedBits)*a.lanes≤h ∧
    (v.ticketBits*5+v.ticketBits*5)*a.lanes≤h ∧ (v.assemblerBits*7+v.assemblerBits)*a.lanes≤h ∧
    (v.assemblerBits*7+v.sourceWordBits)*a.lanes≤h ∧ (DescentResetSourceSeekRAM.keyBits 4 a.candidates+v.sourceValueBits)*a.lanes≤h

end
end Hierarchy.DescentDatedAddressBook.ResetOutput

end OAI
