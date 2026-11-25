import OAI.Hierarchy.DescentPhysicalOrdinaryReturn

namespace OAI
/-! # A numerical description of the returned venue, node headers and argument banks -/
namespace Hierarchy.DescentSixParty.Chronology
open DescentDatedAddressBook DescentSIMDLookup ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure
noncomputable section
set_option quotPrecheck false

structure ReturnProgram where
  venue : StageVenueTail.Date
  sources : StageVenueTail.Sources
  metadata : MetadataReturn
  resolver : DescentDatedPriorOperand.Layout
  rasterEnd : ℕ
  vectorBase : ℕ
  resolvedBase : ℕ

namespace ReturnProgram
variable (p : ReturnProgram)
local notation "r" => p.resolver
local notation "size_" => (r).size+2
local notation "meta" => p.metadata
local notation "base" => p.venue.endAddress p.rasterEnd
local notation "seven" => (meta).ordinaryEnd base
local notation "venue" => p.venue.phase p.sources p.rasterEnd

def node : DescentDatedNodeMetadata.Chart :=
  ⟨(r).blocks,(r).nodes,(r).hosts,(r).groups,(meta).chart.bits,(r).lanes⟩
def finished : DescentOrdinaryFinal.Chart:=⟨r,(meta).chart.bits,(meta).chart.bits⟩
def «fields» : p.finished.Sources:=
  ⟨p.resolvedBase,p.vectorBase,p.node.bank
    (p.node.inputsEnd (p.node.digitEnd base size_) (meta).paidBits size_)⟩
def paid : p.node.Counts:=fun x=>p.venue.metadataPaid p.sources x.val
def spans : p.node.Vectors (r).operands:=fun x j=>
  DescentDatedPriorOperand.previousBank r p.vectorBase x (DescentOperandStateBanks.page 6 j)

def instructions (w : ℕ) : Procedure w:=
  (((venue w).program.seq (p.node.ordinaryProgram base (meta).paidBits size_ w p.paid p.spans)).seq
    (p.finished.program p.fields seven w))
def clock (w : ℕ) :=
  (venue w).ticks+p.node.ordinaryTime base (meta).paidBits size_ p.paid p.spans+p.finished.ticks p.fields seven
end ReturnProgram

namespace PhysicalOrdinary
variable {F P : Type} [Field F] (v : PhysicalOrdinary F P) (floor : ℕ) (B : StageVenueTail.Sources)

def returnProgram : ReturnProgram :=
  ⟨v.venue,B,v.metadata,v.resolver,v.rasterEnd floor,v.vectorOutput floor,v.normalizedEnd floor⟩

theorem return_program_eq (w : ℕ) (safe : v.ResultRoom floor B w) :
    (v.returnPhase floor B w safe).program=(v.returnProgram floor B).instructions w ∧
    (v.returnPhase floor B w safe).ticks=(v.returnProgram floor B).clock w :=⟨rfl,rfl⟩

end PhysicalOrdinary
end
end Hierarchy.DescentSixParty.Chronology

end OAI
