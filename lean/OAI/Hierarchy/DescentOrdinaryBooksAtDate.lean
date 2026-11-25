import OAI.Hierarchy.DescentDatedRegisterState
import OAI.Hierarchy.DescentOrdinaryTicketChart
import OAI.Hierarchy.DescentDatedPrimitivePitch
import OAI.Hierarchy.DescentDatedOperandRootSize
import OAI.Hierarchy.DescentDatedOriginMouth
import OAI.Hierarchy.DescentResetRetainedCalendarWidths
import OAI.Hierarchy.DescentDatedOrdinaryRasterExtent

namespace OAI
/-! # Public operand, newborn and metadata layouts on the ordinary calendar -/
namespace Hierarchy.DescentSixParty.Chronology
open DescentDatedAddressBook DescentSIMDLookup DescentOperandVectorArena
open DescentPacking.PackedMatch.Local
noncomputable section

namespace OrdinaryBooks
variable {F : Type} [Field F] (G : PoweredGadget F) (S : DescentCompiler.AtomSchedule) (op : RotorSpec)

/-- Construct the finite books before pricing the two physical pitches. The
incoming archive supplies its actual node and operand multiplicities. -/
def atDate (gain k age p tail drift degree payload seats : ℕ) (prior : DatePorts) : OrdinaryBooks :=
  let date := DonorDate.atDate G S gain k age p
  let census := S.censusBits p
  let area := date.schedule payload seats census
  let slots := max prior.argumentsPerNode (S.retainedArgumentsAt G drift)
  let nodes := S.retainedNodes
  let size := DescentOperandWidth.recordBits G S k tail drift degree p - 2
  let width := size+2
  let low := StageVenueTail.OrdinaryRaster.shapes area
  let groups := S.groupCount (age+1)
  let lanes := area.lanesAt
  let resolver : DescentDatedPriorOperand.Layout :=
    ⟨2^k,nodes,slots,date.hosts*low,groups,lanes,size⟩
  let vector : DescentOperandVectorArena.Layout :=
    ⟨slots,0,0,date.hosts,low,groups,2^k,lanes,width*nodes⟩
  let metadata : MetadataReturn :=
    ⟨⟨2^k,nodes,resolver.hosts,groups,width,lanes⟩,census,width⟩
  { reference := ⟨0,date.degree,k,prior.nodes,nodes,date.cap,width,
      Nat.clog 2 (low+1),Nat.clog 2 (prior.nodes+1),lanes⟩
    bornBook := ⟨2^k,date.cap,date.format.names,date.format.widths,width,slots,
      date.hosts,date.groups,lanes,p,date.grain,G.b⟩
    ingressWords := 0
    vector := vector
    resolver := resolver
    origin := ⟨0⟩
    palette := DescentOrdinaryPalette.Configuration.atOrdinary G S op p payload
      date.degree k date.cap prior.nodes nodes prior.roleLanes
    metadata := metadata
    operandBook := ⟨resolver,width,width⟩ }

theorem atDate_layout (gain k age p tail drift degree payload seats : ℕ) (prior : DatePorts) :
    let b := atDate G S op gain k age p tail drift degree payload seats prior
    b.vector.operands=max prior.argumentsPerNode (S.retainedArgumentsAt G drift) ∧
      b.reference.oldNodes=prior.nodes ∧ b.reference.newNodes=S.retainedNodes ∧
      b.bornBook.grain=p ∧ b.bornBook.scale=S.grainAt G.b p age ∧
      b.resolver.hosts=b.vector.hosts*b.vector.lows ∧ b.resolver.operands=b.vector.operands ∧
      b.operandBook.layout=b.resolver := by
  exact ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

/-- The fragment codec reserves two tag bits. All its short columns use
the very same field width as the seed and the reset operand stores. -/
theorem record_width (gain k age p tail drift degree payload seats : ℕ) (prior : DatePorts) :
    let b := atDate G S op gain k age p tail drift degree payload seats prior
    b.resolver.size+2=DescentOperandWidth.recordBits G S k tail drift degree p ∧
      b.reference.bits=b.resolver.size+2 ∧ b.bornBook.bits=b.resolver.size+2 ∧
      b.metadata.spanBits=b.resolver.size+2 := by
  have h : 2≤DescentOperandWidth.recordBits G S k tail drift degree p := by
    exact (Nat.le_max_left 2 _).trans (Nat.le_max_left _ _)
  exact ⟨Nat.sub_add_cancel h,rfl,rfl,rfl⟩

end OrdinaryBooks

namespace PhysicalOrdinary
variable {F P : Type} [Field F] (v : PhysicalOrdinary F P)

/-- Install the extent of the three input publishers after their physical
pitches have been selected. The three counts use only earlier public layouts. -/
def withOriginReservation : PhysicalOrdinary F P :=
  {v with origin:=⟨v.originControlWords+v.originMouthWords+v.rootSourceSize⟩}

theorem origin_reservation :
    v.withOriginReservation.origin.preparationWords=
      v.withOriginReservation.originControlWords+v.withOriginReservation.originMouthWords+
        v.withOriginReservation.rootSourceSize := rfl

end PhysicalOrdinary
end
end Hierarchy.DescentSixParty.Chronology

end OAI
