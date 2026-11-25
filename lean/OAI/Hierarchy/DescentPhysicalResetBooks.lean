import OAI.Hierarchy.DescentPhysicalResetRankProgram
import OAI.Hierarchy.DescentResetNodeBooks
import OAI.Hierarchy.DescentPhysicalResetRoots
import OAI.Hierarchy.DescentPreparedPrivateRoots

namespace OAI
/-! # Mounted private roots and the complete next-stage operand books -/
namespace Hierarchy.DescentDatedAddressBook
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open DescentSixParty DescentSixParty.Chronology DescentFallbackPeriod
noncomputable section
set_option quotPrecheck false

namespace PhysicalReset
variable (a : PhysicalReset) (sh : a.StencilShape) (floor : ℕ) (count hub : Bank) (g Y : ℕ) (inputs : a.RootInputs)
local notation "v₀" => a.successor.middle
local notation "Q" w => a.rootPhase sh floor count hub g Y inputs w
variable (book : Projected.RootBook a.successor.middle.rotorBits a.successor.middle.rootDepth a.ports
  (2^a.successor.middle.rootDepth) (a.c/2) inputs.field)

set_option maxHeartbeats 800000 in
theorem prepared_end (shape : a.RootShape) (w : ℕ)
    (shapes : (v₀).rootShapes=book.shapes) (field : (v₀).rootField=inputs.field)
    (laws : (v₀).rootLawWidth=book.width (v₀).signedHosts (2^(v₀).stencil.c) (v₀).signedLanes) :
    (Q w).preparedEnd book=(v₀).stop (a.rebased floor) := by
  unfold Projected.Receiver.preparedEnd Projected.Receiver.headerEnd ResetMiddle.stop ResetMiddle.rootHeader
    RootTemplates.privateEnd
  rw [root_header_physical,a.projection_end sh floor count hub g Y inputs shape w,
    shape.hosts,shape.lanes,shape.groups,shape.degree,shapes,field,laws]

def throughPublishedRoots (src : Bank) (R δ w : ℕ) (safe : (Q w).PreparedFits book) :=
  (a.throughStencil sh floor count hub g Y src R δ w).seq ((Q w).preparedRoots book safe)

def throughPublishedTicks (R δ w : ℕ) (safe : (Q w).PreparedFits book) :=
  a.throughStencilTicks sh floor count hub g Y R δ w+(Q w).preparedTicks book safe

set_option maxHeartbeats 1000000 in
theorem throughPublished_any (src : Bank) (R δ w : ℕ) (safe : (Q w).PreparedFits book) (m : Memory w)
    (front : a.PrimeRoom floor src count R δ w) (middle : (a.stencilPhase sh floor count hub g Y).Room w) :
    ∃measured,(a.throughStencil sh floor count hub g Y src R δ w).Exec m measured
      (a.throughStencilTicks sh floor count hub g Y R δ w) ∧
      (a.throughPublishedRoots sh floor count hub g Y inputs book src R δ w safe).Exec m
        ((Q w).preparedImage book safe measured) (a.throughPublishedTicks sh floor count hub g Y inputs book R δ w safe) ∧
      CheapCode (a.throughPublishedRoots sh floor count hub g Y inputs book src R δ w safe) := by
  obtain ⟨_,measured,_,_,run,small⟩:=a.throughStencil_any sh floor count hub g Y src R δ w m front middle
  have rest:=(Q w).prepared_any book safe measured
  refine ⟨measured,@run,?_,?_⟩
  · exact Procedure.Exec.then (@run) (@rest.1)
  · exact @ProtocolRAM.cheap_seq w (a.throughStencil sh floor count hub g Y src R δ w)
      ((Q w).preparedRoots book safe) (@small) (@rest.2.1)
end PhysicalReset

namespace ResetOutput
variable (v : ResetOutput)
local notation "A" => v.receiver
variable (u : v.RankInputs) (s : v.OperandInputs) (base degree : ℕ)
local notation "L" => v.rankBook u base
local notation "r₀" => v.renderFromRanks u base
local notation "old" => v.operandDictionaryEnd base
variable (bank : v.setup.Sources) (laws : v.setup.Laws)
def retainedReturn (w : ℕ) :=
  (v.rankedReturn u s base degree bank laws w).seq (DescentResetNodeBooks.program (v.scalarEnd base) old v.nodeNames
    v.nodes (A).hosts (A).groups v.nodeBits (A).lanes w)
def retainedTime (w : ℕ) := v.rankedTime u s base degree bank laws w+DescentResetNodeBooks.ticks (v.scalarEnd base) old v.nodeNames
    v.nodes (A).hosts (A).groups v.nodeBits (A).lanes
def retainedMemory {w : ℕ} (m : Memory w) :=
  DescentResetNodeBooks.image (v.scalarEnd base) old v.nodeNames v.nodes (A).hosts (A).groups v.nodeBits (A).lanes
    (v.rankedMemory u s base degree bank laws m)

theorem retained_any {w : ℕ} (m : Memory w) (signedWidth : (A).signedBits=v.assemblerBits)
    (nodeCount : s.nodes=v.nodes) (slots : s.slots=v.argumentSlots) (portInputs : v.RankPortRoom base w) (reads : (L).Previous w)
    (controls : v.ControlRoom base bank w) (placed : v.setup.Ready bank w (v.operandFloor base)) (issued : v.OperandEarly s r₀ w base) (room : v.finalEnd base<2^w) :
    (v.retainedReturn u s base degree bank laws w).Exec m (v.retainedMemory u s base degree bank laws m) (v.retainedTime u s base degree bank laws w) ∧
    (∀i,i<v.candidateEnd base ∨ v.finalEnd base≤ i → v.retainedMemory u s base degree bank laws m i=m i) ∧
    CheapCode (v.retainedReturn u s base degree bank laws w) := by
  have slotsCount : (A).fields=v.nodeNames*v.nodes:=by simpa only [nodeCount,slots,nodeNames] using s.channels
  have srcRoom : old+(v.nodeNames*v.nodes)*DescentResetNodeBooks.rows (A).hosts (A).groups (A).lanes≤v.scalarEnd base := by
    change old+_≤old+(A).fields*_
    rw [slotsCount]; rfl
  have last:=v.final_ge base
  have first:=v.ranked_any u s base degree bank laws m signedWidth portInputs reads controls placed issued (last.trans_lt room)
  have second:=DescentResetNodeBooks.any (v.scalarEnd base) old v.nodeNames v.nodes (A).hosts (A).groups v.nodeBits (A).lanes
    (v.rankedMemory u s base degree bank laws m) srcRoom room
  have lo:v.candidateEnd base≤v.scalarEnd base:=by
    have a:=(L).ordered
    have b:=v.earlier base
    exact (v.rankPort_after base).trans ((((a.1.trans a.2.1).trans a.2.2.1).trans a.2.2.2).trans b.2.2)
  refine ⟨?_,?_,cheap_seq first.2.2 (DescentResetNodeBooks.cheap (v.scalarEnd base) old v.nodeNames v.nodes
    (A).hosts (A).groups v.nodeBits (A).lanes w)⟩
  · intro P R K mach
    exact Procedure.Exec.then first.1 second.1 mach
  rintro i (low|high)
  · exact (second.2 i (.inl (low.trans_le lo))).trans (first.2.1 i (.inl low))
  · exact (second.2 i (.inr high)).trans (first.2.1 i (.inr (last.trans high)))

end ResetOutput
end
end Hierarchy.DescentDatedAddressBook

end OAI
