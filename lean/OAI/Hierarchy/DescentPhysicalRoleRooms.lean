import OAI.Hierarchy.DescentPhysicalResetDateOutput
import OAI.Hierarchy.DescentRetainedTargetPlacementRead

namespace OAI
/-! # Actual retained roles, paid cells, span digits and birth guards are addressable -/
namespace Hierarchy.DescentDatedAddressBook.PhysicalReset
open DescentSixParty DescentSixParty.Chronology DescentFallbackPeriod.Projected DescentSIMDLookup
open Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false
variable {a : PhysicalReset} {floor w : ℕ} {u : a.DateInputs floor w} (z : u.FinalInputs)
local notation "v" => a.successor
local notation "b" => a.rebased floor
local notation "rc" => a.rootPhase u.shape floor u.count u.hub u.g u.Y u.roots w
local notation "actorBase" => (v).middle.stop b
local notation "ds" => (v).actor.directory actorBase
local notation "A" => (v).receiver
local notation "fund" => (v).fundedEnd b
local notation "venue" => (v).venue
local notation "stop₀" => (v).finalEnd b
local notation "roleAt" => (v).fullEnd b
local notation "movedAt" => (v).roleEnd b
local notation "classAt" => (v).classEnd b
local notation "bornAt" => (v).birthEnd b
local notation "meta" => (v).primitiveEnd b
local notation "root" => (v).middle
local notation "T" => (v).metadata.chart

/-- The allocation following the scalar columns includes the full padded width
of the last span lookup, even when there are no occupied receiver rows. -/
theorem FinalInputs.span_at (ready : u.Ready) (x node j) :
    (z.spans x node j).Fits w stop₀ := by
  let rows:=(A).hosts*chunks (A).groups (A).lanes
  let idx:=(v).operandOrdinal u.operand 6 j (x.cast z.metaBlocks) (node.cast z.metaNodes)
  have inRange:idx.val*rows≤(A).fields*rows:=Nat.mul_le_mul_right _ idx.isLt.le
  let dict:=(v).operandDictionaryEnd b
  let e:=2^Nat.clog 2 (rows+1)
  have pad:dict+(A).fields*rows+e≤ stop₀:=by
    change _≤(dict+(A).fields*rows+max _ e)+_+e
    omega
  have tail_:dict+idx.val*rows+e≤ stop₀:=by omega
  exact ⟨⟨Nat.two_pow_pos _,(Nat.le_add_left ..).trans_lt (tail_.trans_lt ready.full),tail_⟩,trivial⟩

private theorem higher {page : Bank} {p q : ℕ} (h : page.Fits w p) (up : p≤q) : page.Fits w q :=
  ⟨h.1,h.2.1,h.2.2.trans up⟩

/-- On the complete actual chart, every birth lookup reads one reached root
or an explicit zero. All other terms come from previously issued registers. -/
theorem FinalInputs.published_rooms (shape : a.RootShape) (ready : u.Ready)
    (successor : (venue).RunRoom (FinalInputs.predecessor u) fund 0 w)
    (blocks : (T).blocks≤2^(venue).next.k)
    (posLanes : 0<(v).birth.placement.lanes) (posBlocks : 0<(v).birth.placement.blocks)
    (endFit : a.endAddress floor<2^w) :
    (v).birth.RootRoom classAt z.guards (ds).count (ds).inverse w ∧
      (v).primitive.Fits bornAt z.roles w ∧
      (∀x,(FinalInputs.paid u x).Fits w meta) ∧ ∀x n j,(z.spans x n j).Fits w meta := by
  obtain ⟨_f,actorStart,actorEnd,trunkEnd,massEnd,jointEnd,privateEnd,maskedEnd,sectionEnd⟩:=ready.ordered
  obtain ⟨fundLo,venueLo⟩:=(v).complete_after b
  obtain ⟨_d₁,_d₂,venueEnd⟩:=(venue).after fund
  have moveLo:roleAt≤ movedAt:=by
    change _≤(v).roleTransfer.endAddress roleAt
    rw [(v).roleTransfer.translate];exact Nat.le_add_right ..
  have classLo:movedAt≤classAt:=by
    change _≤(v).actorClass.endAddress movedAt
    rw [(v).actorClass.translate];exact Nat.le_add_right ..
  have bornLo:classAt≤bornAt:=by
    change _≤(v).birth.endAddress classAt
    rw [(v).birth.translate];exact Nat.le_add_right ..
  have primLo:bornAt≤ meta:=by
    change _≤(v).primitive.endAddress bornAt
    rw [(v).primitive.translate];exact Nat.le_add_right ..
  have endLo:meta≤a.endAddress floor:=by
    change _≤(v).metadata.endAddress meta
    rw [(v).metadata.translate];exact Nat.le_add_right ..
  have classFit:classAt<2^w:=by omega
  have birthFit:bornAt<2^w:=by omega
  obtain ⟨_,_,_,oldCount,oldInv⟩:=(ds).fits ready.actor.room
  have actorBefore:(ds).endAddress≤ movedAt:=by change (v).actorEnd b≤ movedAt;omega
  have count:=higher oldCount actorBefore
  have inv:=higher oldInv actorBefore
  have early:(rc).preparedEnd u.book≤classAt:=by rw [ready.rootEnd];omega
  have prepared:(RootTemplates.arena ((rc).headerEnd u.book) (root).rootHosts (root).rootGroups
    (root).rootLanes (root).rootDepth (root).rotorBits (root).rootDegree).first
      (Fintype.card (RootPage (root).rootDepth (2^(root).rotorBits)))≤classAt:=by
    let headerBase:= (rc).headerEnd u.book
    change (RootTemplates.arena headerBase _ _ _ _ _ _).first _≤classAt
    rw [shape.hosts,shape.groups,shape.lanes,shape.degree]
    exact early
  have guarded:(v).birth.GuardsFit classAt z.guards w:=by
    intro q l B hit
    exact DescentPrimitiveBirth.guards_room _ _ _ _ _ _ _ _ prepared classFit _ _ B hit
  have liftRoof:(v).birth.lifted classAt≤bornAt:=Nat.le_add_right ..
  have remapRoom: (v).actorClass.next movedAt≤classAt:=((v).actorClass.guard movedAt).2
  have beforePage : movedAt≤(v).actorClass.next movedAt:=((v).actorClass.guard movedAt).1
  have safe:=((v).actorClass.remap movedAt).book_fits (ds).count (ds).inverse
    (higher count beforePage) (higher inv beforePage) classFit
  have classWord:(FinalInputs.classWord u).Fits w classAt:=
    ((v).actorClass.remap movedAt).fits safe _
      ⟨higher ((v).actorClass.page_fits movedAt classFit) remapRoom,trivial⟩
  have paid (x : Fin (T).blocks) : (FinalInputs.paid u x).Fits w classAt:=by
    let x' : Fin (2^(venue).next.k):=⟨x.val,x.isLt.trans_le blocks⟩
    have orig:=(successor.return_.paid x').1
    have toClass:(venue).venueStart fund≤classAt:=venueEnd.trans (moveLo.trans classLo)
    exact ⟨higher orig toClass,trivial⟩
  have span (x node j) : (z.spans x node j).Fits w classAt:=
    ProtocolRAMGeneratedWrite.fits_mono _ (by omega : stop₀≤classAt) (z.span_at ready x node j)
  refine ⟨⟨guarded,higher count classLo,higher inv classLo,posLanes,posBlocks,liftRoof.trans_lt birthFit⟩,?_,
    fun x=>ProtocolRAMGeneratedWrite.fits_mono _ (bornLo.trans primLo) (paid x),
    fun x n j=>ProtocolRAMGeneratedWrite.fits_mono _ (bornLo.trans primLo) (span x n j)⟩
  intro x node
  have valid:=(DescentRetainedTargetPlacement.Chart.validBank (v).roleTransfer.placement (v).roleTransfer.batch
    ((v).roleTransfer.placementBase roleAt) (classLo.trans_lt classFit)
    (node.cast z.roleNodes) (x.cast z.roleBlocks)).1
  have native:=(v).birth.operandsFit classAt (node.cast z.birthNodes) (x.cast z.birthBlocks)
    (FinalInputs.classWord u) (FinalInputs.paid u (x.cast z.censusBlocks))
    (fun i=>z.spans (x.cast z.censusBlocks) (node.cast z.censusNodes) (i.cast z.birthArgs))
    classWord (paid _) (fun i=>span _ _ _) birthFit
  exact ⟨⟨higher valid (classLo.trans bornLo),trivial⟩,native⟩

/-- The matrix packet used to order the old-home nodes lives in the
already prepared original root. Its full source fits before role transfer. -/
theorem FinalInputs.old_matrix_room (ready : u.Ready) : (FinalInputs.oldMatrix u).Fits w roleAt:=by
  obtain ⟨_,fromRoots,begin_,ab,bc,cd,de,ef,fg⟩:=ready.ordered
  obtain ⟨first,last⟩:=(v).complete_after b
  have earlier:(rc).preparedEnd u.book≤roleAt:=by rw [ready.rootEnd];omega
  apply ProtocolRAMGeneratedWrite.fits_mono _ earlier
  exact (rc).gathered_fits u.book u.bookFits _

/-- Full tail readiness from the previous atom and role pages, plus the
finite original census and successor-venue room. -/
theorem FinalInputs.room_of_previous (shape : a.RootShape) (ready : u.Ready)
    (old : ∀j,(z.earlier j).Fits w floor)
    (roles : ∀j,(z.previousRoles j).Fits w floor)
    (jobs : DescentFundedCensus.Room z.jobs w fund)
    (successor : (venue).RunRoom (FinalInputs.predecessor u) fund 0 w)
    (blocks : (T).blocks≤2^(venue).next.k)
    (posLanes : 0<(v).birth.placement.lanes) (posBlocks : 0<(v).birth.placement.blocks)
    (moveLanes : 0<(v).roleTransfer.lanes) (moveBlocks : 0<(v).roleTransfer.blocks)
    (endFit : a.endAddress floor<2^w) : z.Room := by
  obtain ⟨bRooms,rRooms,counts,spans⟩:=z.published_rooms shape ready successor blocks posLanes posBlocks endFit
  obtain ⟨firstAt,ao,ta,te,ma,pri,ms,se,fe⟩:=ready.ordered
  obtain ⟨afterFields,afterFund⟩:=(v).complete_after b
  have savedLoc:=stencil_saved_before (u:=u)
  have measured:(rc).origin≤actorBase:=by
    rw [←ready.rootEnd]
    have lim:=u.book.limits (rc).projectionEnd (root).signedHosts (2^(root).stencil.c) (root).signedLanes
    exact (rc).origin_le_projection.trans ((lim.1.trans (lim.2.1.trans lim.2.2)).trans (Nat.le_add_right ..))
  have keyFit:(rc).saved.Fits w stop₀:=by
    have atOrigin:(rc).saved.base<(rc).origin:=savedLoc
    have wide:=ready.full
    change 0<2^0 ∧ 2^0<2^w ∧ (rc).saved.base+2^0≤ stop₀
    rw [pow_zero]
    exact ⟨by decide,by omega,by omega⟩
  have lo:floor≤ stop₀:=by omega
  have mv:roleAt≤ movedAt:=by rw [ResetOutput.roleEnd,(v).roleTransfer.translate];exact Nat.le_add_right ..
  have cl:movedAt≤classAt:=by rw [ResetOutput.classEnd,(v).actorClass.translate];exact Nat.le_add_right ..
  have br:classAt≤bornAt:=by rw [ResetOutput.birthEnd,(v).birth.translate];exact Nat.le_add_right ..
  have pr:bornAt≤ meta:=by rw [ResetOutput.primitiveEnd,(v).primitive.translate];exact Nat.le_add_right ..
  have mt:meta≤a.endAddress floor:=by
    change _≤(v).metadata.endAddress meta
    rw [(v).metadata.translate];exact Nat.le_add_right ..
  obtain ⟨_,_,_,count,inv⟩:=(ds).fits ready.actor.room
  have low:(ds).endAddress≤roleAt:=by change (v).actorEnd b≤roleAt;omega
  refine ⟨fun j=>higher (old j) lo,keyFit,by omega,jobs,successor,?_,bRooms,rRooms,counts,spans,endFit⟩
  exact ⟨fun j=>higher (roles j) (by omega),higher keyFit (afterFields.trans afterFund),
    higher count low,higher inv low,FinalInputs.old_matrix_room (u:=u) ready,moveLanes,moveBlocks,by change movedAt<2^w;omega⟩

end
end Hierarchy.DescentDatedAddressBook.PhysicalReset

end OAI
