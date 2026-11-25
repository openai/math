import OAI.Hierarchy.DescentRegisteredOrdinaryBooks
import OAI.Hierarchy.DescentDatedOperandOriginUniform
import OAI.Hierarchy.DescentDatedOperandEarlyUniform

namespace OAI
/-! # The two relative memory reservations of the registered ordinary date -/
namespace Hierarchy.DescentSixParty.Chronology
open DescentDatedAddressBook DescentDatedPriorOperand DescentPacking.PackedMatch.Local.Stage
open DescentOrdinaryVenueIngress DescentOrdinaryReferenceInputs DescentOrdinaryAtomFieldRAM
open DescentOrdinaryAtomFieldRAM.ScalarOperand DescentOrdinaryOriginMask DescentOrdinaryOriginPorts
open DescentOrdinaryBorn DescentPackedColony DescentHaloWalkRAM DescentSharedCableNames DescentPackedActorMask
open DescentDatedOperandReadPipeline DescentSIMDLookup ProtocolRAM
noncomputable section

namespace OrdinaryBooks
variable (b : OrdinaryBooks)

/-- Program lengths for preloading the old seven fields, old labels, newborn
chip words and the population scan. The preceding date can be a seed or reset. -/
def entryWords (branch : ℕ) (c : Clip) (old : Layout) (roleLanes roleBits : ℕ) :=
  let H := c.venue.hosts
  let G := c.venue.groups
  let M := c.working
  let role : DescentOrdinaryRoleHostPad.Layout :=
    ⟨old.blocks,old.hosts,H,G,roleLanes,M,roleBits*b.reference.oldNodes⟩
  let chip : DescentOrdinaryBirthChip.Layout :=
    ⟨c.venue.socket,H,G,M,c.venue.profile,branch,c.venue.slots⟩
  let population : RoleControl.Layout :=
    ⟨0,H,G,M,c.venue.paths,old.blocks,b.reference.oldNodes,roleBits,b.reference.countBits,b.vector.lows⟩
  (((c.fullEnd 0 + DescentOrdinaryPriorPad.roof old H M 0)+role.roof 0)+chip.finish 0)+population.endAddress

def controlWords :=
  let R:=b.reference
  let V:=b.vector
  let N:=nodes (breadth R.degree*2^R.k) R.oldNodes R.capacity
  let C : Return := ⟨R.degree,R.k,R.oldNodes,R.capacity,b.resolver.nodes,Nat.clog 2 (N+1),
    V.hosts,V.lows,V.groups,V.radix,V.lanes⟩
  C.preparationWords+DescentOrdinaryOriginPorts.words C

def mouthWords :=
  let B:=b.bornBook
  let V:=b.vector
  let n:=B.args*3
  let a:=B.bits*b.resolver.nodes
  let raw:=RolePorts.endAddress B 0+2^Nat.clog 2 (n*DescentVectorBookReshape.sourceWords B.hosts V.lows V.groups V.lanes)
  DescentVectorBookReshape.output raw n B.hosts V.lows V.groups V.radix a V.lanes+
    n*DescentVectorBookReshape.rows B.hosts V.lows V.groups V.radix V.lanes+
    2^Nat.clog 2 ((B.hosts*V.lows)*chunks V.groups V.lanes)

def sourceWords (core : PhysicalOrdinary.StaticCore) (profile : ℕ) :=
  let e:=core.material
  let fmt:=core.format
  let P:=breadth fmt.degree
  let l:=b.resolver
  let r:=DescentSharedCableNames.Packed.bits P
  let oldHeads:=P*(fmt.blocks*(fmt.degree*fmt.cap))
  let anchor:=P*(fmt.blocks*(fmt.cap*3))
  let candidates:=P*(fmt.blocks*(fmt.cap*11))
  let paths:=P*(fmt.degree+1)
  let wide : DescentOrdinaryHeadRetile.Shape := ⟨e.blocks*(4*oldHeads)+(e.blocks*(5*anchor)+e.blocks*(8*candidates)),
    e.hosts,e.groups,e.lanes,l.lanes,e.fieldBits⟩
  let narrow : DescentOrdinaryHeadRetile.Shape := ⟨paths+P,e.hosts,e.groups,e.lanes,l.lanes,r⟩
  let headWords:=wide.endAddress 0+narrow.endAddress 0
  let rows : DescentDatedOperandPages.Layout := ⟨e.oldHosts,e.oldGroups,e.oldLanes,e.lanes*e.blocks,e.fieldBits,profile⟩
  let bits:=max (max e.fieldBits (l.size+2)) (max b.bornBook.bits r)
  let geometry : Geometry := ⟨l.hosts,l.groups,l.lanes,l.jobs,P,fmt.blocks,fmt.degree,fmt.cap,bits,l.size+2⟩
  let old:=DescentDatedOperandPages.lastAddress fmt rows 0
  let col:=old+(P*(fmt.degree+1))*2^Nat.clog 2 e.oldHosts
  let broadcast:=DescentSharedLeafLookup.Public.stop col e.oldHosts e.groups e.lanes r
  let rank:=broadcast+P*2^Nat.clog 2 e.oldHosts
  let previous:=rank+l.nodes*2^(((l.size+2)*l.nodes)*l.lanes)
  let mouth:=previous+l.nodes*2^((b.bornBook.bits*l.nodes)*l.lanes)
  let translate:=DescentSharedLeafLookup.Public.stop 0 l.hosts l.groups l.lanes bits +
    geometry.stageWords 2 1 geometry.paths
  (((mouth+headWords)+4*2^(bits*l.lanes))+translate)+geometry.pipelineWords

/-- The original small input and root directories are emitted exactly once. -/
def paid (b : OrdinaryBooks) (core : PhysicalOrdinary.StaticCore) (c : Clip) (old : Layout)
    (branch roleLanes roleBits profile : ℕ) : OrdinaryBooks :=
  b.reserved (b.entryWords branch c old roleLanes roleBits)
    (b.controlWords+b.mouthWords+b.sourceWords core profile)

end OrdinaryBooks

namespace PhysicalOrdinary
variable {F P : Type} [Field F] (v : PhysicalOrdinary F P)

theorem register_sizes (floor : ℕ) (A : ArgumentEntry v) :
    A.words v=v.books.entryWords v.gadget.b A.clip A.previous A.rolePitch A.roleBits ∧
      v.originControlWords=v.books.controlWords ∧ v.originMouthWords=v.books.mouthWords ∧
      v.rootSourceSize=v.books.sourceWords (v.staticCore floor) v.profile := by
  refine ⟨?_,?_,?_,?_⟩
  · rfl
  · rfl
  · rfl
  · dsimp only [rootSourceSize, OrdinaryBooks.sourceWords, staticCore, books, ticketReadGeometry,
      operandShortBits, operandDepotLayout, headTransferWords, wideHeads, narrowHeads,
      oldHeadCount, anchorHeadCount, rawHeadCount, pathHeadCount]

/-- The prior date's actual registers and the selected clip determine all
operand books, including both finite native directory sizes. -/
theorem registered_paid_books (prior : DatePorts) (floor : ℕ) :
    let c:=v.fundedClip (v.argumentUnitFrom prior floor)
    let b:=v.books.clipped v.area c
    let role:=DescentPrimitivePalette.printedBits v.gadget v.palette.seedWidth v.palette.grainLimit v.palette.rotor
    (v.registeredFrom prior floor).books=
      b.paid (v.staticCore floor) c (prior.argumentLayout (2^v.area.k))
        v.gadget.b prior.roleLanes role v.profile := by
  intro c b role
  let W:=v.registeredFrom prior floor
  let A:=v.registeredEntry prior floor
  have sizes:=W.register_sizes floor A
  rw [v.registered_books]
  change b.reserved (A.words W) (W.originControlWords+W.originMouthWords+W.rootSourceSize) = _
  rw [sizes.1,sizes.2.1,sizes.2.2.1,sizes.2.2.2]
  dsimp only [OrdinaryBooks.paid, OrdinaryBooks.entryWords, OrdinaryBooks.controlWords,
    OrdinaryBooks.mouthWords, OrdinaryBooks.sourceWords, W, A, registeredEntry, registeredFrom,
    fundedFrom, withFundedArguments, withFundedClip, withOriginReservation, books, OrdinaryBooks.clipped,
    staticCore, b, c, role]
  rfl

end PhysicalOrdinary
end
end Hierarchy.DescentSixParty.Chronology

end OAI
