import OAI.Hierarchy.DescentReachedOriginTransport
import OAI.Hierarchy.DescentArchiveRegisterCoordinates
import OAI.Hierarchy.DescentDatedPaddedBirthSocket

namespace OAI
/-! The attained six W fields and physical source coordinates on the registered cable job. -/
namespace Hierarchy.DescentLocalArchiveOrder.PaddedOrigin
open DescentNetworkPartition Computability.BorderVNP.Crossing
open DescentKernelHistory DescentSixParty DescentSixParty.Chronology DescentCompiler DescentStageEdgeReceipt
open DescentCableDonorNames DescentOrdinaryLocalBirth DescentHostDegree DescentHostDirectory DescentOrdinaryDonorHalo
open DescentNetworkPartition Computability.BorderVNP.Crossing DescentSharedCableNames DescentSixParty.StarKeys
open DescentColonies DescentGL DescentWalshTables DescentPacking
open DescentGroupPeerOrder DescentPacking.PackedMatch.Local.Stage DescentSortedHaloRaster DescentHaloWalkRAM DescentSIMDLookup
open DescentScalarVenueMask DescentHostDirectory.SiteDecode DescentOrdinaryLocalBirth DescentSharedCableNames DescentPackedActorMask
open Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM DescentScalarBookReshape
open scoped Classical Fin.CommRing
set_option quotPrecheck false
set_option maxRecDepth 4096
noncomputable section
variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits} {G : PoweredGadget F}
variable {u q ε : ℝ} {S : AtomSchedule} {k i z D z' D' wire hist : ℕ}
    {cap : Reached W G q ε S k i z D wire hist}
    {he : 0≤ε} {T : StageInput W G u ε} {c : (T.result he).Choice}
    {n : Normalize ((T.result he).state c)} {target : Reached n.result G q ε S k (i+1) z' D' wire hist}
    (ticket : OrdinaryLink cap he T c n target) (arch : Archive W)
local notation "r" => BitDescription.scannedRows he T
local notation "sw" => branchWidth G (fun _ : (r).pairs=>T.z) ((r).profile c)
local notation "next" => (ticket.advance arch).bit
local notation "layout" => bestLayout sw
local notation "group" => GadgetNetwork.newSite W.graph (r).pick layout (r).pack

local notation "bookChart" => activeChart ticket
local notation "key" => (bookChart).key he T c

local notation "A" => cap.placement
local notation "deg" => (A).degree
local notation "bound" => DescentHaloWalkRAM.breadth deg*2^k

local notation "shelf"=>2^(packExponent 20 deg)+2
local notation "raw"=>2^(k+1)*shelf
local notation "walks₀"=>DescentHaloWalkRAM.breadth deg
local notation "K"=>1+(A).cap*6
local notation "moves"=>rotor A (groupRank Fin.valEmbedding (cap.vertex.trans Fin.valEmbedding))

open DescentPaidResidentCount
variable {mb : ℕ} (tokens : Block k→Fin (1+cap.placement.cap*6)→Fin (Fintype.card cap.V)→Fin (S.groupCount i)→
  Ticket (DescentHaloWalkRAM.breadth cap.placement.degree) (2^(k+1)*(2^(packExponent 20 cap.placement.degree)+2)))
local notation "stock" => Descriptors shelf k (A).pos (A).block (ticketParent (he:=he) (T:=T)) (ticketSlot (c:=c) ticket)
  (key∘group) cap.vertex (Function.Embedding.refl _) moves tokens

local notation "OH" => Fintype.card cap.V
local notation "OG" => S.groupCount i
variable (age : i<S.length) (radix : S.radix=2^k)

variable (ports:DatePorts) (room:DatePorts.RangeRoom ports cap arch.bit)
local notation "fits₀" => maxNodes_le arch.bit room.capacity
local notation "oldN" => ports.nodes
local notation "N₀" => DescentPackedActorMask.nodes bound oldN (A).cap
variable (prior : Local arch.bit)
variable (priorCount : Block k→Fin (Fintype.card cap.V)→Fin (S.groupCount i)→Cell mb)
variable (old_live : ∀u,(priorCount (cap.placement.block u) (cap.vertex (cap.placement.pos u).2) (cap.placement.pos u).1).val=
    Fintype.card (arch.bit.recipe u).Node)
variable (old_empty : ∀b h g,(¬∃u,cap.placement.block u=b ∧ cap.vertex (cap.placement.pos u).2=h ∧ (cap.placement.pos u).1=g)→priorCount b h g=0)

open DescentOrdinaryAtomFieldRAM DescentRetainedRangeDigits DescentOrdinaryAtomFieldRAM.ScalarOperand DescentHaloWalkRAM


open DescentBundleHistory
open DescentOrdinaryAtomFieldRAM.ScalarOperand DescentOperandVectorArena DescentPackedOperand
open PhysicalOrdinary DescentOrdinaryRasterReturn
variable {p R:ℕ} (hp:0<p) (one:1≤R) (pin:∀e,p∣bits e)
    (sh:WorldShape p R arch.bit) (unit:p∣T.z)
local notation "after" => afterOrdinary hp one pin ticket arch sh unit
local notation "pitch₁" => (2^(k+1)-1)*shelf
local notation "OH₁" => Fintype.card cap.V
local notation "NG₁" => S.groupCount (i+1)
local notation "block₁" x:arg => target.placement.block x
local notation "home₁" x:arg => hostIndex ticket (target.vertex (target.placement.pos x).2)
local notation "group₁" x:arg => (target.placement.pos x).1
local notation "args₁" x:arg => (((after).sites x.1).recipe hp).arity x.2
variable (v:PhysicalOrdinary F P) (shape:v.VectorShape)
    (lo:v.vector.lows=(2^(k+1)-1)*(2^(packExponent 20 cap.placement.degree)+2)) (gs:v.vector.groups=S.groupCount (i+1)) (rad:v.vector.radix=2^k)
    (hostFit:Fintype.card cap.V≤v.vector.hosts)
local notation "physH" x:arg => ((home₁ x).cast (congrArg (OH*·) lo.symm))
local notation "physG" x:arg => ((group₁ x).cast gs.symm)
local notation "physB" x:arg => ((block₁ x).cast rad.symm)
local notation "physicalJob" x:arg fit:arg arg:arg =>
  v.resolver.index ((physB x.1).cast shape.blocks.symm,⟨(advance ticket arch prior x.1 x.2).val,fit⟩,arg)
local notation "rh" x:arg => ((widen hostFit (physH x)).cast shape.hosts.symm)
local notation "rg" x:arg => ((physG x).cast shape.groups.symm)
open DescentOrdinaryOriginMask DescentOrdinaryOriginPorts DescentDatedSourcePathDirectory
open DescentDatedOperandReadPipeline DescentDatedOperandCoordinates

variable (refD:v.reference.degree=cap.placement.degree) (refK:v.reference.k=k) (refN:v.reference.oldNodes=ports.nodes)
    (refC:v.reference.capacity=cap.placement.cap)
variable (receiverH:Fintype.card cap.V≤v.material.oldHosts)
local notation "smallRoster" => hostRotor cap.vertex (hostRoster A (cap.vertex.trans Fin.valEmbedding))
variable {stampField:ℕ}
    (origPrevious:Block k→Fin (Fintype.card cap.V)→Fin (S.groupCount i)→Cell (stampField*ports.nodes))
    (origBorn:Block k→Fin cap.placement.cap→Fin 6→Fin (Fintype.card cap.V)→Fin (S.groupCount i)→Cell stampField)
local notation "smallW" => rangeValues ticket arch tokens age radix priorCount origPrevious origBorn
variable (large:v.OriginalDonors stampField (Packed.bits ((2^(k+1)-1)*(2^(packExponent 20 cap.placement.degree)+2))) mb)
    («prefix»:∀l,Values.Prefix hostFit
      (Values.originTransport refD refK refN refC lo gs rad (rfl:stampField=stampField) (rangeValues ticket arch tokens age radix priorCount origPrevious origBorn) l) (large l))

local notation "chart₁" => originStampChart (cap:=cap) (K₀:=ports.nodes) v.resolver.nodes v.originBits
local notation "storeW" x:arg => DescentScalarBookReshape.book
  (fun l h g=>selection N₀ v.resolver.nodes v.originBits (marked (smallW l) h g)) (block₁ x) (home₁ x) (group₁ x)
local notation "orig_" => v.originHeaderValue shape large
local notation "dense" => cap.vertex.trans (Fin.castLEEmb receiverH)
local notation "physical_" => Gather.reaching (hostRotor dense (hostRoster A (cap.vertex.trans Fin.valEmbedding)))
local notation "rack_" x:arg => (currentLabel ticket arch x.1 x.2).val.1
local notation "oldOrd" saved:arg =>
  (((bounded arch.bit prior saved.1).trans (Fin.castLEEmb fits₀)) saved.2)
local notation "firstSite" pair:arg => W.graph.src ((r).pick (pair,0))
local notation "firstSeat" pair:arg => outgoingSlot A (cap.order.trans Fin.valEmbedding) S cap.valid (r).pick
  (fun q:(r).pairs=>(r).picked (q,0)) pair

include old_live old_empty «prefix» in
/-- The old node's true sorted source ordinal and unrounded source block are read from W. -/
theorem registered_old_W (auth:stock) (x:NodeOrder.All next) (j:Fin (args₁ x))
    (fits:(advance ticket arch prior x.1 x.2).val<v.resolver.nodes) (written:j.val<v.resolver.operands)
    (saved:NodeOrder.All arch.bit) (carried:roots ticket arch x=.inl saved) :
    ∃walk:Fin (breadth deg),
      DescentSortedRoster.indexed physical_ (dense (rack_ x).2) walk=some (dense ((A).pos saved.1).2) ∧
      ((A).pos saved.1).1=(rack_ x).1 ∧
      ∀f:Fin 6,(![1,walk.val,((A).block saved.1).val,(oldOrd saved).val,0,0] f)<2^v.operandShortBits→
        (orig_ (physicalJob x fits ⟨j.val,written⟩) f (rh x.1) (rg x.1)).val=
          ![1,walk.val,((A).block saved.1).val,(oldOrd saved).val,0,0] f :=by
  have stampFits:N₀<2^v.originBits:=by
    simpa only [PhysicalOrdinary.originCandidates,refD,refK,refN,refC] using v.originBits_fit
  obtain ⟨walk,sorted,sourceGroup,stamp⟩:=old_registered_stamp ticket arch tokens age radix fits₀ prior priorCount
    old_live old_empty origPrevious origBorn auth x.1 x.2 saved carried stampFits fits
  obtain ⟨path,⟨visit,_⟩,_⟩:=DescentDatedSourcePathDirectory.Sorted.raw_at (Gather.reaching smallRoster) (cap.vertex (rack_ x).2)
    (cap.vertex ((A).pos saved.1).2) walk sorted
  obtain ⟨storedAt,_,_⟩:=DescentDatedSourcePathDirectory.Sorted.host_coordinates receiverH cap.vertex (hostRoster A (cap.vertex.trans Fin.valEmbedding))
    (cap.vertex (rack_ x).2) (cap.vertex ((A).pos saved.1).2) walk path sorted visit
  refine ⟨walk,storedAt,sourceGroup,?_⟩
  intro f cell
  exact v.old_origin_digit shape large hostFit smallW refD refK refN refC lo gs rad rfl «prefix»
    (block₁ x.1) ⟨(advance ticket arch prior x.1 x.2).val,fits⟩ ⟨j.val,written⟩
    (home₁ x.1) (group₁ x.1) walk ((A).block saved.1) (oldOrd saved) stamp f cell

include room old_live old_empty «prefix» in
/-- The newborn stamp and every origin-register word refer to the same measured scalar,
block and group. This includes the candidate's true old outgoing first-arm ordinal. -/
theorem registered_born_W (auth:stock) (x:NodeOrder.All next) (j:Fin (args₁ x))
    (fits:(advance ticket arch prior x.1 x.2).val<v.resolver.nodes) (written:j.val<v.resolver.operands)
    (pair:(r).pairs) (party:Fin 6) (fresh:roots ticket arch x=.inr (pair,party)) :
    let actor:=firstSite pair
    let slot:Fin v.resolver.nodes:=⟨(advance ticket arch prior x.1 x.2).val,fits⟩
    ∃walk:Fin (breadth deg),
      DescentSortedRoster.indexed physical_ (dense (rack_ x).2) walk=some (dense ((A).pos actor).2) ∧
      ((A).pos actor).1=(rack_ x).1 ∧
      ((encode v.originBits v.resolver.nodes).symm (storeW x.1) slot).val=
        (candidate chart₁ walk ((A).block actor) (.inr (firstSeat pair,party))).val+1 ∧
      ∀f,orig_ (physicalJob x fits ⟨j.val,written⟩) f (rh x.1) (rg x.1)=
        readLaw chart₁ v.operandShortBits slot f (storeW x.1) :=by
  intro actor slot
  have stampFits:N₀<2^v.originBits:=by
    simpa only [PhysicalOrdinary.originCandidates,refD,refK,refN,refC] using v.originBits_fit
  obtain ⟨walk,_,sorted,_,_,sourceGroup,stamp⟩:=padded_birth_socket_coordinates ticket arch tokens age radix fits₀ prior
    priorCount old_live old_empty origPrevious origBorn auth x.1 x.2 pair party fresh stampFits fits receiverH
  refine ⟨walk,sorted,sourceGroup,stamp,?_⟩
  exact v.registered_origin_words shape large hostFit smallW refD refK refN refC lo gs rad rfl «prefix»
    (block₁ x.1) slot ⟨j.val,written⟩ (home₁ x.1) (group₁ x.1)

end
end Hierarchy.DescentLocalArchiveOrder.PaddedOrigin

end OAI
