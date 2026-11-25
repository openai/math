import OAI.Hierarchy.DescentReachedPhysicalPinJob
import OAI.Hierarchy.DescentReachedOriginTransport
import OAI.Hierarchy.DescentDatedReachedOriginSocket
import OAI.Hierarchy.DescentDatedSortedPathPadding
import OAI.Hierarchy.DescentSampledCarriedResolver

namespace OAI
/-! Original private operands at the native sorted-donor resolver job. -/
namespace Hierarchy.DescentDatedSourcePathDirectory.Sorted
open DescentHaloWalkRAM DescentScalarVenueMask DescentSortedRoster
noncomputable section
theorem rack_paths {D D' H H':ℕ} (degree:D'=D) (widen:H≤H')
    (small:Fin H→Fin D→Option (Fin H)) (large:Fin H'→Fin D'→Option (Fin H'))
    (before:∀h j,large (h.castLE widen) (j.cast degree.symm)=(small h j).map (Fin.castLEEmb widen))
    (recv old:Fin H) (s p:Fin (breadth D))
    (ranked:indexed (Gather.reaching small) recv s=some old)
    (walked:Gather.select (Gather.reaching small) recv p=some old) :
    indexed (Gather.reaching large) (recv.castLE widen) (s.cast (congrArg breadth degree.symm))=some (old.castLE widen) ∧
    Gather.select (Gather.reaching large) (recv.castLE widen) (p.cast (congrArg breadth degree.symm))=some (old.castLE widen) :=by
  subst D'
  change indexed (Gather.reaching large) ((Fin.castLEEmb widen) recv) s = some ((Fin.castLEEmb widen) old) ∧
    Gather.select (Gather.reaching large) ((Fin.castLEEmb widen) recv) p = some ((Fin.castLEEmb widen) old)
  have same:=reaching_pad widen small large before recv
  exact ⟨by simpa only [ranked,Option.map_some] using indexed_pad widen _ _ recv same s,
    by simpa only [walked,Option.map_some] using selected_pad widen _ _ recv same p⟩
end
end Hierarchy.DescentDatedSourcePathDirectory.Sorted

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
set_option Elab.async false
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

variable {w : ℕ} (ports : DatePorts) (mem : Memory w) (room : DatePorts.RangeRoom ports cap arch.bit)
    (population : Fintype.card cap.V≤ports.operandHosts)
local notation "fits₀" => maxNodes_le arch.bit room.capacity
local notation "oldN" => ports.nodes
local notation "N₀" => DescentPackedActorMask.nodes bound oldN (A).cap
variable (prior : Local arch.bit)
variable (priorCount : Block k→Fin (Fintype.card cap.V)→Fin (S.groupCount i)→Cell mb)
variable (old_live : ∀u,(priorCount (cap.placement.block u) (cap.vertex (cap.placement.pos u).2) (cap.placement.pos u).1).val=
    Fintype.card (arch.bit.recipe u).Node)
variable (old_empty : ∀b h g,(¬∃u,cap.placement.block u=b ∧ cap.vertex (cap.placement.pos u).2=h ∧ (cap.placement.pos u).1=g)→priorCount b h g=0)

open DescentOrdinaryAtomFieldRAM DescentRetainedRangeDigits DescentOrdinaryAtomFieldRAM.ScalarOperand DescentHaloWalkRAM


open DescentKernelHistory DescentBundleHistory DescentOperandStateBanks DescentDatedPriorOperand
open DescentOrdinaryAtomFieldRAM.ScalarOperand DescentOperandVectorArena DescentPackedOperand
open PhysicalOrdinary DescentOrdinaryRasterReturn
variable {p R s Z:ℕ} (hp:0<p) (one:1≤R) (pin:∀e,p∣bits e)
    (sh:WorldShape p R arch.bit) (unit:p∣T.z)
local notation "uni" => fun _ : (r).pairs=>T.z
local notation "birthRoom" => fun _ : (r).pairs=>le_refl T.z
local notation "whole" => fun _ : (r).pairs=>unit
local notation "prof" => (r).profile c
local notation "after" => afterOrdinary hp one pin ticket arch sh unit
local notation "M" => rawGraph he T c
local notation "baseShape" => physicalShape W arch.bit G (r).pick uni birthRoom prof hp sh.sites sh.edges pin whole
local notation "names" => NodeOrder.physicalNames arch.bit G (r).pick uni birthRoom prof
local notation "source" x:arg => (names).symm (roots ticket arch x)

local notation "pitch₁" => (2^(k+1)-1)*shelf
local notation "OH₁" => Fintype.card cap.V
local notation "NG₁" => S.groupCount (i+1)
variable (pinCode:P→ℕ) (arity:ℕ) (op:RotorSpec) (labels:NodeOrder.All arch.bit→DescentPrimitivePalette.Label G s Z op)
    (flags:Fin (2^ports.venue.k)→Fin ports.nodes→Fin ports.operandHosts→Fin ports.venue.groups→ℕ)
local notation "ptr₀" => Reached.argumentPointer cap arch.bit prior sh hp pinCode arity
variable (stored:DatePorts.ArchiveRead ports cap arch.bit prior room sh op labels (Reached.argumentPointer cap arch.bit prior sh hp pinCode arity) flags mem)
    (paid:∀v u,((sh.sites v).recipe hp).arity u≤ports.argumentsPerNode)
    (bitsFit:ports.operandBits*ports.nodes*ports.operandLanes≤w)
    (birth:Fin 4→Block k→Fin cap.placement.cap→Fin 6→Fin (Fintype.card cap.V)→Fin (S.groupCount i)→Cell ports.operandBits)
local notation "priorAt" n:arg f:arg => DatePorts.physicalHeaderSource ports cap arch.bit room population mem n f
local notation "rows₁" n:arg f:arg => rangeValues ticket arch tokens age radix priorCount (priorAt n f) (birth f)
local notation "block₁" x:arg => target.placement.block x
local notation "home₁" x:arg => hostIndex ticket (target.vertex (target.placement.pos x).2)
local notation "group₁" x:arg => (target.placement.pos x).1
local notation "args₁" x:arg => (((after).sites x.1).recipe hp).arity x.2
local notation "earlier_" x:arg j:arg => ((baseShape (source x).1).recipe hp).operand (source x).2 (sourceIndex ticket arch hp one pin sh unit x j)

variable (v:PhysicalOrdinary F P) (shape:v.VectorShape)
    (lo:v.vector.lows=(2^(k+1)-1)*(2^(packExponent 20 cap.placement.degree)+2)) (gs:v.vector.groups=S.groupCount (i+1)) (rad:v.vector.radix=2^k)
    (field:v.resolver.size+2=ports.operandBits) (hostFit:Fintype.card cap.V≤v.vector.hosts)
    (V:References.Rows v.vector cap.placement.degree k ports.nodes cap.placement.cap (v.resolver.size+2) (Packed.bits ((2^(k+1)-1)*(2^(packExponent 20 cap.placement.degree)+2))) mb)
local notation "small₁" n:arg f:arg => Values.transport lo gs rad field (rows₁ n f)
local notation "physH" x:arg => ((home₁ x).cast (congrArg (OH*·) lo.symm))
local notation "physG" x:arg => ((group₁ x).cast gs.symm)
local notation "physB" x:arg => ((block₁ x).cast rad.symm)
local notation "physicalJob" x:arg fit:arg arg:arg =>
  v.resolver.index ((physB x.1).cast shape.blocks.symm,⟨(advance ticket arch prior x.1 x.2).val,fit⟩,arg)
local notation "rh" x:arg => ((widen hostFit (physH x)).cast shape.hosts.symm)
local notation "rg" x:arg => ((physG x).cast shape.groups.symm)
local notation "book_" => v.returnedBook shape V

local notation "atSlot₀" fit:arg => previousNodeSlot (arch:=arch) (ports:=ports) (room:=room) (prior:=prior) (hp:=hp) (sh:=sh) (arity:=arity) fit


open DescentOrdinaryOriginMask DescentOrdinaryOriginPorts DescentDatedSourcePathDirectory DescentRawCablePanel
open DescentDatedOperandReadPipeline DescentDatedOperandCoordinates

variable (refD:v.reference.degree=cap.placement.degree) (refK:v.reference.k=k) (refN:v.reference.oldNodes=ports.nodes)
    (refC:v.reference.capacity=cap.placement.cap) (matB:v.resolver.blocks=v.material.blocks)
    (matH:v.resolver.hosts≤v.material.hosts) (matG:v.resolver.groups=v.material.groups)
local notation "fmt_" => v.ticket.depotShape v.short
local notation "smallRoster" => hostRotor cap.vertex (hostRoster A (cap.vertex.trans Fin.valEmbedding))
variable (dFit:(v.ticket.depotShape v.short).degree=cap.placement.degree) (blockFit:(v.ticket.depotShape v.short).blocks=2^k)
    (receiverH:Fintype.card cap.V≤v.material.oldHosts) (stepFit:v.materialPitch=(2^(k+1)-1)*(2^(packExponent 20 cap.placement.degree)+2))
    (Rbig:Fin v.material.oldHosts→Fin (v.ticket.depotShape v.short).degree→Option (Fin v.material.oldHosts))
    (nearFit:∀h j,Rbig (h.castLE receiverH) (j.cast dFit.symm)=(hostRotor cap.vertex (hostRoster cap.placement (cap.vertex.trans Fin.valEmbedding)) h j).map (Fin.castLEEmb receiverH))
variable {stampField:ℕ}
    (origPrevious:Block k→Fin (Fintype.card cap.V)→Fin (S.groupCount i)→Cell (stampField*ports.nodes))
    (origBorn:Block k→Fin cap.placement.cap→Fin 6→Fin (Fintype.card cap.V)→Fin (S.groupCount i)→Cell stampField)
local notation "smallW" => rangeValues ticket arch tokens age radix priorCount origPrevious origBorn
variable (large:v.OriginalDonors stampField (Packed.bits ((2^(k+1)-1)*(2^(packExponent 20 cap.placement.degree)+2))) mb)
    («prefix»:∀l,Values.Prefix hostFit
      (Values.originTransport refD refK refN refC lo gs rad (rfl:stampField=stampField) (rangeValues ticket arch tokens age radix priorCount origPrevious origBorn) l) (large l))
    (mouth:Fin v.resolver.jobs→Fin 3→DescentDatedOperandReadPipeline.Values v.ticketReadGeometry v.bornBook.bits)
    (published:v.WideHead→Fin v.material.hosts→Fin v.material.groups→Cell v.material.fieldBits)
local notation "originWords" => v.originHeaderValue shape large
local notation "oldWords" => fun i f h g=>booksHeader book_ i h g f
local notation "heads_" => v.sampleHeads matB matH matG originWords oldWords mouth published (v.narrowValue Rbig)
local notation "data_" => v.originalValues heads_
local notation "inv_" => SortedInput.Broadcast.value v.ticketReadGeometry v.materialPitch (Gather.reaching Rbig)
local notation "digits_" => ticketAt v.ticketReadGeometry (SortedInput.values v.ticketReadGeometry data_ inv_)
variable (typed:BookPointers (v.returnedBook shape V))
    (room₁:∀j h g,11*(v.ticketRoles (ticketAt v.ticketReadGeometry (SortedInput.values v.ticketReadGeometry
        (v.originalValues (v.sampleHeads matB matH matG (v.originHeaderValue shape large)
          (fun i f h g=>booksHeader (v.returnedBook shape V) i h g f) mouth published (v.narrowValue Rbig)))
        (SortedInput.Broadcast.value v.ticketReadGeometry v.materialPitch (Gather.reaching Rbig)))) j 1 h g).val+(v.ticketRoles (ticketAt v.ticketReadGeometry (SortedInput.values v.ticketReadGeometry
        (v.originalValues (v.sampleHeads matB matH matG (v.originHeaderValue shape large)
          (fun i f h g=>booksHeader (v.returnedBook shape V) i h g f) mouth published (v.narrowValue Rbig)))
        (SortedInput.Broadcast.value v.ticketReadGeometry v.materialPitch (Gather.reaching Rbig)))) j 2 h g).val<2^(v.resolver.size+2))
local notation "jobs_" => ofBooks book_ typed
  (fun i h g=>DescentDatedPublicGrain.withGrain v.chosenGrain (v.ticketSides digits_ i h g))
  (v.ticketRoles digits_) room₁

local notation "decodedJobs" => decodedBooks book_
  (fun i h g=>DescentDatedPublicGrain.withGrain v.chosenGrain (v.ticketSides digits_ i h g))
  (v.ticketRoles digits_) room₁

set_option maxHeartbeats 800000 in
include ticket arch tokens age radix ports mem room population prior priorCount old_live old_empty hp one pin sh unit
  pinCode arity op labels flags stored paid bitsFit birth v shape lo gs rad field hostFit V refD refK refN refC
  matB matH matG dFit blockFit receiverH stepFit Rbig nearFit origPrevious origBorn large «prefix» mouth published room₁ in
theorem registered_private_job_decoded (auth:stock)
    (arityFit:∀u a,((sh.sites u).recipe hp).arity a≤arity)
    (x:NodeOrder.All next) (j:Fin (args₁ x))
    (fits:(advance ticket arch prior x.1 x.2).val<v.resolver.nodes) (written:j.val<v.resolver.operands)
    (resident:∀(f : Fin 4) (l : Fin v.vector.lows),Values.Prefix hostFit ((small₁ j.val f) l)
      (V ((DescentOperandStateBanks.page (f.castLE (by decide : 4≤7)) ⟨j.val,written⟩).cast
        (congrArg (7*·) shape.operands)) l))
    (h:((baseShape (source x).1).recipe hp).UsedWord) (hidden:earlier_ x j=.inr h.val)
    (rankFits:breadth deg*2^k≤2^(v.resolver.size+2)) :
    resolve (((decodedJobs) (physicalJob x fits ⟨j.val,written⟩)).compiled (rh x.1) (rg x.1))=
      carriedLabel ticket arch hp one pin sh unit (atSlot₀ arityFit) (source x).1 h :=by
  let job:=physicalJob x fits ⟨j.val,written⟩
  let recHost:=cap.vertex (currentLabel ticket arch x.1 x.2).val.1.2
  let node:Fin v.resolver.nodes:=⟨(advance ticket arch prior x.1 x.2).val,fits⟩
  have stampFits:N₀<2^v.originBits:=by
    simpa only [PhysicalOrdinary.originCandidates,refD,refK,refN,refC] using v.originBits_fit
  obtain ⟨donor,arg,word,inHalo,carried,_,_,keyEq,words⟩:=registered_private_digits
    (ticket:=ticket) (arch:=arch) (tokens:=tokens) (age:=age) (radix:=radix)
    (ports:=ports) (mem:=mem) (room:=room) (population:=population) (prior:=prior) (priorCount:=priorCount)
    (old_live:=old_live) (old_empty:=old_empty) (hp:=hp) (one:=one) (pin:=pin) (sh:=sh) (unit:=unit)
    (pinCode:=pinCode) (arity:=arity) (op:=op) (labels:=labels) (flags:=flags) (stored:=stored)
    (paid:=paid) (bitsFit:=bitsFit) (birth:=birth) (v:=v) (shape:=shape) (lo:=lo) (gs:=gs)
    (rad:=rad) (field:=field) (hostFit:=hostFit) (V:=V) auth stampFits arityFit x j fits written resident h hidden
  obtain ⟨_,sorted,visit,address,ranked,_,walked,stamped⟩:=old_occurrence_coordinates ticket arch tokens age radix
    fits₀ prior priorCount old_live old_empty origPrevious origBorn auth x.1 x.2 donor carried stampFits fits
  let original:=cap.vertex ((A).pos donor.1).2
  let oldBlock:=(A).block donor.1
  let oldNode:=((bounded arch.bit prior donor.1).trans (Fin.castLEEmb fits₀)) donor.2
  have receiver:DepotRAM.Material.Route.receiver v.material.oldHosts v.materialPitch ((rh x.1).castLE matH)=
      some (recHost.castLE receiverH):=by
    have divide:(home₁ x.1).val/pitch₁=recHost.val:=
      congrArg (fun a=>a.1.val) (older_location ticket arch age radix x.1 x.2).1
    have pitchPos:0<pitch₁:=Nat.zero_lt_of_lt (localIndex ticket arch x.1 x.2).isLt
    change (if valid:0<v.materialPitch ∧ (home₁ x.1).val/v.materialPitch<v.material.oldHosts
      then some (⟨_,valid.2⟩:Fin v.material.oldHosts) else none)=_
    rw [stepFit,dite_eq_left ⟨pitchPos,by rw [divide];exact recHost.isLt.trans_le receiverH⟩]
    exact congrArg some (Fin.ext divide)
  obtain ⟨rankAt,visitAt⟩:=Sorted.rack_paths dFit receiverH smallRoster Rbig nearFit recHost original
    sorted visit ranked walked
  let «alias»:=(DescentLocalPrivateNames.firstAlias ((sh.sites donor.1).recipe hp) ((atSlot₀ arityFit) donor.1) word).val
  have fieldAt (f:Fin 6) (roomAt:(![1,sorted.val,oldBlock.val,oldNode.val,0,0] f)<2^v.operandShortBits) :
      ((data_).origin job f (rh x.1) (rg x.1)).val=![1,sorted.val,oldBlock.val,oldNode.val,0,0] f:=by
    change (v.originHeaderValue shape large job f (rh x.1) (rg x.1)).val=_
    exact v.old_origin_digit shape large hostFit smallW refD refK refN refC lo gs rad rfl «prefix»
      (block₁ x.1) node ⟨j.val,written⟩ (home₁ x.1) (group₁ x.1) sorted oldBlock oldNode stamped f roomAt
  have digitRoom:2^(v.resolver.size+2)≤2^v.operandShortBits:=
    Nat.pow_le_pow_right (by decide) ((Nat.le_max_right ..).trans (Nat.le_max_left ..))
  have rootBits:1<2^v.operandShortBits:=
    (Nat.one_lt_pow (by omega : v.resolver.size+2≠0) (by decide:1<2)).trans_le digitRoom
  have walkBits:breadth deg≤2^v.operandShortBits:=
    (Nat.le_mul_of_pos_right _ (by positivity : 0<2^k)).trans (rankFits.trans digitRoom)
  have positivePath:0<breadth deg:=by unfold DescentHaloWalkRAM.breadth;positivity
  have blockBits:2^k≤2^v.operandShortBits:=
    (Nat.le_mul_of_pos_left _ positivePath).trans (rankFits.trans digitRoom)
  have flag:((data_).origin job 0 (rh x.1) (rg x.1)).val=1:=fieldAt 0 rootBits
  have ord:((data_).origin job 1 (rh x.1) (rg x.1)).val=sorted.val:=fieldAt 1 (sorted.isLt.trans_le walkBits)
  have blk:((data_).origin job 2 (rh x.1) (rg x.1)).val=oldBlock.val:=fieldAt 2 (oldBlock.isLt.trans_le blockBits)
  have kind:((data_).prior job 0 (rh x.1) (rg x.1)).val=(booksHeader book_ job (rh x.1) (rg x.1) 0).val:=
    v.original_prior_number heads_ job 0 (rh x.1) (rg x.1)
  have fitsKey:sorted.val*(fmt_).blocks+oldBlock.val<2^(v.resolver.size+2):=by
    rw [blockFit]
    have packed:sorted.val*2^k+oldBlock.val<breadth deg*2^k:=by
      simpa only [finProdFinEquiv_apply_val,Nat.add_comm,Nat.mul_comm] using (finProdFinEquiv (sorted,oldBlock)).isLt
    exact packed.trans_le rankFits
  have exactKey:=v.registered_carried_resolver_decoded matB matH matG originWords oldWords mouth published Rbig
    (recHost.castLE receiverH) (original.castLE receiverH) _ _ (rh x.1) (rg x.1) receiver visitAt rankAt
    book_ room₁ job oldBlock.val «alias» flag ord blk kind words fitsKey
  rw [keyEq,address]
  have scaled := congrArg (fun lanes : ℕ => Key.carried (sorted.val*lanes+oldBlock.val) «alias») blockFit
  exact exactKey.trans scaled

include ticket arch tokens age radix ports mem room population prior priorCount old_live old_empty hp one pin sh unit
  pinCode arity op labels flags stored paid bitsFit birth v shape lo gs rad field hostFit V refD refK refN refC
  matB matH matG dFit blockFit receiverH stepFit Rbig nearFit origPrevious origBorn large «prefix» mouth published room₁ in
theorem registered_private_job (auth:stock)
    (arityFit:∀u a,((sh.sites u).recipe hp).arity a≤arity)
    (x:NodeOrder.All next) (j:Fin (args₁ x))
    (fits:(advance ticket arch prior x.1 x.2).val<v.resolver.nodes) (written:j.val<v.resolver.operands)
    (resident:∀(f : Fin 4) (l : Fin v.vector.lows),Values.Prefix hostFit ((small₁ j.val f) l)
      (V ((DescentOperandStateBanks.page (f.castLE (by decide : 4≤7)) ⟨j.val,written⟩).cast
        (congrArg (7*·) shape.operands)) l))
    (h:((baseShape (source x).1).recipe hp).UsedWord) (hidden:earlier_ x j=.inr h.val)
    (rankFits:breadth deg*2^k≤2^(v.resolver.size+2)) :
    resolve (((jobs_) (physicalJob x fits ⟨j.val,written⟩)).compiled (rh x.1) (rg x.1))=
      carriedLabel ticket arch hp one pin sh unit (atSlot₀ arityFit) (source x).1 h :=by
  exact registered_private_job_decoded (ticket:=ticket) (arch:=arch) (tokens:=tokens) (age:=age)
    (radix:=radix) (ports:=ports) (mem:=mem) (room:=room) (population:=population) (prior:=prior)
    (priorCount:=priorCount) (old_live:=old_live) (old_empty:=old_empty) (hp:=hp) (one:=one)
    (pin:=pin) (sh:=sh) (unit:=unit) (pinCode:=pinCode) (arity:=arity) (op:=op)
    (labels:=labels) (flags:=flags) (stored:=stored) (paid:=paid) (bitsFit:=bitsFit) (birth:=birth)
    (v:=v) (shape:=shape) (lo:=lo) (gs:=gs) (rad:=rad) (field:=field) (hostFit:=hostFit) (V:=V)
    (refD:=refD) (refK:=refK) (refN:=refN) (refC:=refC) (matB:=matB) (matH:=matH) (matG:=matG)
    (dFit:=dFit) (blockFit:=blockFit) (receiverH:=receiverH) (stepFit:=stepFit) (Rbig:=Rbig)
    (nearFit:=nearFit) (origPrevious:=origPrevious) (origBorn:=origBorn) (large:=large)
    («prefix»:=«prefix») (mouth:=mouth) (published:=published) (room₁:=room₁)
    auth arityFit x j fits written resident h hidden rankFits

end
end Hierarchy.DescentLocalArchiveOrder.PaddedOrigin

end OAI
