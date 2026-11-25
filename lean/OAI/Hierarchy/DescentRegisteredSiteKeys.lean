import OAI.Hierarchy.DescentRegisteredDecodedPinJob
import OAI.Hierarchy.DescentReachedPhysicalPrivateJob
import OAI.Hierarchy.DescentReachedCableOutcome

namespace OAI
/-! Original dated operand receipts at all active nodes of the reached site. -/
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
private theorem issuedMouthKey {F P Tag Port : Type} [Field F] (model : PhysicalOrdinary F P)
    (jobs : Fin model.resolver.jobs → DescentDatedPriorOperand.Source model.resolver)
    (block : Fin model.resolver.blocks) (host : Fin model.resolver.hosts) (groupIx : Fin model.resolver.groups)
    (recipe : DescentKernelHistory.Recipe Tag Port) (node : recipe.Node ↪ Fin model.resolver.nodes)
    (arity : ∀ u, recipe.arity u ≤ model.resolver.operands) (slot : DescentLocalPrivateNames.Slot recipe) :
    DescentPackedOperand.resolve (model.issuedFragment jobs block host groupIx
      (model.finalChart.mouths recipe node arity slot)) =
    DescentPackedOperand.resolve ((jobs (model.resolver.index (block,node slot.1,slot.2.castLE (arity slot.1)))).compiled host groupIx) := by
  exact congrArg (fun p : Fin model.resolver.nodes × Fin model.resolver.operands =>
    DescentPackedOperand.resolve ((jobs (model.resolver.index (block,p))).compiled host groupIx))
    (model.finalChart.slots.symm_apply_apply (node slot.1,slot.2.castLE (arity slot.1)))

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
local notation:max "physicalJob" x:arg fit:arg arg:arg =>
  v.resolver.index ((physB (x).1).cast shape.blocks.symm,⟨(advance ticket arch prior (x).1 (x).2).val,fit⟩,arg)
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

local notation "venueName" => cap.vertex.trans (Fin.castLEEmb receiverH)

include dFit nearFit in
/-- Every geometric neighbor occurs in the actual padded dated roster. -/
theorem material_listed (a t:cap.V) (hit:t∈(A).near a) :
    ∃j,Rbig (venueName a) j=some (venueName t) :=by
  obtain ⟨j,socket⟩:=(DescentGroupPeerOrder.hostRoster_mem A (cap.vertex.trans Fin.valEmbedding) a t).mp hit
  refine ⟨j.cast dFit.symm,?_⟩
  change Rbig ((cap.vertex a).castLE receiverH) _=_
  rw [nearFit]
  simp [hostRotor,socket]

local notation "listed₁" => material_listed (cap:=cap) (v:=v) (Rbig:=Rbig)
  (dFit:=dFit) (receiverH:=receiverH) (nearFit:=nearFit)
local notation "haloRoot" site:arg => receivedRoot ticket arch hp one pin sh unit venueName Rbig listed₁ site
local notation "receipt" x:arg n:arg f:arg => resolve (((jobs_) (physicalJob x n f)).compiled (rh x.1) (rg x.1))
local notation "cableCase" x:arg j:arg e:arg k:arg len:arg val:arg =>
  CableOutcome ticket arch hp one pin sh unit venueName Rbig listed₁ x j e k len val
local notation "pageAt" index:arg f:arg => ((DescentOperandStateBanks.page ((f).castLE (by decide : 4≤7)) index).cast
  (congrArg (7*·) shape.operands))

include old_live old_empty stored paid bitsFit nearFit «prefix» stepFit blockFit in
theorem registered_input_response (auth:stock)
    (arityFit:∀u a,((sh.sites u).recipe hp).arity a≤arity)
    (x:NodeOrder.All next) (j:Fin (args₁ x))
    (fits:(advance ticket arch prior x.1 x.2).val<v.resolver.nodes) (written:j.val<v.resolver.operands)
    (resident:∀(f : Fin 4) (l : Fin v.vector.lows),Values.Prefix hostFit ((small₁ j.val f) l) (V (pageAt ⟨j.val,written⟩ f) l))
    (rankFits:breadth deg*2^k≤2^(v.resolver.size+2))
    (cableJob:∀(e:Incident (M) (source x).1) k (len:(k+1)*p≤(M).width e.val),
      earlier_ x j=.inl ⟨.inl e,k,len⟩→cableCase x j e k len (receipt x fits ⟨j.val,written⟩)) :
    InputResponse ticket arch hp one pin sh unit (atSlot₀ arityFit) (fun _ _=>0) (haloRoot x.1)
      x j (receipt x fits ⟨j.val,written⟩) :=by
  refine ⟨?_,?_,?_,?_⟩
  · intro h hidden
    exact registered_private_job
      (ticket:=ticket) (arch:=arch) (tokens:=tokens) (age:=age) (radix:=radix)
      (ports:=ports) (mem:=mem) (room:=room) (population:=population) (prior:=prior)
      (priorCount:=priorCount) (old_live:=old_live) (old_empty:=old_empty) (hp:=hp) (one:=one)
      (pin:=pin) (sh:=sh) (unit:=unit) (pinCode:=pinCode) (arity:=arity)
      (op:=op) (labels:=labels) (flags:=flags) (stored:=stored) (paid:=paid)
      (bitsFit:=bitsFit) (birth:=birth) (v:=v) (shape:=shape) (lo:=lo)
      (gs:=gs) (rad:=rad) (field:=field) (hostFit:=hostFit) (V:=V)
      (refD:=refD) (refK:=refK) (refN:=refN) (refC:=refC) (matB:=matB)
      (matH:=matH) (matG:=matG) (dFit:=dFit) (blockFit:=blockFit) (receiverH:=receiverH)
      (stepFit:=stepFit) (Rbig:=Rbig) (nearFit:=nearFit) (origPrevious:=origPrevious) (origBorn:=origBorn)
      (large:=large) («prefix»:=«prefix») (mouth:=mouth) (published:=published) (typed:=typed)
      (room₁:=room₁)
      auth arityFit x j fits written resident h hidden rankFits
  · intro e k len same arg
    exact (cableJob e k len arg).captured same
  · intro e k len distinct arg
    exact (cableJob e k len arg).survivor distinct
  · intro z chunk len external
    refine ⟨pinCode z.val,?_⟩
    have stampFits:N₀<2^v.originBits:=by
      simpa only [PhysicalOrdinary.originCandidates,refD,refK,refN,refC] using v.originBits_fit
    exact registered_pin_job
      (ticket:=ticket) (arch:=arch) (tokens:=tokens) (age:=age) (radix:=radix)
      (ports:=ports) (mem:=mem) (room:=room) (population:=population) (prior:=prior)
      (priorCount:=priorCount) (old_live:=old_live) (old_empty:=old_empty) (hp:=hp) (one:=one)
      (pin:=pin) (sh:=sh) (unit:=unit) (pinCode:=pinCode) (arity:=arity)
      (op:=op) (labels:=labels) (flags:=flags) (stored:=stored) (paid:=paid)
      (bitsFit:=bitsFit) (birth:=birth) (v:=v) (shape:=shape) (lo:=lo)
      (gs:=gs) (rad:=rad) (field:=field) (hostFit:=hostFit) (V:=V)
      (typed:=typed) (digits:=digits_) (grain:=v.chosenGrain) (room₁:=room₁)
      auth stampFits x j fits written resident z chunk len external

local notation "siteNode" t:arg nc:arg => ((advance ticket arch prior t).toEmbedding.trans (Fin.castLEEmb nc))
local notation "actualArg" _t:arg s:arg ar:arg => s.2.castLE (ar s.1)
local notation "siteKey" t:arg nc:arg ar:arg s:arg => resolve (v.issuedFragment jobs_
  ((physB t).cast shape.blocks.symm) (rh t) (rg t)
  (v.finalChart.mouths (((after).sites t).recipe hp) (siteNode t nc) ar s))


theorem registered_fragment (t:n.result.graph.Site) (capacity:Fintype.card ((next).recipe t).Node≤v.resolver.nodes)
    (written:∀u,(((after).sites t).recipe hp).arity u≤v.resolver.operands)
    (s:DescentLocalPrivateNames.Slot (((after).sites t).recipe hp)) :
    siteKey t capacity written s=receipt (⟨t,s.1⟩:NodeOrder.All next)
      ((advance ticket arch prior t s.1).isLt.trans_le capacity) (s.2.castLE (written s.1)) :=by
  exact issuedMouthKey v (jobs_) ((physB t).cast shape.blocks.symm) (rh t) (rg t)
    (((after).sites t).recipe hp) (siteNode t capacity) written s

include old_live old_empty stored paid bitsFit in
/-- The exterior field at the final chart's actual mouth and original returned
RAM book retains the immutable pin name and selected block. -/
theorem registered_site_pin (auth:stock) {wide:ℕ} (stampFits:N₀<2^wide)
    (t:n.result.graph.Site) (capacity:Fintype.card ((next).recipe t).Node≤v.resolver.nodes)
    (written:∀u,(((after).sites t).recipe hp).arity u≤v.resolver.operands)
    (s:DescentLocalPrivateNames.Slot (((after).sites t).recipe hp))
    (resident:∀(f : Fin 4) (l : Fin v.vector.lows),Values.Prefix hostFit ((small₁ s.2.val f) l) (V (pageAt (s.2.castLE (written s.1)) f) l))
    (z:Attached n.result.graph t) (chunk:ℕ) (len:(chunk+1)*p≤bits z.val)
    (found:(((after).sites t).recipe hp).operand s.1 s.2=.inl ⟨.inr z,chunk,len⟩) :
    siteKey t capacity written s=.pin (pinCode z.val) chunk :=by
  rw [registered_fragment (lo:=lo) (gs:=gs) (rad:=rad)]
  exact registered_final_pin
      (ticket:=ticket) (arch:=arch) (tokens:=tokens) (age:=age) (radix:=radix)
      (ports:=ports) (mem:=mem) (room:=room) (population:=population) (prior:=prior)
      (priorCount:=priorCount) (old_live:=old_live) (old_empty:=old_empty) (hp:=hp) (one:=one)
      (pin:=pin) (sh:=sh) (unit:=unit) (pinCode:=pinCode) (arity:=arity)
      (op:=op) (labels:=labels) (flags:=flags) (stored:=stored) (paid:=paid)
      (bitsFit:=bitsFit) (birth:=birth) (v:=v) (shape:=shape) (lo:=lo)
      (gs:=gs) (rad:=rad) (field:=field) (hostFit:=hostFit) (V:=V)
      (typed:=typed) (digits:=digits_) (grain:=v.chosenGrain) (room₁:=room₁)
    auth stampFits ⟨t,s.1⟩ s.2 ((advance ticket arch prior t s.1).isLt.trans_le capacity)
    (s.2.isLt.trans_le (written s.1)) resident z chunk len found

include old_live old_empty stored paid bitsFit nearFit «prefix» stepFit blockFit in
/-- A single dated cable receipt per original raw public incidence, together
with the real predecessor headers and measured origin, covers every resolver
job of the reached site in its native scalar and operand order. -/
theorem registered_site_keys (auth:stock)
    (arityFit:∀u a,((sh.sites u).recipe hp).arity a≤arity)
    (t:n.result.graph.Site) (capacity:Fintype.card ((next).recipe t).Node≤v.resolver.nodes)
    (written:∀u,(((after).sites t).recipe hp).arity u≤v.resolver.operands)
    (resident:∀(s:DescentLocalPrivateNames.Slot (((after).sites t).recipe hp)) (f : Fin 4) (l : Fin v.vector.lows),
      Values.Prefix hostFit ((small₁ s.2.val f) l) (V (pageAt (actualArg t s written) f) l))
    (rankFits:breadth deg*2^k≤2^(v.resolver.size+2))
    (cableJob:∀(s:DescentLocalPrivateNames.Slot (((after).sites t).recipe hp))
      (e:Incident (M) (source (⟨t,s.1⟩:NodeOrder.All next)).1) k (len:(k+1)*p≤(M).width e.val),
      earlier_ (⟨t,s.1⟩:NodeOrder.All next) s.2=.inl ⟨.inl e,k,len⟩→
        cableCase (⟨t,s.1⟩:NodeOrder.All next) s.2 e k len (siteKey t capacity written s)) :
    v.SourceKeys jobs_ ((physB t).cast shape.blocks.symm) (rh t) (rg t)
      (((after).sites t).recipe hp) (siteNode t capacity) written
      ((reachedPrivateKey ticket arch hp one pin sh unit (atSlot₀ arityFit) (fun _ _=>0) t).trans
        (DescentOrdinaryNativeNames.captures (haloRoot t))) :=by
  refine site_keys ticket arch hp one pin sh unit (atSlot₀ arityFit) (fun _ _ => 0) (haloRoot t)
    t v jobs_ ((physB t).cast shape.blocks.symm) (rh t) (rg t) (siteNode t capacity) written ?_
  intro s
  let x : NodeOrder.All next := ⟨t,s.1⟩
  have nodeFits := (advance ticket arch prior t s.1).isLt.trans_le capacity
  have argFits := s.2.isLt.trans_le (written s.1)
  have keyEq : siteKey t capacity written s = receipt x nodeFits ⟨s.2.val,argFits⟩ := by
    apply registered_fragment (lo:=lo) (gs:=gs) (rad:=rad)
  have reply := registered_input_response
      (ticket:=ticket) (arch:=arch) (tokens:=tokens) (age:=age) (radix:=radix)
      (ports:=ports) (mem:=mem) (room:=room) (population:=population) (prior:=prior)
      (priorCount:=priorCount) (old_live:=old_live) (old_empty:=old_empty) (hp:=hp) (one:=one)
      (pin:=pin) (sh:=sh) (unit:=unit) (pinCode:=pinCode) (arity:=arity)
      (op:=op) (labels:=labels) (flags:=flags) (stored:=stored) (paid:=paid)
      (bitsFit:=bitsFit) (birth:=birth) (v:=v) (shape:=shape) (lo:=lo)
      (gs:=gs) (rad:=rad) (field:=field) (hostFit:=hostFit) (V:=V)
      (refD:=refD) (refK:=refK) (refN:=refN) (refC:=refC) (matB:=matB)
      (matH:=matH) (matG:=matG) (dFit:=dFit) (blockFit:=blockFit) (receiverH:=receiverH)
      (stepFit:=stepFit) (Rbig:=Rbig) (nearFit:=nearFit) (origPrevious:=origPrevious) (origBorn:=origBorn)
      (large:=large) («prefix»:=«prefix») (mouth:=mouth) (published:=published) (typed:=typed)
      (room₁:=room₁)
    auth arityFit x s.2 nodeFits argFits (resident s) rankFits (fun e d len arg =>
      Eq.mp (congrArg (fun (resultKey : DescentPackedOperand.Key) => cableCase x s.2 e d len resultKey) keyEq) (cableJob s e d len arg))
  exact Eq.mpr (congrArg (fun (resultKey : DescentPackedOperand.Key) => InputResponse ticket arch hp one pin sh unit
    (atSlot₀ arityFit) (fun _ _ => 0) (haloRoot t) x s.2 resultKey) keyEq) reply

section IssuedRow
local notation "decodedJobs" => decodedBooks book_
  (fun i h g=>DescentDatedPublicGrain.withGrain v.chosenGrain (v.ticketSides digits_ i h g))
  (v.ticketRoles digits_) room₁
local notation "decodedRead" x:arg n:arg f:arg => resolve (((decodedJobs) (physicalJob x n f)).compiled (rh x.1) (rg x.1))
local notation "decodedSite" t:arg nc:arg ar:arg s:arg => resolve (v.issuedFragment decodedJobs
  ((physB t).cast shape.blocks.symm) (rh t) (rg t)
  (v.finalChart.mouths (((after).sites t).recipe hp) (siteNode t nc) ar s))

include old_live old_empty stored paid bitsFit nearFit «prefix» stepFit blockFit in
theorem registered_input_response_decoded (auth:stock)
    (arityFit:∀u a,((sh.sites u).recipe hp).arity a≤arity)
    (x:NodeOrder.All next) (j:Fin (args₁ x))
    (fits:(advance ticket arch prior x.1 x.2).val<v.resolver.nodes) (written:j.val<v.resolver.operands)
    (resident:∀(f : Fin 4) (l : Fin v.vector.lows),Values.Prefix hostFit ((small₁ j.val f) l) (V (pageAt ⟨j.val,written⟩ f) l))
    (rankFits:breadth deg*2^k≤2^(v.resolver.size+2))
    (cableJob:∀(e:Incident (M) (source x).1) k (len:(k+1)*p≤(M).width e.val),
      earlier_ x j=.inl ⟨.inl e,k,len⟩→cableCase x j e k len (decodedRead x fits ⟨j.val,written⟩)) :
    InputResponse ticket arch hp one pin sh unit (atSlot₀ arityFit) (fun _ _=>0) (haloRoot x.1)
      x j (decodedRead x fits ⟨j.val,written⟩) :=by
  refine ⟨?_,?_,?_,?_⟩
  · intro h hidden
    exact registered_private_job_decoded
      (ticket:=ticket) (arch:=arch) (tokens:=tokens) (age:=age) (radix:=radix)
      (ports:=ports) (mem:=mem) (room:=room) (population:=population) (prior:=prior)
      (priorCount:=priorCount) (old_live:=old_live) (old_empty:=old_empty) (hp:=hp) (one:=one)
      (pin:=pin) (sh:=sh) (unit:=unit) (pinCode:=pinCode) (arity:=arity)
      (op:=op) (labels:=labels) (flags:=flags) (stored:=stored) (paid:=paid)
      (bitsFit:=bitsFit) (birth:=birth) (v:=v) (shape:=shape) (lo:=lo)
      (gs:=gs) (rad:=rad) (field:=field) (hostFit:=hostFit) (V:=V)
      (refD:=refD) (refK:=refK) (refN:=refN) (refC:=refC) (matB:=matB)
      (matH:=matH) (matG:=matG) (dFit:=dFit) (blockFit:=blockFit) (receiverH:=receiverH)
      (stepFit:=stepFit) (Rbig:=Rbig) (nearFit:=nearFit) (origPrevious:=origPrevious) (origBorn:=origBorn)
      (large:=large) («prefix»:=«prefix») (mouth:=mouth) (published:=published)
      (room₁:=room₁)
      auth arityFit x j fits written resident h hidden rankFits
  · intro e k len same arg
    exact (cableJob e k len arg).captured same
  · intro e k len distinct arg
    exact (cableJob e k len arg).survivor distinct
  · intro z chunk len external
    refine ⟨pinCode z.val,?_⟩
    have stampFits:N₀<2^v.originBits:=by
      simpa only [PhysicalOrdinary.originCandidates,refD,refK,refN,refC] using v.originBits_fit
    apply DescentDatedPriorOperand.decoded_pin
    exact registered_pin_digits
      (ticket:=ticket) (arch:=arch) (tokens:=tokens) (age:=age) (radix:=radix)
      (ports:=ports) (mem:=mem) (room:=room) (population:=population) (prior:=prior)
      (priorCount:=priorCount) (old_live:=old_live) (old_empty:=old_empty) (hp:=hp) (one:=one)
      (pin:=pin) (sh:=sh) (unit:=unit) (pinCode:=pinCode) (arity:=arity)
      (op:=op) (labels:=labels) (flags:=flags) (stored:=stored) (paid:=paid)
      (bitsFit:=bitsFit) (birth:=birth) (v:=v) (shape:=shape) (lo:=lo)
      (gs:=gs) (rad:=rad) (field:=field) (hostFit:=hostFit) (V:=V)

      auth stampFits x j fits written resident z chunk len external

theorem registered_fragment_decoded (t:n.result.graph.Site) (capacity:Fintype.card ((next).recipe t).Node≤v.resolver.nodes)
    (written:∀u,(((after).sites t).recipe hp).arity u≤v.resolver.operands)
    (s:DescentLocalPrivateNames.Slot (((after).sites t).recipe hp)) :
    decodedSite t capacity written s=decodedRead (⟨t,s.1⟩:NodeOrder.All next)
      ((advance ticket arch prior t s.1).isLt.trans_le capacity) (s.2.castLE (written s.1)) :=by
  exact issuedMouthKey v (decodedJobs) ((physB t).cast shape.blocks.symm) (rh t) (rg t)
    (((after).sites t).recipe hp) (siteNode t capacity) written s

include old_live old_empty stored paid bitsFit in
theorem registered_site_pin_decoded (auth:stock) {wide:ℕ} (stampFits:N₀<2^wide)
    (t:n.result.graph.Site) (capacity:Fintype.card ((next).recipe t).Node≤v.resolver.nodes)
    (written:∀u,(((after).sites t).recipe hp).arity u≤v.resolver.operands)
    (s:DescentLocalPrivateNames.Slot (((after).sites t).recipe hp))
    (resident:∀(f : Fin 4) (l : Fin v.vector.lows),Values.Prefix hostFit ((small₁ s.2.val f) l) (V (pageAt (s.2.castLE (written s.1)) f) l))
    (z:Attached n.result.graph t) (chunk:ℕ) (len:(chunk+1)*p≤bits z.val)
    (found:(((after).sites t).recipe hp).operand s.1 s.2=.inl ⟨.inr z,chunk,len⟩) :
    decodedSite t capacity written s=.pin (pinCode z.val) chunk :=by
  rw [registered_fragment_decoded (lo:=lo) (gs:=gs) (rad:=rad)]
  exact registered_final_pin_decoded
      (ticket:=ticket) (arch:=arch) (tokens:=tokens) (age:=age) (radix:=radix)
      (ports:=ports) (mem:=mem) (room:=room) (population:=population) (prior:=prior)
      (priorCount:=priorCount) (old_live:=old_live) (old_empty:=old_empty) (hp:=hp) (one:=one)
      (pin:=pin) (sh:=sh) (unit:=unit) (pinCode:=pinCode) (arity:=arity)
      (op:=op) (labels:=labels) (flags:=flags) (stored:=stored) (paid:=paid)
      (bitsFit:=bitsFit) (birth:=birth) (v:=v) (shape:=shape) (lo:=lo)
      (gs:=gs) (rad:=rad) (field:=field) (hostFit:=hostFit) (V:=V)
      (digits:=digits_) (grain:=v.chosenGrain) (room₁:=room₁)
    auth stampFits ⟨t,s.1⟩ s.2 ((advance ticket arch prior t s.1).isLt.trans_le capacity)
    (s.2.isLt.trans_le (written s.1)) resident z chunk len found

variable (birthAt:ℕ→Fin 4→Block k→Fin cap.placement.cap→Fin 6→Fin (Fintype.card cap.V)→Fin (S.groupCount i)→Cell ports.operandBits)
local notation "birthRow" n:arg f:arg l:arg => (Values.transport lo gs rad field (rangeValues ticket arch tokens age radix
  priorCount (priorAt n f) (birthAt n f)) l)

include old_live old_empty stored paid bitsFit nearFit «prefix» stepFit blockFit in
theorem registered_site_keys_decoded (auth:stock)
    (arityFit:∀u a,((sh.sites u).recipe hp).arity a≤arity)
    (t:n.result.graph.Site) (capacity:Fintype.card ((next).recipe t).Node≤v.resolver.nodes)
    (written:∀u,(((after).sites t).recipe hp).arity u≤v.resolver.operands)
    (resident:∀(s:DescentLocalPrivateNames.Slot (((after).sites t).recipe hp)) (f : Fin 4) (l : Fin v.vector.lows),
      Values.Prefix hostFit (birthRow s.2.val f l) (V (pageAt (actualArg t s written) f) l))
    (rankFits:breadth deg*2^k≤2^(v.resolver.size+2))
    (cableJob:∀(s:DescentLocalPrivateNames.Slot (((after).sites t).recipe hp))
      (e:Incident (M) (source (⟨t,s.1⟩:NodeOrder.All next)).1) k (len:(k+1)*p≤(M).width e.val),
      earlier_ (⟨t,s.1⟩:NodeOrder.All next) s.2=.inl ⟨.inl e,k,len⟩→
        cableCase (⟨t,s.1⟩:NodeOrder.All next) s.2 e k len (decodedSite t capacity written s)) :
    v.SourceKeys decodedJobs ((physB t).cast shape.blocks.symm) (rh t) (rg t)
      (((after).sites t).recipe hp) (siteNode t capacity) written
      ((reachedPrivateKey ticket arch hp one pin sh unit (atSlot₀ arityFit) (fun _ _=>0) t).trans
        (DescentOrdinaryNativeNames.captures (haloRoot t))) :=by
  refine site_keys ticket arch hp one pin sh unit (atSlot₀ arityFit) (fun _ _ => 0) (haloRoot t)
    t v decodedJobs ((physB t).cast shape.blocks.symm) (rh t) (rg t) (siteNode t capacity) written ?_
  intro s
  let x : NodeOrder.All next := ⟨t,s.1⟩
  have nodeFits := (advance ticket arch prior t s.1).isLt.trans_le capacity
  have argFits := s.2.isLt.trans_le (written s.1)
  have keyEq : decodedSite t capacity written s = decodedRead x nodeFits ⟨s.2.val,argFits⟩ := by
    apply registered_fragment_decoded (lo:=lo) (gs:=gs) (rad:=rad)
  have reply := registered_input_response_decoded
      (ticket:=ticket) (arch:=arch) (tokens:=tokens) (age:=age) (radix:=radix)
      (ports:=ports) (mem:=mem) (room:=room) (population:=population) (prior:=prior)
      (priorCount:=priorCount) (old_live:=old_live) (old_empty:=old_empty) (hp:=hp) (one:=one)
      (pin:=pin) (sh:=sh) (unit:=unit) (pinCode:=pinCode) (arity:=arity)
      (op:=op) (labels:=labels) (flags:=flags) (stored:=stored) (paid:=paid)
      (bitsFit:=bitsFit) (birth:=birthAt s.2.val) (v:=v) (shape:=shape) (lo:=lo)
      (gs:=gs) (rad:=rad) (field:=field) (hostFit:=hostFit) (V:=V)
      (refD:=refD) (refK:=refK) (refN:=refN) (refC:=refC) (matB:=matB)
      (matH:=matH) (matG:=matG) (dFit:=dFit) (blockFit:=blockFit) (receiverH:=receiverH)
      (stepFit:=stepFit) (Rbig:=Rbig) (nearFit:=nearFit) (origPrevious:=origPrevious) (origBorn:=origBorn)
      (large:=large) («prefix»:=«prefix») (mouth:=mouth) (published:=published)
      (room₁:=room₁)
    auth arityFit x s.2 nodeFits argFits (resident s) rankFits (fun e d len arg =>
      Eq.mp (congrArg (fun (resultKey : DescentPackedOperand.Key) => cableCase x s.2 e d len resultKey) keyEq) (cableJob s e d len arg))
  exact Eq.mpr (congrArg (fun (resultKey : DescentPackedOperand.Key) => InputResponse ticket arch hp one pin sh unit
    (atSlot₀ arityFit) (fun _ _ => 0) (haloRoot t) x s.2 resultKey) keyEq) reply

end IssuedRow

end
end Hierarchy.DescentLocalArchiveOrder.PaddedOrigin

end OAI
