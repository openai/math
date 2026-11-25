import OAI.Hierarchy.DescentRegisteredCableOriginWords
import OAI.Hierarchy.DescentReachedPhysicalBornHeader
import OAI.Hierarchy.DescentRegisteredBornPorts
import OAI.Hierarchy.DescentOrdinaryRosterRead
import OAI.Hierarchy.DescentRegisteredReceiver
import OAI.Hierarchy.DescentRegisteredCableJobs
import OAI.Hierarchy.DescentRegisteredSiteKeys
import OAI.Hierarchy.DescentRegisteredCableAlive
import OAI.Hierarchy.DescentDatedSourcePublicPointer

namespace OAI
/-! Native cable jobs at the literal reached node, source block, register and cohort. -/
namespace Hierarchy.DescentOrdinaryBorn

/-- The chunk in a newborn mouth is its zero-based offset inside one consecutive
role. Every earlier role contributes a nonnegative prefix to the operand number. -/
theorem mouth_chunk_le (B:Spec) (z prof:ℕ) (party:Fin 6) {arg:ℕ} {m:Mouth}
    (hit:mouth B z prof party arg=some m) : m.chunk≤arg:=by
  have «prefix» (xs:List (Fin (Fintype.card (DescentKernelHistory.RolePort party)))) (j:ℕ)
      (atRow:(xs.flatMap (group B z prof party))[j]?=some m) : m.chunk≤j:=by
    induction xs generalizing j with
    | nil => simp at atRow
    | cons i rest ih =>
      rw [List.flatMap_cons] at atRow
      by_cases before:j<(group B z prof party i).length
      · rw [List.getElem?_append_left before] at atRow
        obtain ⟨b,eq⟩:=List.getElem?_eq_some_iff.mp atRow
        have same:=congrArg Mouth.chunk eq
        simpa [group] using same.ge
      · rw [List.getElem?_append_right (Nat.le_of_not_gt before)] at atRow
        exact (ih _ atRow).trans (Nat.sub_le ..)
  exact «prefix» _ _ hit

end Hierarchy.DescentOrdinaryBorn

namespace Hierarchy.DescentLocalArchiveOrder.PaddedOrigin
open DescentColonies DescentParallelBase.ParentFilter DescentOrdinaryMouthReturn DescentSixParty.Chronology.PhysicalOrdinary
open ThreeFlat.RAM PhysicalProcedure
open DescentCableDonorNames DescentOrdinaryDonorHalo DescentSixParty.StarKeys DescentGL DescentWalshTables
open Computability.BorderVNP.Crossing DescentSixParty DescentSixParty.Chronology DescentStageEdgeReceipt
open DescentCompiler DescentKernelHistory DescentBundleHistory DescentHostDirectory DescentHostDegree
open DescentNetworkPartition DescentPackedOperand DescentSharedCableNames DescentPacking.PackedMatch.Local
open DescentGroupPeerOrder DescentPacking.PackedMatch.Local.Stage DescentSortedHaloRaster DescentHaloWalkRAM DescentSIMDLookup
open DescentScalarVenueMask DescentHostDirectory.SiteDecode DescentOrdinaryLocalBirth DescentPackedActorMask
open DescentOrdinaryAtomFieldRAM.ScalarOperand DescentOperandVectorArena DescentRetainedRangeDigits
open DescentOperandStateBanks DescentDatedPriorOperand DescentDatedOperandReadPipeline DescentDatedOperandCoordinates
open DescentRawCablePanel DescentPackedColony DescentPaidResidentCount DescentDatedAddressBook
open DescentOrdinaryAtomFieldRAM DescentOrdinaryOriginMask DescentOrdinaryOriginPorts DescentHistoryOrder
open DescentOrdinaryBorn DescentPacking DescentPackedZip DescentOrdinaryRasterReturn
open Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM DescentScalarBookReshape
open scoped Classical Fin.CommRing
set_option quotPrecheck false
set_option hygiene false
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

variable {F P:Type} [Field F] (v:PhysicalOrdinary F P)
local notation "phys" => v.withIssuedSigned
local notation "S" => v.schedule
local notation "G" => v.gadget
local notation "cap" => v.prior
local notation "A" => (cap).placement
local notation "T" => (A).stage
local notation "D" => (A).degree
local notation "OH" => Fintype.card (cap).V
local notation "H" => v.area.H
local notation "og" => (S).groupCount v.age
local notation "ng" => (S).groupCount (v.age+1)
local notation "bk" => 2^v.k
local notation "walks" => breadth D
local notation "slots" => 2^(packExponent 20 D)+2
local notation "pitch₁" => (2^(v.k+1)-1)*slots
local notation "lowNames" => 2^(v.k+1)*slots
local notation "count₀" => 1+(A).cap*6
local notation "ℒ" => (phys).resolver
local notation "E" => (phys).material
local notation "Γ" => (phys).ticketReadGeometry
local notation "fmt" => v.ticket.depotShape v.short
local notation "rr" => BitDescription.scannedRows v.nonnegative T
local notation "used" => fun t:(rr).pairs=>(rr).picked (t,0)
local notation "native" => (cap).order.trans Fin.valEmbedding
local notation "units₀" => fun _:(rr).pairs=>(T).z
local notation "moves" => rotor A (groupRank Fin.valEmbedding ((cap).vertex.trans Fin.valEmbedding))
variable (oldFit:OH≤H)
local notation "host" => (cap).vertex.trans (Fin.castLEEmb oldFit)
local notation "R₀" => hostRotor host (hostRoster A ((host).trans Fin.valEmbedding))
theorem registered_listed (u t:(cap).V) (near:t∈(A).near u) : ∃j,R₀ (host u) j=some (host t) :=
  (original_hostRotor_rows A host u (host t)).2 ⟨t,near,rfl⟩

theorem registered_symmetric (a b:Fin H) (j:Fin D) (edge:R₀ a j=some b) :
    ∃i,R₀ b i=some a:=by
  by_cases hit:∃u,host u=a
  · obtain ⟨u,rfl⟩:=hit
    obtain ⟨t,near,rfl⟩:=(original_hostRotor_rows A host u b).1 ⟨j,edge⟩
    exact registered_listed v oldFit t u (((A).symmetric u t).mp near)
  · simp [hostRotor] at edge
    exact (hit edge.1).elim

local notation "listed₀" => registered_listed v oldFit
variable (selected:((T).result v.nonnegative).Choice) (choiceEq:HEq selected v.choice)
local notation "ac" => PhysicalOrdinary.atSelected v selected choiceEq
local notation "ticket" => (ac).link
local notation "target" => (ac).next
local notation "cProf" => (rr).profile selected
local notation "lay" => bestLayout (branchWidth G units₀ cProf)
local notation "group" => GadgetNetwork.newSite v.world.graph (rr).pick lay (rr).pack
local notation "key" => (activeChart ticket).key v.nonnegative T selected
variable (arch:Archive v.world)
local notation "next" => ((ticket).advance arch).bit
variable {w mb p stretch s Z:ℕ} (m:Memory w) (parts:Bank) (B:v.SelectedBoard oldFit R₀ selected m parts)
    (tokens:DescentColonies.Block v.k→Fin count₀→Fin OH→Fin og→DescentScalarVenueMask.Ticket walks lowNames)
local notation "stock" => Descriptors slots v.k (A).pos (A).block (ticketParent (he:=v.nonnegative) («T»:=T))
  (ticketSlot (c:=selected) ticket) (key∘group) (cap).vertex (Function.Embedding.refl _) moves tokens
variable (age:v.age<(S).length) (radix:(S).radix=2^v.k) (hp:0<p) (one:1≤ stretch) (pin:∀x,p∣v.bits x)
    (sh:WorldShape p stretch arch.bit) (unit:p∣(T).z)
    (ports:DatePorts) (mem:Memory w) (room:DatePorts.RangeRoom ports cap arch.bit)
    (population:OH≤ports.operandHosts) (prior:Local arch.bit)
    (counts:DescentColonies.Block v.k→Fin OH→Fin og→Cell mb)
    (live:∀u,(counts ((A).block u) ((cap).vertex ((A).pos u).2) ((A).pos u).1).val=Fintype.card (arch.bit.recipe u).Node)
    (empty:∀b h g,(¬∃u,(A).block u=b ∧ (cap).vertex ((A).pos u).2=h ∧ ((A).pos u).1=g)→counts b h g=0)
variable (pinCode:P→ℕ) (arity:ℕ) (op:RotorSpec) (labels:NodeOrder.All arch.bit→DescentPrimitivePalette.Label G s Z op)
    (flags:Fin (2^ports.venue.k)→Fin ports.nodes→Fin ports.operandHosts→Fin ports.venue.groups→ℕ)
local notation "ptr₀" => Reached.argumentPointer cap arch.bit prior sh hp pinCode arity
variable (stored:DatePorts.ArchiveRead ports cap arch.bit prior room sh op labels ptr₀ flags mem)
    (paid:∀v u,((sh.sites v).recipe hp).arity u≤ports.argumentsPerNode)
    (bitsFit:ports.operandBits*ports.nodes*ports.operandLanes≤w)
    (birth:Fin 4→DescentColonies.Block v.k→Fin (A).cap→Fin 6→Fin OH→Fin og→Cell ports.operandBits)
variable (shape:(phys).VectorShape) (lo:(phys).vector.lows=pitch₁) (gs:(phys).vector.groups=ng) (rad:(phys).vector.radix=bk)
    (field:(ℒ).size+2=ports.operandBits) (hostFit:OH≤(phys).vector.hosts)
    (V:References.Rows (phys).vector D v.k ports.nodes (A).cap ((ℒ).size+2) (DescentSharedCableNames.Packed.bits pitch₁) mb)
local notation:max "priorAt" n:arg f:arg => DatePorts.physicalHeaderSource ports cap arch.bit room population mem n f
local notation:max "rows₁" n:arg f:arg => rangeValues ticket arch tokens age radix counts (priorAt n f) (birth f)
local notation:max "small" n:arg f:arg => Values.transport lo gs rad field (rows₁ n f)
local notation "oldBook" => (phys).returnedBook shape V
variable (refD:(phys).reference.degree=D) (refK:(phys).reference.k=v.k)
    (refN:(phys).reference.oldNodes=ports.nodes) (refC:(phys).reference.capacity=(A).cap)
    (bl:(ℒ).blocks=(E).blocks) (hb:(ℒ).hosts≤(E).hosts) (mg:(ℒ).groups=(E).groups)
    (bands:og=(E).groups*(E).blocks) (stepFit:(phys).materialPitch=pitch₁) (blockFit:(E).blocks=bk)
variable {stampField:ℕ} (origPrevious:DescentColonies.Block v.k→Fin OH→Fin og→Cell (stampField*ports.nodes))
    (origBorn:DescentColonies.Block v.k→Fin (A).cap→Fin 6→Fin OH→Fin og→Cell stampField)
local notation "smallW" => rangeValues ticket arch tokens age radix counts origPrevious origBorn
variable (large:(phys).OriginalDonors stampField (DescentSharedCableNames.Packed.bits pitch₁) mb)
    («prefix»:∀l,Values.Prefix hostFit
      (Values.originTransport refD refK refN refC lo gs rad (rfl:stampField=stampField) smallW l) (large l))
local notation "orig" => (phys).originHeaderValue shape large
variable (wide:Fintype.card v.target.V≤(phys).signed.hosts)
local notation "serial" => v.retainedSerial oldFit R₀ selected m parts B choiceEq wide age radix bands
    (registered_symmetric v oldFit)
local notation "peer" => v.retainedPeer oldFit R₀ selected m parts B choiceEq wide age radix bands
    (registered_symmetric v oldFit)
variable (floor:ℕ) (entry:(phys).ArgumentEntry) (mat:entry.Match phys floor)
    (homes:(phys).bornBook.hosts=(phys).vector.hosts) (groups:(phys).bornBook.groups=(phys).vector.groups*(phys).vector.radix)
    (bits_:(phys).bornBook.bits=(ℒ).size+2)
    (U:References.Rows (phys).vector (phys).reference.degree (phys).reference.k (phys).reference.oldNodes (phys).reference.capacity
      ((ℒ).size+2) (DescentSharedCableNames.Packed.bits pitch₁) mb)
    (chip:Fin (phys).bornBook.hosts→Fin (phys).bornBook.groups→Cell (phys).bornBook.chipBits)
local notation "mouthRows" => (phys).headerMouthRows floor entry mat U homes groups bits_
local notation "ports₃" => fun j f h g=>take (((ℒ).index.symm j).2.1)
    ((phys).mouthHeaderValue floor entry mat shape mouthRows chip homes groups j f h g)
local notation:max "mouthPage" j:arg => (phys).headerMouthPage floor entry mat ((j).cast (shape.operands.trans mat.newArgs.symm))
local notation "oldWords" => fun j f h g=>booksHeader oldBook j h g f
local notation "data₀" => (phys).originalValues ((phys).sampleHeads bl hb mg orig oldWords ports₃
   ((phys).wideMaterialValues R₀ B.material bands serial peer) ((phys).narrowValue R₀))
local notation "ticketWords" => ticketAt Γ (SortedInput.values Γ data₀ ((phys).walkValues (Gather.reaching R₀)))
local notation "role₀" => (phys).ticketRoles ticketWords
variable (nameRoom:∀j h y,11*(role₀ j 1 h y).val+(role₀ j 2 h y).val<2^((ℒ).size+2))
local notation "jobs" => decodedBooks oldBook (fun j h y=>DescentDatedPublicGrain.withGrain (phys).chosenGrain
   ((phys).ticketSides ticketWords j h y)) role₀ nameRoom
local notation "after" => afterOrdinary hp one pin ticket arch sh unit
local notation "base₀" => physicalShape v.world arch.bit G (rr).pick units₀ (fun _=>le_refl (T).z) cProf
    hp sh.sites sh.edges pin (fun _=>unit)
local notation:max "atNode" x:arg => (NodeOrder.physicalNames arch.bit G (rr).pick units₀ (fun _=>le_refl (T).z) cProf).symm
    (roots ticket arch x)
local notation "net" => rawGraph v.nonnegative T selected
local notation:max "actualArg" x:arg a:arg => ((base₀ (atNode x).1).recipe hp).operand (atNode x).2 (sourceIndex ticket arch hp one pin sh unit x a)
local notation:max "block₁" x:arg => (target).placement.block x
local notation:max "home₁" x:arg => hostIndex ticket ((target).vertex ((target).placement.pos x).2)
local notation:max "group₁" x:arg => ((target).placement.pos x).1
local notation:max "flat₁" x:arg => ((home₁ x).cast (congrArg (OH*·) lo.symm))
local notation:max "rh" x:arg => ((widen hostFit (flat₁ x)).cast shape.hosts.symm)
local notation:max "rg" x:arg => (((group₁ x).cast gs.symm).cast shape.groups.symm)
local notation:max "physJob" x:arg fit:arg a:arg => (ℒ).index (((block₁ (x).1).cast rad.symm).cast shape.blocks.symm,
    ⟨(advance ticket arch prior (x).1 (x).2).val,fit⟩,a)
local notation:max "rec" x:arg => host (currentLabel ticket arch (x).1 (x).2).val.1.2
local notation:max "oldGrp" x:arg => (currentLabel ticket arch (x).1 (x).2).val.1.1
local notation "fits₀" => maxNodes_le arch.bit room.capacity
local notation "N₀" => DescentPackedActorMask.nodes ((D+1)^4*bk) ports.nodes (A).cap
local notation "rank₀" => groupRank Fin.valEmbedding ((cap).vertex.trans Fin.valEmbedding)
local notation:max "firstSite" pair:arg => v.world.graph.src ((rr).pick (pair,0))
local notation:max "seat₀" pair:arg => outgoingSlot A native S (cap).valid (rr).pick used pair
local notation:max "localBorn" pair:arg party:arg f:arg => birth f ((A).block (firstSite pair)) (seat₀ pair) party
    ((cap).vertex ((A).pos (firstSite pair)).2) ((A).pos (firstSite pair)).1
local notation "chart₀" => originStampChart («cap»:=cap) (K₀:=ports.nodes) (ℒ).nodes (phys).originBits
local notation:max "store₀" x:arg => DescentScalarBookReshape.book
    (fun l h g=>selection N₀ (ℒ).nodes (phys).originBits (marked (smallW l) h g)) (block₁ x) (home₁ x) (group₁ x)
local notation:max "code₀" pair:arg => (DescentPacking.PackedMatch.LayoutSum.profileCode (G).C (cProf pair)).val
local notation:max "originalMouth" occ:arg => occurrenceMouth v.world G (rr).pick units₀ cProf occ


local notation:max "seedBlock" b:arg => (b).cast (congrArg (2^·) refK.symm)
local notation:max "seedSeat" s:arg => (s).cast (mat.newCap.trans refC).symm
local notation:max "seedHosts" h:arg => ((h).castLE hostFit).cast homes.symm
local notation:max "seedGroups" g:arg => (finProdFinEquiv (((S).groupDigits age radix) g)).cast
    (groups.trans (congrArg₂ Nat.mul gs rad)).symm
local notation:max "birthSource" pair:arg => chipDonor (phys).bornBook.format (chip
    (seedHosts ((cap).vertex ((A).pos (firstSite pair)).2)) (seedGroups ((A).pos (firstSite pair)).1))
    (finProdFinEquiv ((seedBlock ((A).block (firstSite pair))).cast mat.newBlocks.symm,seedSeat (seat₀ pair)))
local notation:max "mouthW" n:arg => Values.originTransport refD refK refN refC lo gs rad field (rows₁ n 0)
local notation "donorFit" => walks*bk≤2^((ℒ).size+2)
local notation "codeFit" => 11*(A).cap≤2^((ℒ).size+2)

variable (x:NodeOrder.All next) (arg:Fin ((((after).sites x.1).recipe hp).arity x.2))
    (fits:(advance ticket arch prior x.1 x.2).val<(ℒ).nodes) (written:arg.val<(ℒ).operands)
    (wire:Incident net (atNode x).1) (piece:ℕ) (length:(piece+1)*p≤(net).width wire.val)
local notation "job" => physJob x fits (⟨arg.val,written⟩:Fin (ℒ).operands)
local notation:max "pageAt" f:arg => (DescentOperandStateBanks.page ((f).castLE (by decide : 4≤7))
    (⟨arg.val,written⟩:Fin (ℒ).operands)).cast (congrArg (7*·) shape.operands)
local notation "res₀" => (phys).receiverBlock bl job

local notation "pos₀" => DescentPrivateRawLabels.parent_positive A S (cap).valid (rr).pick units₀
    (fun _=>(T).unitPos) (rr).fit cProf hp
    (⟨wire.val,piece,(Nat.le_div_iff_mul_le hp).mpr length⟩:WireWord net p)
local notation "raw₀" => (⟨wire.val,pos₀⟩:DescentRawCablePanel.Live A (rr).pick)
local notation "jobRoute" => PhysicalOrdinary.CableRoute (v:=v) (oldFit:=oldFit) (R:=R₀) (selected:=selected)
    (m:=m) (parts:=parts) (B:=B) (bl:=bl) (hb:=hb) (gs:=mg) (bands:=bands)
    («serial»:=serial) («peer»:=peer) («orig»:=orig) (old:=oldBook) (born:=ports₃)
    (j:=job) (h:=rh x.1) (y:=rg x.1) (recv:=rec x) raw₀ piece

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 16000 in
private theorem registered_cable_jobs_proof
    {F P:Type}
    [Field F]
    (v:PhysicalOrdinary F P)
    (oldFit:OH≤H)
    (selected:((T).result v.nonnegative).Choice)
    (choiceEq:HEq selected v.choice)
    (arch:Archive v.world)
    {w mb p stretch s Z:ℕ}
    (m:Memory w)
    (parts:Bank)
    (B:v.SelectedBoard oldFit R₀ selected m parts)
    (tokens:DescentColonies.Block v.k→Fin count₀→Fin OH→Fin og→DescentScalarVenueMask.Ticket walks lowNames)
    (age:v.age<(S).length)
    (radix:(S).radix=2^v.k)
    (hp:0<p)
    (one:1≤ stretch)
    (pin:∀x,p∣v.bits x)
    (sh:WorldShape p stretch arch.bit)
    (unit:p∣(T).z)
    (ports:DatePorts)
    (mem:Memory w)
    (room:DatePorts.RangeRoom ports cap arch.bit)
    (population:OH≤ports.operandHosts)
    (prior:Local arch.bit)
    (counts:DescentColonies.Block v.k→Fin OH→Fin og→Cell mb)
    (live:∀u,(counts ((A).block u) ((cap).vertex ((A).pos u).2) ((A).pos u).1).val=Fintype.card (arch.bit.recipe u).Node)
    (empty:∀b h g,(¬∃u,(A).block u=b ∧ (cap).vertex ((A).pos u).2=h ∧ ((A).pos u).1=g)→counts b h g=0)
    (pinCode:P→ℕ)
    (arity:ℕ)
    (op:RotorSpec)
    (labels:NodeOrder.All arch.bit→DescentPrimitivePalette.Label G s Z op)
    (flags:Fin (2^ports.venue.k)→Fin ports.nodes→Fin ports.operandHosts→Fin ports.venue.groups→ℕ)
    (stored:DatePorts.ArchiveRead ports cap arch.bit prior room sh op labels ptr₀ flags mem)
    (paid:∀v u,((sh.sites v).recipe hp).arity u≤ports.argumentsPerNode)
    (bitsFit:ports.operandBits*ports.nodes*ports.operandLanes≤w)
    (birth:Fin 4→DescentColonies.Block v.k→Fin (A).cap→Fin 6→Fin OH→Fin og→Cell ports.operandBits)
    (shape:(phys).VectorShape)
    (lo:(phys).vector.lows=pitch₁)
    (gs:(phys).vector.groups=ng)
    (rad:(phys).vector.radix=bk)
    (field:(ℒ).size+2=ports.operandBits)
    (hostFit:OH≤(phys).vector.hosts)
    (V:References.Rows (phys).vector D v.k ports.nodes (A).cap ((ℒ).size+2) (DescentSharedCableNames.Packed.bits pitch₁) mb)
    (refD:(phys).reference.degree=D)
    (refK:(phys).reference.k=v.k)
    (refN:(phys).reference.oldNodes=ports.nodes)
    (refC:(phys).reference.capacity=(A).cap)
    (bl:(ℒ).blocks=(E).blocks)
    (hb:(ℒ).hosts≤(E).hosts)
    (mg:(ℒ).groups=(E).groups)
    (bands:og=(E).groups*(E).blocks)
    (stepFit:(phys).materialPitch=pitch₁)
    (blockFit:(E).blocks=bk)
    {stampField:ℕ}
    (origPrevious:DescentColonies.Block v.k→Fin OH→Fin og→Cell (stampField*ports.nodes))
    (origBorn:DescentColonies.Block v.k→Fin (A).cap→Fin 6→Fin OH→Fin og→Cell stampField)
    (large:(phys).OriginalDonors stampField (DescentSharedCableNames.Packed.bits pitch₁) mb)
    («prefix»:∀l,Values.Prefix hostFit
      (Values.originTransport refD refK refN refC lo gs rad (rfl:stampField=stampField) smallW l) (large l))
    (wide:Fintype.card v.target.V≤(phys).signed.hosts)
    (floor:ℕ)
    (entry:(phys).ArgumentEntry)
    (mat:entry.Match phys floor)
    (homes:(phys).bornBook.hosts=(phys).vector.hosts)
    (groups:(phys).bornBook.groups=(phys).vector.groups*(phys).vector.radix)
    (bits_:(phys).bornBook.bits=(ℒ).size+2)
    (U:References.Rows (phys).vector (phys).reference.degree (phys).reference.k (phys).reference.oldNodes (phys).reference.capacity
      ((ℒ).size+2) (DescentSharedCableNames.Packed.bits pitch₁) mb)
    (chip:Fin (phys).bornBook.hosts→Fin (phys).bornBook.groups→Cell (phys).bornBook.chipBits)
    (nameRoom:∀j h y,11*(role₀ j 1 h y).val+(role₀ j 2 h y).val<2^((ℒ).size+2))
    (x:NodeOrder.All next)
    (arg:Fin ((((after).sites x.1).recipe hp).arity x.2))
    (fits:(advance ticket arch prior x.1 x.2).val<(ℒ).nodes)
    (written:arg.val<(ℒ).operands)
    (wire:Incident net (atNode x).1)
    (piece:ℕ)
    (length:(piece+1)*p≤(net).width wire.val)
    (auth:stock)
    (rankRoom:donorFit) (nameFit:codeFit) (argumentsFit:(ℒ).operands≤2^((ℒ).size+2))
    (resident:∀f l,Values.Prefix hostFit (small arg.val f l) (V (pageAt f) l))
    (mouthResident:∀l,Values.Prefix hostFit (mouthW arg.val l) (U (mouthPage (⟨arg.val,written⟩:Fin (ℒ).operands)) l))
    (demand:(phys).bornBook.demand=(G).b) (grain:(phys).bornBook.grain=p) (scale:(phys).bornBook.scale=(T).z)
    (mouthSize:11≤2^(phys).bornBook.bits)
    (first:∀i,(birthSource i).first=true)
    (supply:∀i s,((birthSource i).supplyUnits s).val=((cProf i).val s).val+(G).k)
    (birthBytes:∀pair party f,(localBorn pair party f).val=
      (component ((ℒ).size+2) (pointerAt (G).b p (T).z (birthSource pair) party arg.val)
        (f.castLE (by decide : 4≤7))).val)
    (read:actualArg x arg=.inl ⟨.inl wire,piece,length⟩) :
    CableOutcome ticket arch hp one pin sh unit host R₀ listed₀ x arg wire piece length
      (resolve (((jobs) job).compiled (rh x.1) (rg x.1))) ∧ jobRoute :=by
  have limit:N₀<2^(phys).originBits:=by
    simpa only [PhysicalOrdinary.originCandidates,refD,refK,refN,refC,DescentHaloWalkRAM.breadth] using (phys).originBits_fit
  have atHost:DepotRAM.Material.Route.receiver H (phys).materialPitch ((rh x.1).castLE hb)=some (rec x):=by
    rw [stepFit]
    exact registered_receiver_at ticket arch age radix x ((rh x.1).castLE hb) oldFit rfl
  have localGroup:(finProdFinEquiv ((rg x.1).cast mg,res₀)).val=(oldGrp x).val:=by
    apply registered_cohort_at ticket arch age radix x ((rg x.1).cast mg) res₀ blockFit rfl
    simp only [PhysicalOrdinary.receiverBlock,Equiv.symm_apply_apply,Fin.val_cast]
  have largeDigits:2^((ℒ).size+2)≤2^(phys).operandShortBits:=
    Nat.pow_le_pow_right (by decide) ((Nat.le_max_right ..).trans (Nat.le_max_left ..))
  have twoFits:2<2^(phys).operandShortBits:=by
    have : 2^((ℒ).size+2)=2^(ℒ).size*4:=by rw [pow_add,show (2:ℕ)^2=4 from rfl]
    have positive:0<2^(ℒ).size:=by positivity
    omega
  have walksFit:walks≤2^(phys).operandShortBits:=
    (Nat.le_mul_of_pos_right _ (by positivity : 0<bk)).trans (rankRoom.trans largeDigits)
  have blocksFit:bk≤2^(phys).operandShortBits:=
    (Nat.le_mul_of_pos_left _ (by unfold DescentHaloWalkRAM.breadth;positivity : 0<walks)).trans
      (rankRoom.trans largeDigits)
  have slotsFit:(A).cap≤2^(phys).operandShortBits:=(by omega : (A).cap≤11*(A).cap).trans (nameFit.trans largeDigits)
  apply PhysicalOrdinary.registered_cable_route (v:=v) (oldFit:=oldFit) (R:=R₀) (selected:=selected)
    (m:=m) (parts:=parts) (B:=B) (bl:=bl) (hb:=hb) (gs:=mg) (bands:=bands)
    («serial»:=serial) («peer»:=peer) (old:=oldBook) (grain:=(phys).chosenGrain) («orig»:=orig) (born:=ports₃)
    (j:=job) (h:=rh x.1) (y:=rg x.1) (recv:=rec x) (atHost:=atHost) (choiceEq:=choiceEq)
    (nameRoom:=nameRoom) (archive:=arch) (hp:=hp) (one:=one) (pin:=pin) (sh:=sh) (unit:=unit)
    (x:=x) (arg:=arg) (wire:=wire) (piece:=piece) (length:=length) (listed:=listed₀)
    (agrees:=fun _ _=>rfl) (symmetric:=registered_symmetric v oldFit) («donorFit»:=rankRoom) («codeFit»:=nameFit)
    read mouthSize rfl
  · intro saved carried slot edge valid positive num earlier
    constructor
    · intro f
      have digits := registered_old_cable_digits («ticket»:=ticket) (arch:=arch) (tokens:=tokens) (age:=age) (radix:=radix)
          (ports:=ports) (mem:=mem) (room:=room) (population:=population) (prior:=prior) (priorCount:=counts)
          (old_live:=live) (old_empty:=empty) (hp:=hp) (one:=one) (pin:=pin) (sh:=sh) (unit:=unit)
          (pinCode:=pinCode) (arity:=arity) (op:=op) (labels:=labels) (flags:=flags) (stored:=stored)
          (paid:=paid) (bitsFit:=bitsFit) (birth:=birth) (v:=phys) (shape:=shape) (lo:=lo) (gs:=gs)
          (rad:=rad) (field:=field) (hostFit:=hostFit) (V:=V)
          auth limit x arg fits written resident saved carried slot num edge piece valid earlier f
      exact digits.trans (show (Reached.firstCable (cap) hp saved.1 edge piece valid).header f = _ from rfl)
    · let stockAt := registered_old_W (ports:=ports) («ticket»:=ticket) (arch:=arch) (tokens:=tokens)
          (age:=age) (radix:=radix) (room:=room) (prior:=prior) (priorCount:=counts)
          (old_live:=live) (old_empty:=empty) (hp:=hp) (one:=one) (pin:=pin) (sh:=sh) (unit:=unit)
          (v:=phys) (shape:=shape) (lo:=lo) (gs:=gs) (rad:=rad) (hostFit:=hostFit)
          (refD:=refD) (refK:=refK) (refN:=refN) (refC:=refC) (receiverH:=oldFit)
          (origPrevious:=origPrevious) (origBorn:=origBorn) (large:=large) («prefix»:=«prefix»)
          auth x arg fits written saved carried
      let walk := stockAt.choose
      have sorted := stockAt.choose_spec.1
      have cluster := stockAt.choose_spec.2.1
      have origin := stockAt.choose_spec.2.2
      have labelsEq : (host).trans Fin.valEmbedding = (cap).vertex.trans Fin.valEmbedding := by
        ext a
        rfl
      have sorted₁ : DescentSortedRoster.indexed
          (Gather.reaching (hostRotor host (hostRoster A ((cap).vertex.trans Fin.valEmbedding))))
          (rec x) walk=some (host ((A).pos saved.1).2) := by exact sorted
      refine ⟨⟨inputTarget ticket arch x wire,walk,?_,?_,
        origin 0 (show 1 < _ from (by decide : 1 ≤ 2).trans_lt twoFits),origin 1 (walk.isLt.trans_le walksFit),?_,
        origin 2 (((A).block saved.1).isLt.trans_le blocksFit)⟩⟩
      · exact congrArg (fun z=>host z.2) (original_receiver ticket arch (ticket).donorChart.same x wire)
      · apply Fin.ext
        simpa only [Fin.val_cast] using localGroup.trans (congrArg Fin.val cluster.symm)
      · simpa only [labelsEq] using sorted₁
  · intro pair party fresh occ occurs
    dsimp only
    intro mouthHit pieceEq
    have getPorts (f:Fin 3) : (ports₃ job f (rh x.1) (rg x.1)).val=
        (RolePorts.value (phys).bornBook.bits (some (originalMouth occ)) f).val:=
      congrArg Fin.val (registered_born_ports («ticket»:=ticket) (arch:=arch) (tokens:=tokens) (age:=age)
        (radix:=radix) (ports:=ports) (mem:=mem) (room:=room) (population:=population) (prior:=prior)
        (priorCount:=counts) (old_live:=live) (old_empty:=empty) (p:=p) (v:=phys) (floor:=floor)
        (entry:=entry) (mat:=mat) (shape:=shape) (degree:=refD) (depth:=refK) (oldNodes:=refN)
        (capacity:=refC) (lo:=lo) (gs:=gs) (rad:=rad) (field:=field) (hostFit:=hostFit) (homes:=homes)
        (groups:=groups) (bits_:=bits_) (V:=U) (chip:=chip) (born₀:=birth 0) auth limit x arg.val
        pair party fresh fits written mouthResident (originalMouth occ) mouthHit demand grain scale
        (first pair) (supply pair) f)
    have lowFit:(originalMouth occ).chunk<2^((ℒ).size+2):=
      (mouth_chunk_le (actual G p) (T).z (code₀ pair) party mouthHit).trans_lt (written.trans_le argumentsFit)
    have digits:=registered_born_headers («ticket»:=ticket) (arch:=arch) (tokens:=tokens) (age:=age) (radix:=radix)
      (ports:=ports) (mem:=mem) (room:=room) (population:=population) (prior:=prior) (priorCount:=counts)
      (old_live:=live) (old_empty:=empty) (hp:=hp) (one:=one) (pin:=pin) (sh:=sh) (unit:=unit)
      (birth:=birth) (v:=phys) (shape:=shape) (lo:=lo) (gs:=gs) (rad:=rad) (field:=field)
      (hostFit:=hostFit) (V:=V) auth limit x arg pair party fresh fits written resident (originalMouth occ)
      mouthHit lowFit (birthSource pair) (first pair) (supply pair) (birthBytes pair party)
    refine ⟨by simpa only [pieceEq] using digits.1,?_⟩
    let bornStock := registered_born_W («ticket»:=ticket) (arch:=arch) (ports:=ports)
      (tokens:=tokens) (age:=age) (radix:=radix) (room:=room) (prior:=prior) (priorCount:=counts)
      (old_live:=live) (old_empty:=empty) (hp:=hp) (one:=one) (pin:=pin) (sh:=sh) (unit:=unit)
      (v:=phys) (shape:=shape) (lo:=lo) (gs:=gs) (rad:=rad) (hostFit:=hostFit)
      (refD:=refD) (refK:=refK) (refN:=refN) (refC:=refC) (receiverH:=oldFit)
      (origPrevious:=origPrevious) (origBorn:=origBorn) (large:=large) («prefix»:=«prefix»)
      auth x arg fits written pair party fresh
    let walk := bornStock.choose
    have sorted := bornStock.choose_spec.1
    have cluster := bornStock.choose_spec.2.1
    have stamp := bornStock.choose_spec.2.2.1
    have origin := bornStock.choose_spec.2.2.2
    have chosen:(Stage.picked A v.nonnegative pair.1 pair.2 true).val=(rr).pick (pair,0):=
      Stage.picked_old A v.nonnegative pair.1 pair.2 true
    have bound:max 2 (max walk.val (max ((A).block (firstSite pair)).val (seat₀ pair).val))<2^(phys).operandShortBits:=
      max_lt twoFits (max_lt (walk.isLt.trans_le walksFit)
        (max_lt (((A).block (firstSite pair)).isLt.trans_le blocksFit) ((seat₀ pair).isLt.trans_le slotsFit)))
    refine ⟨⟨chart₀,walk,(A).block (firstSite pair),seat₀ pair,⟨_,fits⟩,store₀ x.1,walk,
      stamp,origin,rfl,?_,?_,bound,?_,?_,getPorts⟩⟩
    · simp only [chosen]
    · apply congrArg Fin.val
      unfold outgoingSlot
      congr 1
    · have labelsEq : (host).trans Fin.valEmbedding = (cap).vertex.trans Fin.valEmbedding := by
        ext a
        rfl
      have sorted₁ : DescentSortedRoster.indexed
          (Gather.reaching (hostRotor host (hostRoster A ((cap).vertex.trans Fin.valEmbedding)))) (rec x) walk =
          some (host ((A).pos (firstSite pair)).2) := by
        exact sorted
      simpa only [chosen,labelsEq] using sorted₁
    · apply Fin.ext
      simpa only [chosen,Fin.val_cast] using localGroup.trans (congrArg Fin.val cluster.symm)

private abbrev RegisteredArchiveCableJobsStatement : Prop := type_of% @registered_cable_jobs_proof

/-- The scheduled job of a real cable exposes a matching cable ticket at the same epoch,
using the retained predecessor archive, the six recorded origin fields and the physical newborn
chip when the scalar has just been created. -/
theorem registered_cable_jobs : RegisteredArchiveCableJobsStatement := @registered_cable_jobs_proof

private theorem registered_cable_pointer_proof
    {F P:Type}
    [Field F]
    (v:PhysicalOrdinary F P)
    (oldFit:OH≤H)
    (selected:((T).result v.nonnegative).Choice)
    (choiceEq:HEq selected v.choice)
    (arch:Archive v.world)
    {w mb p stretch:ℕ}
    (m:Memory w)
    (parts:Bank)
    (B:v.SelectedBoard oldFit R₀ selected m parts)
    (age:v.age<(S).length)
    (radix:(S).radix=2^v.k)
    (hp:0<p)
    (one:1≤ stretch)
    (pin:∀x,p∣v.bits x)
    (sh:WorldShape p stretch arch.bit)
    (unit:p∣(T).z)
    (ports:DatePorts)
    (prior:Local arch.bit)
    (shape:(phys).VectorShape)
    (lo:(phys).vector.lows=pitch₁)
    (gs:(phys).vector.groups=ng)
    (rad:(phys).vector.radix=bk)
    (hostFit:OH≤(phys).vector.hosts)
    (V:References.Rows (phys).vector D v.k ports.nodes (A).cap ((ℒ).size+2) (DescentSharedCableNames.Packed.bits pitch₁) mb)
    (bl:(ℒ).blocks=(E).blocks)
    (hb:(ℒ).hosts≤(E).hosts)
    (mg:(ℒ).groups=(E).groups)
    (bands:og=(E).groups*(E).blocks)
    {stampField:ℕ}
    (large:(phys).OriginalDonors stampField (DescentSharedCableNames.Packed.bits pitch₁) mb)
    (wide:Fintype.card v.target.V≤(phys).signed.hosts)
    (floor:ℕ)
    (entry:(phys).ArgumentEntry)
    (mat:entry.Match phys floor)
    (homes:(phys).bornBook.hosts=(phys).vector.hosts)
    (groups:(phys).bornBook.groups=(phys).vector.groups*(phys).vector.radix)
    (bits_:(phys).bornBook.bits=(ℒ).size+2)
    (U:References.Rows (phys).vector (phys).reference.degree (phys).reference.k (phys).reference.oldNodes (phys).reference.capacity
      ((ℒ).size+2) (DescentSharedCableNames.Packed.bits pitch₁) mb)
    (chip:Fin (phys).bornBook.hosts→Fin (phys).bornBook.groups→Cell (phys).bornBook.chipBits)
    (nameRoom:∀j h y,11*(role₀ j 1 h y).val+(role₀ j 2 h y).val<2^((ℒ).size+2))
    (x:NodeOrder.All next)
    (arg:Fin ((((after).sites x.1).recipe hp).arity x.2))
    (fits:(advance ticket arch prior x.1 x.2).val<(ℒ).nodes)
    (written:arg.val<(ℒ).operands)
    (wire:Incident net (atNode x).1)
    (piece:ℕ)
    (length:(piece+1)*p≤(net).width wire.val)
    (edge:Incident (ac).norm.result.graph x.1) (digit:ℕ) (full:(digit+1)*p≤(ac).norm.result.graph.width edge.val)
    (hit:(((after).sites x.1).recipe hp).operand x.2 arg=.inl ⟨.inl edge,digit,full⟩)
    (read:actualArg x arg=.inl ⟨.inl wire,piece,length⟩) (route:jobRoute)
    (rankRoom:donorFit) (nameFit:codeFit)
    (wireFit:v.target.placement.cap≤2^(phys).signed.fieldBits) (peerFit:v.target.placement.degree≤2^(phys).signed.fieldBits)
    (wireWide:v.target.placement.cap≤2^((ℒ).size+2)) (peerWide:v.target.placement.degree≤2^((ℒ).size+2))
    (cutRead:(phys).chosenGrain.val=(T).z/p) (step:(phys).materialPitch=pitch₁) :
    Pointer.ofKey 0 (resolve (((jobs) job).compiled (rh x.1) (rg x.1)))=
      (ac).next.firstCable hp x.1 edge digit full :=by
  have different:=uncaptured_source ticket arch hp one pin sh unit x arg hit wire piece length read
  have yielded := PhysicalOrdinary.CableRoute.surviving
    (v:=v) (oldFit:=oldFit) (R:=R₀) (selected:=selected) (m:=m) (parts:=parts) (B:=B)
    (bl:=bl) (hb:=hb) (gs:=mg) (bands:=bands) («serial»:=serial) («peer»:=peer) («orig»:=orig)
    (old:=oldBook) (grain:=(phys).chosenGrain) (born:=ports₃) (j:=job) (h:=rh x.1) (y:=rg x.1)
    (recv:=rec x) (choiceEq:=choiceEq) (nameRoom:=nameRoom) (archive:=arch)
    (hp:=hp) (one:=one) (pin:=pin) (sh:=sh) (unit:=unit) (x:=x) (wire:=wire) (piece:=piece)
    (length:=length) (listed:=listed₀) (agrees:=fun _ _=>rfl) (symmetric:=registered_symmetric v oldFit)
    («donorFit»:=rankRoom) («codeFit»:=nameFit) route different
  rcases yielded with ⟨path, representable, visited, printed⟩
  have atHost:DepotRAM.Material.Route.receiver H (phys).materialPitch ((rh x.1).castLE hb)=some (rec x):=
    (congrArg (fun stride => DepotRAM.Material.Route.receiver H stride ((rh x.1).castLE hb)) step).trans
      (registered_receiver_at ticket arch age radix x ((rh x.1).castLE hb) oldFit rfl)
  have block:(block₁ x.1).val=(res₀).val:=by simp only [PhysicalOrdinary.receiverBlock,Equiv.symm_apply_apply,Fin.val_cast]
  have donated := v.dated_source_pointer oldFit R₀ selected m parts B choiceEq wide age radix bands
    (registered_symmetric v oldFit) arch hp one pin sh unit bl hb mg orig oldWords ports₃ job (rh x.1) (rg x.1)
    x arg edge digit full hit raw₀ wire piece length read rfl wireFit peerFit wireWide peerWide
    (rec x) atHost rfl rfl block path visited ⟨piece,representable⟩ (phys).chosenGrain rfl cutRead
  exact (congrArg (Pointer.ofKey 0) printed).trans donated

private abbrev RegisteredArchiveCablePointerStatement : Prop := type_of% @registered_cable_pointer_proof

/-- The donated row physically read by the job is the original public operand,
at the registered successor node and in the signed roster's actual serial order. -/
theorem registered_cable_pointer : RegisteredArchiveCablePointerStatement := @registered_cable_pointer_proof

set_option maxHeartbeats 4500000 in
set_option maxRecDepth 24000 in
private theorem registered_public_cable_proof
    {F P:Type}
    [Field F]
    (v:PhysicalOrdinary F P)
    (oldFit:OH≤H)
    (selected:((T).result v.nonnegative).Choice)
    (choiceEq:HEq selected v.choice)
    (arch:Archive v.world)
    {w mb p stretch s Z:ℕ}
    (m:Memory w)
    (parts:Bank)
    (B:v.SelectedBoard oldFit R₀ selected m parts)
    (tokens:DescentColonies.Block v.k→Fin count₀→Fin OH→Fin og→DescentScalarVenueMask.Ticket walks lowNames)
    (age:v.age<(S).length)
    (radix:(S).radix=2^v.k)
    (hp:0<p)
    (one:1≤ stretch)
    (pin:∀x,p∣v.bits x)
    (sh:WorldShape p stretch arch.bit)
    (unit:p∣(T).z)
    (ports:DatePorts)
    (mem:Memory w)
    (room:DatePorts.RangeRoom ports cap arch.bit)
    (population:OH≤ports.operandHosts)
    (prior:Local arch.bit)
    (counts:DescentColonies.Block v.k→Fin OH→Fin og→Cell mb)
    (live:∀u,(counts ((A).block u) ((cap).vertex ((A).pos u).2) ((A).pos u).1).val=Fintype.card (arch.bit.recipe u).Node)
    (empty:∀b h g,(¬∃u,(A).block u=b ∧ (cap).vertex ((A).pos u).2=h ∧ ((A).pos u).1=g)→counts b h g=0)
    (pinCode:P→ℕ)
    (arity:ℕ)
    (op:RotorSpec)
    (labels:NodeOrder.All arch.bit→DescentPrimitivePalette.Label G s Z op)
    (flags:Fin (2^ports.venue.k)→Fin ports.nodes→Fin ports.operandHosts→Fin ports.venue.groups→ℕ)
    (stored:DatePorts.ArchiveRead ports cap arch.bit prior room sh op labels ptr₀ flags mem)
    (paid:∀v u,((sh.sites v).recipe hp).arity u≤ports.argumentsPerNode)
    (bitsFit:ports.operandBits*ports.nodes*ports.operandLanes≤w)
    (birth:Fin 4→DescentColonies.Block v.k→Fin (A).cap→Fin 6→Fin OH→Fin og→Cell ports.operandBits)
    (shape:(phys).VectorShape)
    (lo:(phys).vector.lows=pitch₁)
    (gs:(phys).vector.groups=ng)
    (rad:(phys).vector.radix=bk)
    (field:(ℒ).size+2=ports.operandBits)
    (hostFit:OH≤(phys).vector.hosts)
    (V:References.Rows (phys).vector D v.k ports.nodes (A).cap ((ℒ).size+2) (DescentSharedCableNames.Packed.bits pitch₁) mb)
    (refD:(phys).reference.degree=D)
    (refK:(phys).reference.k=v.k)
    (refN:(phys).reference.oldNodes=ports.nodes)
    (refC:(phys).reference.capacity=(A).cap)
    (bl:(ℒ).blocks=(E).blocks)
    (hb:(ℒ).hosts≤(E).hosts)
    (mg:(ℒ).groups=(E).groups)
    (bands:og=(E).groups*(E).blocks)
    (stepFit:(phys).materialPitch=pitch₁)
    (blockFit:(E).blocks=bk)
    {stampField:ℕ}
    (origPrevious:DescentColonies.Block v.k→Fin OH→Fin og→Cell (stampField*ports.nodes))
    (origBorn:DescentColonies.Block v.k→Fin (A).cap→Fin 6→Fin OH→Fin og→Cell stampField)
    (large:(phys).OriginalDonors stampField (DescentSharedCableNames.Packed.bits pitch₁) mb)
    («prefix»:∀l,Values.Prefix hostFit
      (Values.originTransport refD refK refN refC lo gs rad (rfl:stampField=stampField) smallW l) (large l))
    (wide:Fintype.card v.target.V≤(phys).signed.hosts)
    (floor:ℕ)
    (entry:(phys).ArgumentEntry)
    (mat:entry.Match phys floor)
    (homes:(phys).bornBook.hosts=(phys).vector.hosts)
    (groups:(phys).bornBook.groups=(phys).vector.groups*(phys).vector.radix)
    (bits_:(phys).bornBook.bits=(ℒ).size+2)
    (U:References.Rows (phys).vector (phys).reference.degree (phys).reference.k (phys).reference.oldNodes (phys).reference.capacity
      ((ℒ).size+2) (DescentSharedCableNames.Packed.bits pitch₁) mb)
    (chip:Fin (phys).bornBook.hosts→Fin (phys).bornBook.groups→Cell (phys).bornBook.chipBits)
    (nameRoom:∀j h y,11*(role₀ j 1 h y).val+(role₀ j 2 h y).val<2^((ℒ).size+2))
    (x:NodeOrder.All next)
    (arg:Fin ((((after).sites x.1).recipe hp).arity x.2))
    (fits:(advance ticket arch prior x.1 x.2).val<(ℒ).nodes)
    (written:arg.val<(ℒ).operands)
    (auth:stock)
    (rankRoom:donorFit) (nameFit:codeFit) (argumentsFit:(ℒ).operands≤2^((ℒ).size+2))
    (resident:∀f l,Values.Prefix hostFit (small arg.val f l) (V (pageAt f) l))
    (mouthResident:∀l,Values.Prefix hostFit (mouthW arg.val l) (U (mouthPage (⟨arg.val,written⟩:Fin (ℒ).operands)) l))
    (demand:(phys).bornBook.demand=(G).b) (grain:(phys).bornBook.grain=p) (scale:(phys).bornBook.scale=(T).z)
    (mouthSize:11≤2^(phys).bornBook.bits)
    (first:∀i,(birthSource i).first=true)
    (supply:∀i s,((birthSource i).supplyUnits s).val=((cProf i).val s).val+(G).k)
    (birthBytes:∀pair party f,(localBorn pair party f).val=
      (component ((ℒ).size+2) (pointerAt (G).b p (T).z (birthSource pair) party arg.val)
        (f.castLE (by decide : 4≤7))).val)
    (edge:Incident (ac).norm.result.graph x.1) (digit:ℕ) (full:(digit+1)*p≤(ac).norm.result.graph.width edge.val)
    (hit:(((after).sites x.1).recipe hp).operand x.2 arg=.inl ⟨.inl edge,digit,full⟩)
    (wireFit:v.target.placement.cap≤2^(phys).signed.fieldBits) (peerFit:v.target.placement.degree≤2^(phys).signed.fieldBits)
    (wireWide:v.target.placement.cap≤2^((ℒ).size+2)) (peerWide:v.target.placement.degree≤2^((ℒ).size+2))
    (cutRead:(phys).chosenGrain.val=(T).z/p) :
    Pointer.ofKey 0 (resolve (((jobs) job).compiled (rh x.1) (rg x.1)))=
      (ac).next.firstCable hp x.1 edge digit full :=by
  obtain ⟨rawEdge,rawChunk,rawRoom,rawRead⟩:=v.dated_source_exists (oldFit:=oldFit) (R:=R₀)
    (selected:=selected) (m:=m) (parts:=parts) (B:=B) (choiceEq:=choiceEq) (wide:=wide)
    (age:=age) (radix:=radix) (reciprocal:=registered_symmetric v oldFit) (arch:=arch) (hp:=hp)
    (one:=one) (pin:=pin) (sh:=sh) (unit:=unit) x arg edge digit full hit
  have observed:=registered_cable_jobs (v:=v) (oldFit:=oldFit) (selected:=selected) (choiceEq:=choiceEq)
    (arch:=arch) (m:=m) (parts:=parts) (B:=B) (tokens:=tokens) (age:=age) (radix:=radix)
    (hp:=hp) (one:=one) (pin:=pin) (sh:=sh) (unit:=unit) (ports:=ports) (mem:=mem) (room:=room)
    (population:=population) (prior:=prior) (counts:=counts) (live:=live) (empty:=empty) (pinCode:=pinCode)
    (arity:=arity) (op:=op) (labels:=labels) (flags:=flags) (stored:=stored) (paid:=paid)
    (bitsFit:=bitsFit) (birth:=birth) (shape:=shape) (lo:=lo) (gs:=gs) (rad:=rad) (field:=field)
    (hostFit:=hostFit) (V:=V) (refD:=refD) (refK:=refK) (refN:=refN) (refC:=refC) (bl:=bl)
    (hb:=hb) (mg:=mg) (bands:=bands) (stepFit:=stepFit) (blockFit:=blockFit)
    (origPrevious:=origPrevious) (origBorn:=origBorn) (large:=large) («prefix»:=«prefix») (wide:=wide)
    (floor:=floor) (entry:=entry) (mat:=mat) (homes:=homes) (groups:=groups) (bits_:=bits_)
    (U:=U) (chip:=chip) (nameRoom:=nameRoom) (x:=x) (arg:=arg) (fits:=fits) (written:=written)
    (wire:=rawEdge) (piece:=rawChunk) (length:=rawRoom) auth rankRoom nameFit argumentsFit resident mouthResident
    demand grain scale mouthSize first supply birthBytes rawRead
  exact registered_cable_pointer (v:=v) (oldFit:=oldFit) (selected:=selected) (choiceEq:=choiceEq)
    (arch:=arch) (m:=m) (parts:=parts) (B:=B) (age:=age) (radix:=radix) (hp:=hp) (one:=one)
    (pin:=pin) (sh:=sh) (unit:=unit) (ports:=ports) (prior:=prior) (shape:=shape) (lo:=lo) (gs:=gs) (rad:=rad)
    (hostFit:=hostFit) (V:=V) (bl:=bl) (hb:=hb) (mg:=mg) (bands:=bands) (large:=large) (wide:=wide)
    (floor:=floor) (entry:=entry) (mat:=mat) (homes:=homes) (groups:=groups) (bits_:=bits_) (U:=U)
    (chip:=chip) (nameRoom:=nameRoom) (x:=x) (arg:=arg) (fits:=fits) (written:=written)
    (wire:=rawEdge) (piece:=rawChunk) (length:=rawRoom) edge digit full hit rawRead observed.2
    rankRoom nameFit wireFit peerFit wireWide peerWide cutRead stepFit

private abbrev RegisteredArchivePublicCableStatement : Prop := type_of% @registered_public_cable_proof

theorem registered_public_cable : RegisteredArchivePublicCableStatement := @registered_public_cable_proof

section Site
variable (t:(ac).norm.result.graph.Site) (capacity:Fintype.card ((next).recipe t).Node≤(ℒ).nodes)
local notation "recipe" => ((after).sites t).recipe hp
variable (writtenAt:∀u,(recipe).arity u≤(ℒ).operands)
    (birthAt:ℕ→Fin 4→DescentColonies.Block v.k→Fin (A).cap→Fin 6→Fin OH→Fin og→Cell ports.operandBits)
local notation:max "smallAt" n:arg f:arg => Values.transport lo gs rad field
    (rangeValues ticket arch tokens age radix counts (priorAt n f) (birthAt n f))
local notation:max "mouthAt" n:arg => Values.originTransport refD refK refN refC lo gs rad field
    (rangeValues ticket arch tokens age radix counts (priorAt n 0) (birthAt n 0))
local notation:max "seat" s:arg => (s).2.castLE (writtenAt (s).1)
local notation:max "page₁" s:arg f:arg => (DescentOperandStateBanks.page ((f).castLE (by decide : 4≤7)) (seat s)).cast
    (congrArg (7*·) shape.operands)
local notation "node" => (advance ticket arch prior t).toEmbedding.trans (Fin.castLEEmb capacity)
local notation "blockAt" => ((block₁ t).cast rad.symm).cast shape.blocks.symm
local notation:max "siteFragment" n:arg j:arg => (phys).issuedFragment jobs blockAt (rh t) (rg t)
    ((phys).finalChart.mouths recipe node writtenAt ⟨n,j⟩)

set_option maxHeartbeats 1600000 in
set_option maxRecDepth 16000 in
private theorem registered_chosen_headers_proof
    {F P:Type}
    [Field F]
    (v:PhysicalOrdinary F P)
    (oldFit:OH≤H)
    (selected:((T).result v.nonnegative).Choice)
    (choiceEq:HEq selected v.choice)
    (arch:Archive v.world)
    {w mb p stretch s Z:ℕ}
    (m:Memory w)
    (parts:Bank)
    (B:v.SelectedBoard oldFit R₀ selected m parts)
    (tokens:DescentColonies.Block v.k→Fin count₀→Fin OH→Fin og→DescentScalarVenueMask.Ticket walks lowNames)
    (age:v.age<(S).length)
    (radix:(S).radix=2^v.k)
    (hp:0<p)
    (one:1≤ stretch)
    (pin:∀x,p∣v.bits x)
    (sh:WorldShape p stretch arch.bit)
    (unit:p∣(T).z)
    (ports:DatePorts)
    (mem:Memory w)
    (room:DatePorts.RangeRoom ports cap arch.bit)
    (population:OH≤ports.operandHosts)
    (prior:Local arch.bit)
    (counts:DescentColonies.Block v.k→Fin OH→Fin og→Cell mb)
    (live:∀u,(counts ((A).block u) ((cap).vertex ((A).pos u).2) ((A).pos u).1).val=Fintype.card (arch.bit.recipe u).Node)
    (empty:∀b h g,(¬∃u,(A).block u=b ∧ (cap).vertex ((A).pos u).2=h ∧ ((A).pos u).1=g)→counts b h g=0)
    (pinCode:P→ℕ)
    (arity:ℕ)
    (op:RotorSpec)
    (labels:NodeOrder.All arch.bit→DescentPrimitivePalette.Label G s Z op)
    (flags:Fin (2^ports.venue.k)→Fin ports.nodes→Fin ports.operandHosts→Fin ports.venue.groups→ℕ)
    (stored:DatePorts.ArchiveRead ports cap arch.bit prior room sh op labels ptr₀ flags mem)
    (paid:∀v u,((sh.sites v).recipe hp).arity u≤ports.argumentsPerNode)
    (bitsFit:ports.operandBits*ports.nodes*ports.operandLanes≤w)
    (shape:(phys).VectorShape)
    (lo:(phys).vector.lows=pitch₁)
    (gs:(phys).vector.groups=ng)
    (rad:(phys).vector.radix=bk)
    (field:(ℒ).size+2=ports.operandBits)
    (hostFit:OH≤(phys).vector.hosts)
    (V:References.Rows (phys).vector D v.k ports.nodes (A).cap ((ℒ).size+2) (DescentSharedCableNames.Packed.bits pitch₁) mb)
    (refD:(phys).reference.degree=D)
    (refK:(phys).reference.k=v.k)
    (refN:(phys).reference.oldNodes=ports.nodes)
    (refC:(phys).reference.capacity=(A).cap)
    (bl:(ℒ).blocks=(E).blocks)
    (hb:(ℒ).hosts≤(E).hosts)
    (mg:(ℒ).groups=(E).groups)
    (bands:og=(E).groups*(E).blocks)
    (stepFit:(phys).materialPitch=pitch₁)
    (blockFit:(E).blocks=bk)
    {stampField:ℕ}
    (origPrevious:DescentColonies.Block v.k→Fin OH→Fin og→Cell (stampField*ports.nodes))
    (origBorn:DescentColonies.Block v.k→Fin (A).cap→Fin 6→Fin OH→Fin og→Cell stampField)
    (large:(phys).OriginalDonors stampField (DescentSharedCableNames.Packed.bits pitch₁) mb)
    («prefix»:∀l,Values.Prefix hostFit
      (Values.originTransport refD refK refN refC lo gs rad (rfl:stampField=stampField) smallW l) (large l))
    (wide:Fintype.card v.target.V≤(phys).signed.hosts)
    (floor:ℕ)
    (entry:(phys).ArgumentEntry)
    (mat:entry.Match phys floor)
    (homes:(phys).bornBook.hosts=(phys).vector.hosts)
    (groups:(phys).bornBook.groups=(phys).vector.groups*(phys).vector.radix)
    (bits_:(phys).bornBook.bits=(ℒ).size+2)
    (U:References.Rows (phys).vector (phys).reference.degree (phys).reference.k (phys).reference.oldNodes (phys).reference.capacity
      ((ℒ).size+2) (DescentSharedCableNames.Packed.bits pitch₁) mb)
    (chip:Fin (phys).bornBook.hosts→Fin (phys).bornBook.groups→Cell (phys).bornBook.chipBits)
    (nameRoom:∀j h y,11*(role₀ j 1 h y).val+(role₀ j 2 h y).val<2^((ℒ).size+2))
    (t:(ac).norm.result.graph.Site)
    (capacity:Fintype.card ((next).recipe t).Node≤(ℒ).nodes)
    (writtenAt:∀u,(recipe).arity u≤(ℒ).operands)
    (birthAt:ℕ→Fin 4→DescentColonies.Block v.k→Fin (A).cap→Fin 6→Fin OH→Fin og→Cell ports.operandBits)
    (auth:stock) (arityFit:∀u n,((sh.sites u).recipe hp).arity n≤arity)
    (rankRoom:donorFit) (nameFit:codeFit) (argumentsFit:(ℒ).operands≤2^((ℒ).size+2))
    (resident:∀(s:DescentLocalPrivateNames.Slot recipe) f l,
      Values.Prefix hostFit (smallAt s.2.val f l) (V (page₁ s f) l))
    (mouthResident:∀(s:DescentLocalPrivateNames.Slot recipe) l,Values.Prefix hostFit
      (mouthAt s.2.val l) (U (mouthPage (seat s)) l))
    (demand:(phys).bornBook.demand=(G).b) (grain:(phys).bornBook.grain=p) (scale:(phys).bornBook.scale=(T).z)
    (mouthSize:11≤2^(phys).bornBook.bits)
    (first:∀i,(birthSource i).first=true)
    (supply:∀i a,((birthSource i).supplyUnits a).val=((cProf i).val a).val+(G).k)
    (birthBytes:∀(s:DescentLocalPrivateNames.Slot recipe) pair party f,
      (birthAt s.2.val f ((A).block (firstSite pair)) (seat₀ pair) party
        ((cap).vertex ((A).pos (firstSite pair)).2) ((A).pos (firstSite pair)).1).val=
      (component ((ℒ).size+2) (pointerAt (G).b p (T).z (birthSource pair) party s.2.val)
        (f.castLE (by decide : 4≤7))).val)
    (wireFit:v.target.placement.cap≤2^(phys).signed.fieldBits) (peerFit:v.target.placement.degree≤2^(phys).signed.fieldBits)
    (wireWide:v.target.placement.cap≤2^((ℒ).size+2)) (peerWide:v.target.placement.degree≤2^((ℒ).size+2))
    (cutRead:(phys).chosenGrain.val=(T).z/p) :
    (∃hidden:(recipe).UsedWord↪Key,(phys).SourceKeys jobs blockAt (rh t) (rg t) recipe node writtenAt hidden) ∧
    (∀n (j:Fin ((recipe).arity n)) (e:Incident (ac).norm.result.graph t) d
      (fit:(d+1)*p≤(ac).norm.result.graph.width e.val),(recipe).operand n j=.inl ⟨.inl e,d,fit⟩→
      Pointer.ofKey 0 (resolve (siteFragment n j))=(ac).next.firstCable hp t e d fit) ∧
    ∀n (j:Fin ((recipe).arity n)) (z:Attached (ac).norm.result.graph t) d
      (fit:(d+1)*p≤v.bits z.val),(recipe).operand n j=.inl ⟨.inr z,d,fit⟩→
      resolve (siteFragment n j)=Key.pin (pinCode z.val) d :=by
  let argFit (s:DescentLocalPrivateNames.Slot recipe):s.2.val<(ℒ).operands:=s.2.isLt.trans_le (writtenAt s.1)
  let nodeFit (n:((next).recipe t).Node):(advance ticket arch prior t n).val<(ℒ).nodes:=
    (advance ticket arch prior t n).isLt.trans_le capacity
  have value (s:DescentLocalPrivateNames.Slot recipe) :
      resolve (siteFragment s.1 s.2)=resolve (((jobs) (physJob (⟨t,s.1⟩:NodeOrder.All next)
        (nodeFit s.1) (seat s))).compiled (rh t) (rg t)):=by
    exact issuedMouthKey (phys) jobs blockAt (rh t) (rg t) recipe node writtenAt s
  have limit:N₀<2^(phys).originBits:=by
    simpa only [PhysicalOrdinary.originCandidates,refD,refK,refN,refC,DescentHaloWalkRAM.breadth] using (phys).originBits_fit
  have padded (h:Fin OH) (j:Fin D) : R₀ (h.castLE oldFit) j=(hostRotor (cap).vertex
      (hostRoster A ((cap).vertex.trans Fin.valEmbedding)) h j).map (Fin.castLEEmb oldFit):=
    physical_rotor oldFit (cap).vertex (hostRoster A ((cap).vertex.trans Fin.valEmbedding)) h j
  constructor
  · refine ⟨_,registered_site_keys_decoded
      («ticket»:=ticket) (arch:=arch) (tokens:=tokens) (age:=age) (radix:=radix)
      (ports:=ports) (mem:=mem) (room:=room) (population:=population) (prior:=prior) (priorCount:=counts)
      (old_live:=live) (old_empty:=empty) (hp:=hp) (one:=one) (pin:=pin) (sh:=sh) (unit:=unit)
      (pinCode:=pinCode) (arity:=arity) (op:=op) (labels:=labels) (flags:=flags) (stored:=stored)
      (paid:=paid) (bitsFit:=bitsFit) (birthAt:=birthAt) (v:=phys) (shape:=shape) (lo:=lo) (gs:=gs)
      (rad:=rad) (field:=field) (hostFit:=hostFit) (V:=V) (refD:=refD) (refK:=refK)
      (refN:=refN) (refC:=refC) (matB:=bl) (matH:=hb) (matG:=mg) (dFit:=rfl)
      (blockFit:=by rfl) (receiverH:=oldFit) (stepFit:=stepFit) (Rbig:=R₀) (nearFit:=padded)
      (origPrevious:=origPrevious) (origBorn:=origBorn) (large:=large) («prefix»:=«prefix»)
      (mouth:=ports₃) (published:=(phys).wideMaterialValues R₀ B.material bands serial peer) (room₁:=nameRoom)
      auth arityFit t capacity writtenAt resident rankRoom ?_⟩
    intro s e d fit fromRaw
    exact Eq.mpr (congrArg (fun (sourceKey : DescentPackedOperand.Key) =>
      CableOutcome ticket arch hp one pin sh unit host R₀ listed₀ (⟨t,s.1⟩:NodeOrder.All next)
        s.2 e d fit sourceKey) (value s)) <|
      (registered_cable_jobs
      (v:=v) (oldFit:=oldFit) (selected:=selected) (choiceEq:=choiceEq)
      (arch:=arch) (m:=m) (parts:=parts) (B:=B) (tokens:=tokens) (age:=age) (radix:=radix)
      (hp:=hp) (one:=one) (pin:=pin) (sh:=sh) (unit:=unit) (ports:=ports) (mem:=mem) (room:=room)
      (population:=population) (prior:=prior) (counts:=counts) (live:=live) (empty:=empty) (pinCode:=pinCode)
      (arity:=arity) (op:=op) (labels:=labels) (flags:=flags) (stored:=stored) (paid:=paid)
      (bitsFit:=bitsFit) (birth:=birthAt s.2.val) (shape:=shape) (lo:=lo) (gs:=gs) (rad:=rad) (field:=field)
      (hostFit:=hostFit) (V:=V) (refD:=refD) (refK:=refK) (refN:=refN) (refC:=refC) (bl:=bl)
      (hb:=hb) (mg:=mg) (bands:=bands) (stepFit:=stepFit) (blockFit:=blockFit)
      (origPrevious:=origPrevious) (origBorn:=origBorn) (large:=large) («prefix»:=«prefix») (wide:=wide)
      (floor:=floor) (entry:=entry) (mat:=mat) (homes:=homes) (groups:=groups) (bits_:=bits_)
      (U:=U) (chip:=chip) (nameRoom:=nameRoom) (x:=(⟨t,s.1⟩:NodeOrder.All next)) (arg:=s.2) (fits:=nodeFit s.1) (written:=argFit s)
      (wire:=e) (piece:=d) (length:=fit) auth rankRoom nameFit argumentsFit (resident s) (mouthResident s)
      demand grain scale mouthSize first supply (birthBytes s) fromRaw).1
  constructor
  · intro n j e d fit read
    let s:DescentLocalPrivateNames.Slot recipe:=⟨n,j⟩
    exact (congrArg (Pointer.ofKey 0) (value s)).trans <|
      registered_public_cable
      (v:=v) (oldFit:=oldFit) (selected:=selected) (choiceEq:=choiceEq)
      (arch:=arch) (m:=m) (parts:=parts) (B:=B) (tokens:=tokens) (age:=age) (radix:=radix)
      (hp:=hp) (one:=one) (pin:=pin) (sh:=sh) (unit:=unit) (ports:=ports) (mem:=mem) (room:=room)
      (population:=population) (prior:=prior) (counts:=counts) (live:=live) (empty:=empty) (pinCode:=pinCode)
      (arity:=arity) (op:=op) (labels:=labels) (flags:=flags) (stored:=stored) (paid:=paid)
      (bitsFit:=bitsFit) (birth:=birthAt s.2.val) (shape:=shape) (lo:=lo) (gs:=gs) (rad:=rad) (field:=field)
      (hostFit:=hostFit) (V:=V) (refD:=refD) (refK:=refK) (refN:=refN) (refC:=refC) (bl:=bl)
      (hb:=hb) (mg:=mg) (bands:=bands) (stepFit:=stepFit) (blockFit:=blockFit)
      (origPrevious:=origPrevious) (origBorn:=origBorn) (large:=large) («prefix»:=«prefix») (wide:=wide)
      (floor:=floor) (entry:=entry) (mat:=mat) (homes:=homes) (groups:=groups) (bits_:=bits_)
      (U:=U) (chip:=chip) (nameRoom:=nameRoom) (x:=(⟨t,s.1⟩:NodeOrder.All next)) (arg:=s.2) (fits:=nodeFit s.1) (written:=argFit s)
      auth rankRoom nameFit argumentsFit (resident s) (mouthResident s) demand grain scale mouthSize first supply
      (birthBytes s) e d fit read wireFit peerFit wireWide peerWide cutRead
  · intro n j z d fit read
    let s:DescentLocalPrivateNames.Slot recipe:=⟨n,j⟩
    exact registered_site_pin_decoded
      («ticket»:=ticket) (arch:=arch) (tokens:=tokens) (age:=age) (radix:=radix)
      (ports:=ports) (mem:=mem) (room:=room) (population:=population) (prior:=prior) (priorCount:=counts)
      (old_live:=live) (old_empty:=empty) (hp:=hp) (one:=one) (pin:=pin) (sh:=sh) (unit:=unit)
      (pinCode:=pinCode) (arity:=arity) (op:=op) (labels:=labels) (flags:=flags) (stored:=stored)
      (paid:=paid) (bitsFit:=bitsFit) (birth:=birthAt j.val) (v:=phys) (shape:=shape) (lo:=lo) (gs:=gs)
      (rad:=rad) (field:=field) (hostFit:=hostFit) (V:=V) (large:=large) (mouth:=ports₃)
      (published:=(phys).wideMaterialValues R₀ B.material bands serial peer) (Rbig:=R₀) (matB:=bl)
      (matH:=hb) (matG:=mg) (room₁:=nameRoom)
      auth limit t capacity writtenAt s (resident s) z d fit read

private abbrev RegisteredArchiveChosenHeadersStatement : Prop := type_of% @registered_chosen_headers_proof

/-- The three actual site fields accepted by the ordinary chronological header writer.
The four predecessor and one mouth source page are indexed by the requested operand. -/
theorem registered_chosen_headers : RegisteredArchiveChosenHeadersStatement := @registered_chosen_headers_proof

end Site
end
end Hierarchy.DescentLocalArchiveOrder.PaddedOrigin

end OAI
