import OAI.Hierarchy.DescentRegisteredCableArchive
import OAI.Hierarchy.DescentRegisteredPointerOrigins

namespace OAI
/-! The three original job fields at the physical coordinate of every reached site. -/
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
set_option maxHeartbeats 800000
noncomputable section

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
    (tokens:DescentColonies.Block v.k → Fin count₀ → Fin OH → Fin og → DescentScalarVenueMask.Ticket walks lowNames)
local notation "stock" => Descriptors slots v.k (A).pos (A).block (ticketParent (he:=v.nonnegative) («T»:=T))
  (ticketSlot (c:=selected) ticket) (key∘group) (cap).vertex (Function.Embedding.refl _) moves tokens
variable (age:v.age<(S).length) (radix:(S).radix=2^v.k) (hp:0<p) (one:1≤ stretch) (pin:∀x,p∣v.bits x)
    (sh:WorldShape p stretch arch.bit) (unit:p∣(T).z)
    (ports:DatePorts) (mem:Memory w) (room:DatePorts.RangeRoom ports cap arch.bit)
    (population:OH≤ports.operandHosts) (prior:Local arch.bit)
    (counts:DescentColonies.Block v.k → Fin OH → Fin og → Cell mb)
    (live:∀u,(counts ((A).block u) ((cap).vertex ((A).pos u).2) ((A).pos u).1).val=Fintype.card (arch.bit.recipe u).Node)
    (empty:∀b h g,(¬∃u,(A).block u=b ∧ (cap).vertex ((A).pos u).2=h ∧ ((A).pos u).1=g) → counts b h g=0)
variable (pinCode:P → ℕ) (arity:ℕ) (op:RotorSpec) (labels:NodeOrder.All arch.bit → DescentPrimitivePalette.Label G s Z op)
    (flags:Fin (2^ports.venue.k) → Fin ports.nodes → Fin ports.operandHosts → Fin ports.venue.groups → ℕ)
local notation "ptr₀" => Reached.argumentPointer cap arch.bit prior sh hp pinCode arity
variable (stored:DatePorts.ArchiveRead ports cap arch.bit prior room sh op labels ptr₀ flags mem)
    (paid:∀v u,((sh.sites v).recipe hp).arity u≤ports.argumentsPerNode)
    (bitsFit:ports.operandBits*ports.nodes*ports.operandLanes≤w)
    (birth:Fin 4 → DescentColonies.Block v.k → Fin (A).cap → Fin 6 → Fin OH → Fin og → Cell ports.operandBits)
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
variable {stampField:ℕ} (origPrevious:DescentColonies.Block v.k → Fin OH → Fin og → Cell (stampField*ports.nodes))
    (origBorn:DescentColonies.Block v.k → Fin (A).cap → Fin 6 → Fin OH → Fin og → Cell stampField)
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
    (chip:Fin (phys).bornBook.hosts → Fin (phys).bornBook.groups → Cell (phys).bornBook.chipBits)
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


variable (birthAt:ℕ → Fin 4 → DescentColonies.Block v.k → Fin (A).cap → Fin 6 → Fin OH → Fin og → Cell ports.operandBits)
local notation:max "smallAt" j:arg f:arg => Values.transport lo gs rad field
    (rangeValues ticket arch tokens age radix counts (priorAt j f) (birthAt j f))
local notation:max "mouthAt" j:arg => Values.originTransport refD refK refN refC lo gs rad field
    (rangeValues ticket arch tokens age radix counts (priorAt j 0) (birthAt j 0))
local notation:max "pg" j:arg f:arg => (DescentOperandStateBanks.page ((f:Fin 4).castLE (by decide : 4≤7)) j).cast
    (congrArg (7*·) shape.operands)
include stored live empty paid bitsFit «prefix» stepFit blockFit in
theorem registered_chosen_sites (auth:stock) (arityFit:∀u n,((sh.sites u).recipe hp).arity n≤arity)
    (rankRoom:donorFit) (nameFit:codeFit) (argumentsFit:(ℒ).operands≤2^((ℒ).size+2))
    (resident:∀(j:Fin (ℒ).operands) f l,Values.Prefix hostFit (smallAt j.val f l) (V (pg j f) l))
    (mouthResident:∀(j:Fin (ℒ).operands) l,Values.Prefix hostFit (mouthAt j.val l) (U (mouthPage j) l))
    (demand:(phys).bornBook.demand=(G).b) (grain:(phys).bornBook.grain=p) (scale:(phys).bornBook.scale=(T).z)
    (mouthSize:11≤2^(phys).bornBook.bits)
    (first:∀i,(birthSource i).first=true)
    (supply:∀i a,((birthSource i).supplyUnits a).val=((cProf i).val a).val+(G).k)
    (birthBytes:∀(j:Fin (ℒ).operands) pair party f,
      (birthAt j.val f ((A).block (firstSite pair)) (seat₀ pair) party
        ((cap).vertex ((A).pos (firstSite pair)).2) ((A).pos (firstSite pair)).1).val=
      (component ((ℒ).size+2) (pointerAt (G).b p (T).z (birthSource pair) party j.val)
        (f.castLE (by decide : 4≤7))).val)
    (wireFit:v.target.placement.cap≤2^(phys).signed.fieldBits) (peerFit:v.target.placement.degree≤2^(phys).signed.fieldBits)
    (wireWide:v.target.placement.cap≤2^((ℒ).size+2)) (peerWide:v.target.placement.degree≤2^((ℒ).size+2))
    (cutRead:(phys).chosenGrain.val=(T).z/p) :
    Reached.PointerSites (ac).next phys next (advance ticket arch prior) after hp pinCode jobs:=by
  intro t block home group_ blockAt homeAt groupAt capacity writtenAt
  have eb:block=((block₁ t).cast rad.symm).cast shape.blocks.symm:=Fin.ext blockAt
  have eh:home=(rh t):=Fin.ext homeAt
  have eg:group_=(rg t):=Fin.ext groupAt
  subst block;subst home;subst group_
  exact registered_chosen_headers
    (v:=v) (oldFit:=oldFit) (selected:=selected) (choiceEq:=choiceEq)
      (arch:=arch) (m:=m) (parts:=parts) (B:=B) (tokens:=tokens) (age:=age) (radix:=radix)
      (hp:=hp) (one:=one) (pin:=pin) (sh:=sh) (unit:=unit) (ports:=ports) (mem:=mem) (room:=room)
      (population:=population) (prior:=prior) (counts:=counts) (live:=live) (empty:=empty) (pinCode:=pinCode)
      (arity:=arity) (op:=op) (labels:=labels) (flags:=flags) (stored:=stored) (paid:=paid)
      (bitsFit:=bitsFit) (birthAt:=birthAt) (shape:=shape) (lo:=lo) (gs:=gs) (rad:=rad) (field:=field)
      (hostFit:=hostFit) (V:=V) (refD:=refD) (refK:=refK) (refN:=refN) (refC:=refC) (bl:=bl)
      (hb:=hb) (mg:=mg) (bands:=bands) (stepFit:=stepFit) (blockFit:=blockFit)
      (origPrevious:=origPrevious) (origBorn:=origBorn) (large:=large) («prefix»:=«prefix») (wide:=wide)
      (floor:=floor) (entry:=entry) (mat:=mat) (homes:=homes) (groups:=groups) (bits_:=bits_)
      (U:=U) (chip:=chip) (nameRoom:=nameRoom)
    (t:=t) (capacity:=capacity) (writtenAt:=writtenAt) auth arityFit rankRoom nameFit argumentsFit
    (fun s=>resident (s.2.castLE (writtenAt s.1))) (fun s=>mouthResident (s.2.castLE (writtenAt s.1)))
    demand grain scale mouthSize first supply (fun s=>birthBytes (s.2.castLE (writtenAt s.1)))
    wireFit peerFit wireWide peerWide cutRead

end
end Hierarchy.DescentLocalArchiveOrder.PaddedOrigin

end OAI
