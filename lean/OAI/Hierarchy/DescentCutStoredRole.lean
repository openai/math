import OAI.Hierarchy.DescentCutAcquiredSources
import OAI.Hierarchy.DescentNodeCellRoleCount
import OAI.Hierarchy.DescentSparseAcquiredRole

namespace OAI
/-! Previous primitive labels and exact all-node counts from the same registered cut. -/
namespace Hierarchy.DescentSixParty.SeedNamed.Branch
open DescentDatedAddressBook DescentCompiler.TerminalScale DescentCompiler Chronology DescentPacking.PackedMatch.Local.Stage.Dated
open DescentPacking.PackedMatch.Local.Stage
open DescentInitialHost DescentColonies Catalyst DescentMixedRouter DescentResetInvoice
open ThreeFlat.RAM PhysicalProcedure Computability.VPVNP.BurstRAM PrivateRAM
open scoped Classical
noncomputable section
set_option quotPrecheck false
set_option maxRecDepth 7000
set_option maxHeartbeats 900000
set_option cleanup.letToHave false

variable {F : Type} [Field F] {cp pins : ℕ} (X : Approximation F cp pins) (G : PoweredGadget F) (S : AtomSchedule)
variable {k n h C f g p R : ℕ}
local notation "wire" => S.epochPower^S.priceExponent
local notation "s" => S.firstWidth G.b p
local notation "price" => (1/((s:ℝ)*(wire:ℝ)):ℝ)
local notation "fee" => (((S.initialSites*S.copies:ℕ):ℝ)/S.epochPower)
local notation "u" => price*(wire:ℝ)
local notation "Ht" => GroupStage.depthBound (atRound S.rounds) n f g
variable {he : 0 ≤ (((S.initialSites * S.copies : ℕ) : ℝ) / S.epochPower)}
    {hu : 0 ≤ (1 / ((S.firstWidth G.b p : ℝ) * (S.epochPower : ℝ) ^ S.priceExponent)) *
      (S.epochPower : ℝ) ^ S.priceExponent} {radix : S.radix=2^k}
variable {run : Epochs G hu he (h:=h) (C:=C) («Ht»:=GroupStage.depthBound (atRound S.rounds) n f g)
      (t:=S.rounds) S.height (initial X S.copies (S.firstWidth G.b p) (S.groupCount 0) k (S.initialDigits radix))}
    {c : (Epochs.finish G hu he run).Choice}
    (br : Branch X G S (p:=p) (n:=n) (h:=h) (C:=C) (f:=f) (g:=g) radix R run c)
local notation "P" => (Σ _ : Fin S.copies,Fin (Fintype.card (Port pins X.width)))
local notation "bits" => (fun _ : P=>s*1)
variable {W : MarkedWorld F 0 (Σ _ : Fin S.copies,Fin (Fintype.card (Port pins X.width))) (fun _ => S.firstWidth G.b p*1)} {i z D z' D' : ℕ} {rate : ℝ}
    {prior : Reached W G (1 / ((S.firstWidth G.b p : ℝ) * (S.epochPower : ℝ) ^ S.priceExponent)) (((S.initialSites*S.copies:ℕ):ℝ)/S.epochPower) S k i z D (S.epochPower^S.priceExponent) (S.firstWidth G.b p)} {T : StageInput W G rate (((S.initialSites*S.copies:ℕ):ℝ)/S.epochPower)}
    {nonneg : 0 ≤ (((S.initialSites*S.copies:ℕ):ℝ)/S.epochPower)} {choice : (T.result nonneg).Choice} {norm : Normalize ((T.result nonneg).state choice)}
    {next : Reached norm.result G (1 / ((S.firstWidth G.b p : ℝ) * (S.epochPower : ℝ) ^ S.priceExponent)) (((S.initialSites*S.copies:ℕ):ℝ)/S.epochPower) S k (i+1) z' D' (S.epochPower^S.priceExponent) (S.firstWidth G.b p)}
    (ticket : OrdinaryLink prior nonneg T choice norm next)
    (before : Path br.origin.source prior) (tail : Path next br.target)
    (cut : (Path.ordinary before ticket).append tail=br.path)
local notation "A" => prior.placement
local notation "calendar" => capCalendar G.b S.rounds g S.height


set_option quotPrecheck false
variable (ports : DatePorts) (op : RotorSpec) (tailBits drift degree payload seats root : ℕ)
    (ordinary : ℕ→Dated.Ordinary)
local notation "books₀" => OrdinaryBooks.atDate G S op g k i p tailBits drift degree payload seats ports
local notation "base₀" => (books₀).onTicket ticket g tailBits p f payload seats ports.venue.lanes ports.io.roster ordinary
local notation "floor₀" => (base₀).stageStart root
local notation "v₀" => DatePorts.ordinaryModel ports ticket op g tailBits p f drift degree payload seats root ordinary
local notation "entry₀" => (base₀).registeredEntry ports floor₀
local notation "mat₀" => (base₀).registered_match ports floor₀ (Nat.le_max_left ports.argumentsPerNode (S.retainedArgumentsAt G drift))

open DescentDatedPriorOperand DescentOperandStateBanks DescentHaloWalkRAM DescentSharedCableNames
open PhysicalOrdinary.ArgumentEntry
open DescentDatedOperandReadPipeline DescentSIMDLookup DescentPackedZip DescentPackedColony
open DescentOrdinaryAtomFieldRAM DescentOrdinaryAtomFieldRAM.ScalarOperand DescentOperandVectorArena DescentOrdinaryOriginMask
open DescentRawCablePanel ProtocolRAM
open scoped Classical Fin.CommRing
local notation "sh₀" => (base₀).registered_geometry ports floor₀
local notation "rc₀" => (v₀).resolver
local notation "vx₀" => (v₀).vector
local notation "bn₀" => (v₀).bornBook
local notation "g₀" => (v₀).ticketReadGeometry
local notation "M₀" => (rc₀).lanes
local notation "W₀" => (vx₀).lanes*(vx₀).radix
local notation "vecAt" => (v₀).vectorStart floor₀
local notation "mouthEnd₀" => (v₀).originMouthEnd floor₀
local notation "headerEnd" => (v₀).operandHeaderEnd floor₀
local notation "e₀" => (v₀).material
local notation "fmt₀" => (v₀).ticket.depotShape (v₀).short
local notation "ps₀" => (v₀).operandPathStart floor₀
local notation "refs₀" => ((entry₀).directory (v₀) floor₀ (mat₀)).refs
local notation "Val₀" => References.Rows (v₀).vector (v₀).reference.degree (v₀).reference.k (v₀).reference.oldNodes
  (v₀).reference.capacity ((rc₀).size+2)
local notation "dims₀" => DatePorts.ordinary_header_dimensions ports ticket op g tailBits p f drift degree payload seats root ordinary
local notation "H₀" => (entry₀).clip.venue.hosts
local notation "G₀" => (entry₀).clip.venue.groups
local notation "pop₀" => (entry₀).population (v₀) floor₀
local notation "Active" => Fin H₀→Fin G₀→Cell (1*(entry₀).clip.venue.socket.blocks)
local notation "RealPeers" => Fin H₀→Fin (entry₀).clip.venue.socket.degree→Option (Fin H₀)

variable (w shelfHeader headerBase : ℕ) (pos : 0<k)
    (code : DatePorts.OrdinaryCodeRoom ports ticket op g tailBits p f drift degree payload seats root ordinary w)
    (exec : DatePorts.OrdinaryExecutionRoom ports ticket op g tailBits p f drift degree payload seats root ordinary
      w shelfHeader headerBase code)
local notation "wired" m:arg => DatePorts.ordinarySignedMemory ports ticket op g tailBits p f drift degree
  payload seats root ordinary w shelfHeader headerBase pos code exec m


local notation "steps₀" => (v₀).issuedSteps root ports (entry₀) code.signed w (mat₀) (sh₀) code.blocks code.paths
  code.slots code.chip code.endFit code.packed code.radix code.funded
local notation "donors" m:arg => DatePorts.ordinaryDonorMemory ports ticket op g tailBits p f drift degree
  payload seats root ordinary w shelfHeader headerBase pos code exec m
local notation "phys₀" => (v₀).withIssuedSigned
local notation "room₀" => (v₀).signedReturn floor₀ ports.io ports.archive.count (steps₀).parts (steps₀).adjacency w
local notation "page₀" => (⟨0,Nat.mul_pos (by decide : 0<7) code.slots⟩:Fin (7*(vx₀).operands))
open DescentGroupPeerOrder DescentStageEdgeReceipt DescentPacking.PackedMatch.Local

open DescentScalarVenueMask DescentPacking.PackedMatch.Local.Stage
open DescentGroupPeerOrder DescentOrdinaryAtomFieldRAM
local notation "deg₀" => prior.placement.degree
local notation "shelf" => DescentOrdinaryVenueReturn.shapeSlots deg₀
local notation "pitch₀" => (2^(k+1)-1)*shelf
local notation "trueCap" => prior.placement.cap
local notation "GS" => S.groupCount (i+1)*2^k
local notation "OG" => S.groupCount i
local notation "roleWidth" => (pop₀).roleBits
local notation "nb" => (v₀).reference.nameBits
local notation "mb" => (v₀).reference.countBits


variable {original:Memory w} (stores:CutStores X G S (f:=f) (g:=g) (p:=p) (radix:=radix) ticket ports op tailBits drift degree payload seats root ordinary w shelfHeader headerBase pos code exec original)
local notation "peer_" => hostRotor (prior.vertex.trans (Fin.castLEEmb stores.oldFit))
  (hostRoster prior.placement (prior.vertex.trans Fin.valEmbedding))

open DescentLocalArchiveOrder DescentPrimitivePalette DescentKernelHistory DescentRetainedRangeDigits
variable (B : BitDescription W) (numbering : Local B) (places : DatePorts.RangeRoom ports prior B)
    (enough : Fintype.card prior.V≤ports.operandHosts)

open DescentScalarVenueMask DescentGroupPeerOrder DescentHaloWalkRAM DescentGL
open DescentSortedHaloRaster DescentPaidResidentCount
local notation "rr₀" => BitDescription.scannedRows nonneg T
local notation "ly₀" => bestLayout (branchWidth G (fun _:(rr₀).pairs=>T.z) ((rr₀).profile choice))
local notation "groups₀" => GadgetNetwork.newSite W.graph (rr₀).pick ly₀ (rr₀).pack
local notation "tall₀" => (entry₀).clip.core.values stores.parts stores.active
local notation "tokens₀" => fun b j h g=>(tall₀) b j (h.castLE stores.oldFit) g
local notation "nativeRank" => groupRank Fin.valEmbedding (prior.vertex.trans Fin.valEmbedding)


local notation "tokenWidth_" => printedBits G s (S.grainAt G.b p 0) op
local notation "Q₀" => fun x (v:Fin (Fintype.card prior.V)) g=>
  DescentOrdinaryAtomFieldRAM.RoleCounts.count (K:=ports.nodes) mb
    (((entry₀).roleValues (v₀) stores.roles) x (v.castLE stores.oldFit) g)



private theorem extend_reindexed_role {oldHosts newHosts oldGroups archiveGroups bitWidth : ℕ}
    (groups : oldGroups = archiveGroups) (roles : Fin oldHosts → Fin oldGroups → Cell bitWidth)
    (host : Fin newHosts) (group : Fin oldGroups) :
    DescentOrdinaryHostPad.extend newHosts (fun h q => roles h (q.cast groups.symm)) host (group.cast groups) =
      DescentOrdinaryHostPad.extend newHosts roles host group := by
  subst archiveGroups
  rfl

theorem cut_sparse_role
    (labels : NodeOrder.All B→Label G (S.firstWidth G.b p) (S.grainAt G.b p 0) op)
    (issued : ∀(x : Block k) (h : Fin ports.operandHosts) (g : Fin (S.groupCount i)),(stores.roles x h g).val=(DescentSIMDLookup.encode (printedBits G (S.firstWidth G.b p) (S.grainAt G.b p 0) op) ports.nodes (fun j=>
  (DatePorts.slotAt ports prior B numbering places (x.cast (congrArg (2^·) places.radix)) j h (g.cast places.groups)).elim 0
    (fun y=>token G (S.firstWidth G.b p) (S.grainAt G.b p 0) op (labels y)))).val)
    (x:Block k) (h:Fin (Fintype.card prior.V)) (g:Fin OG):
    (((entry₀).roleValues (v₀) stores.roles) x (h.castLE stores.oldFit) g).val=
      (Reached.NodeCells.rolePage (N:=ports.nodes) prior B numbering
        (fun y=>token G s (S.grainAt G.b p 0) op (labels y)) x h g).val:=by
  let earlier (x : Block k) (h : Fin ports.operandHosts) (q:Fin ports.venue.groups):=stores.roles x h (q.cast places.groups.symm)
  have posted:∀(b : Block k) (h : Fin ports.operandHosts) (g : Fin ports.venue.groups),(earlier b h g).val=(encode tokenWidth_ ports.nodes (fun n=>
      (DatePorts.slotAt ports prior B numbering places (b.cast (congrArg (2^·) places.radix)) n h g).elim 0
        (fun y=>token G s (S.grainAt G.b p 0) op (labels y)))).val:=by
    intro b h g
    exact issued b h (g.cast places.groups.symm)
  have read:=DatePorts.acquired_sparse_role_page prior B numbering ports places op labels stores.oldFit earlier posted x h g
  have same := extend_reindexed_role places.groups (stores.roles x) (h.castLE stores.oldFit) g
  exact (congrArg Fin.val same).symm.trans read

theorem cut_stored_role
    (labels : NodeOrder.All B→Label G (S.firstWidth G.b p) (S.grainAt G.b p 0) op)
    (issued : ∀(x : Block k) (h : Fin ports.operandHosts) (g : Fin (S.groupCount i)),(stores.roles x h g).val=(DescentSIMDLookup.encode (printedBits G (S.firstWidth G.b p) (S.grainAt G.b p 0) op) ports.nodes (fun j=>
  (DatePorts.slotAt ports prior B numbering places (x.cast (congrArg (2^·) places.radix)) j h (g.cast places.groups)).elim 0
    (fun y=>token G (S.firstWidth G.b p) (S.grainAt G.b p 0) op (labels y)))).val)
    (age:i<S.length) (v:W.graph.Site) (n:(B.recipe v).Node) (j:Fin ports.nodes)
    (ord:j.val=(numbering v n).val):
    let y:=finProdFinEquiv ((S.groupDigits age radix) ((A).pos v).1)
    let original:=(entry₀).roleValues (v₀) stores.roles
    (encode tokenWidth_ ports.nodes).symm
      (original ((A).block v) ((prior.vertex ((A).pos v).2).castLE stores.oldFit) (y.cast stores.groups.symm)) j=
      token G s (S.grainAt G.b p 0) op (labels ⟨v,n⟩):=by
  intro y originalRoles
  have sparse := cut_sparse_role X G S ticket ports op tailBits drift degree payload seats root ordinary
    w shelfHeader headerBase pos code exec stores B numbering places labels issued
  have groupAt : y.cast stores.groups.symm = (prior.placement.pos v).1 :=
    Fin.ext (Chronology.DatePorts.ordinary_source_number age radix (prior.placement.pos v).1)
  have atGroup := congrArg
    (originalRoles (prior.placement.block v) ((prior.vertex (prior.placement.pos v).2).castLE stores.oldFit)) groupAt
  have atPage := Fin.ext (sparse (prior.placement.block v) (prior.vertex (prior.placement.pos v).2) (prior.placement.pos v).1)
  let readCell (page : Cell (tokenWidth_*ports.nodes)) := (encode tokenWidth_ ports.nodes).symm page j
  exact (congrArg readCell (atGroup.trans atPage)).trans
    (Reached.NodeCells.role_at prior B numbering prior.vertex (fun _ => rfl)
      (fun y => token G s (S.grainAt G.b p 0) op (labels y)) v n j ord)

theorem cut_stored_counts
    (labels : NodeOrder.All B→Label G (S.firstWidth G.b p) (S.grainAt G.b p 0) op)
    (issued : ∀(x : Block k) (h : Fin ports.operandHosts) (g : Fin (S.groupCount i)),(stores.roles x h g).val=(DescentSIMDLookup.encode (printedBits G (S.firstWidth G.b p) (S.grainAt G.b p 0) op) ports.nodes (fun j=>
  (DatePorts.slotAt ports prior B numbering places (x.cast (congrArg (2^·) places.radix)) j h (g.cast places.groups)).elim 0
    (fun y=>token G (S.firstWidth G.b p) (S.grainAt G.b p 0) op (labels y)))).val)
    (countWide:ports.nodes<2^mb) :
    (∀v,((Q₀) ((A).block v) (prior.vertex ((A).pos v).2) ((A).pos v).1).val=Fintype.card (B.recipe v).Node) ∧
    (∀x h g,(¬∃v,(A).block v=x ∧ prior.vertex ((A).pos v).2=h ∧ ((A).pos v).1=g)→(Q₀) x h g=0):=by
  let label:=fun v=>token G s (S.grainAt G.b p 0) op (labels v)
  have posLabel:∀v,label v≠0:=by
    intro v bad
    have zero:=congrArg Fin.val bad
    change ((codec (G:=G) op).store (labels v)).val+1=0 at zero
    omega
  have read:=cut_sparse_role X G S ticket ports op tailBits drift degree payload seats root ordinary w shelfHeader headerBase pos code exec stores B numbering places labels issued
  have countsAt (x:Block k) (host:Fin (Fintype.card prior.V)) (groupIndex:Fin (S.groupCount i)) :
      (Q₀) x host groupIndex = DescentOrdinaryAtomFieldRAM.RoleCounts.count (a:=tokenWidth_) (K:=ports.nodes) mb
        (Reached.NodeCells.rolePage (N:=ports.nodes) prior B numbering label x host groupIndex) :=
    congrArg (fun (row:Cell (tokenWidth_*ports.nodes)) => DescentOrdinaryAtomFieldRAM.RoleCounts.count (a:=tokenWidth_) (K:=ports.nodes) mb row)
      (Fin.ext (read x host groupIndex))
  constructor
  · intro site
    exact (congrArg Fin.val (countsAt ((A).block site) (prior.vertex ((A).pos site).2) ((A).pos site).1)).trans
      (Reached.NodeCells.role_count_at prior B numbering prior.vertex (fun _=>rfl) label posLabel site (places.capacity site) countWide)
  · intro x host groupIndex ghost
    apply (countsAt x host groupIndex).trans
    apply Reached.NodeCells.role_count_empty
    rintro ⟨site,block,hostEq,groupEq⟩
    exact ghost ⟨site,block,Fin.ext hostEq,groupEq⟩

end
end Hierarchy.DescentSixParty.SeedNamed.Branch

end OAI
