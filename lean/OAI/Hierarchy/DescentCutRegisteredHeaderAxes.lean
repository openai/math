import OAI.Hierarchy.DescentCutAcquiredNumerals
import OAI.Hierarchy.DescentCutAcquiredSources
import OAI.Hierarchy.DescentAcquiredPriorHeader

namespace OAI
/-! All six components of the actual registered W at each preceding header page. -/
namespace Hierarchy.DescentSixParty.SeedNamed.Branch
open DescentDatedAddressBook DescentCompiler.TerminalScale DescentCompiler Chronology DescentPacking.PackedMatch.Local.Stage.Dated
open DescentPacking.PackedMatch.Local.Stage
open DescentInitialHost DescentColonies Catalyst DescentMixedRouter DescentResetInvoice
open ThreeFlat.RAM PhysicalProcedure Computability.VPVNP.BurstRAM PrivateRAM
noncomputable section
set_option quotPrecheck false
set_option hygiene false

variable {F : Type} [Field F] {cp pins : ℕ} (X : Approximation F cp pins) (G : PoweredGadget F) (S : AtomSchedule)
variable {k n h C f g p R : ℕ}
local notation "wire" => S.epochPower^S.priceExponent
local notation "s" => S.firstWidth G.b p
local notation "price" => (1/((s:ℝ)*(wire:ℝ)):ℝ)
local notation "fee" => (((S.initialSites*S.copies:ℕ):ℝ)/S.epochPower)
local notation "u" => price*(wire:ℝ)
local notation "Ht" => GroupStage.depthBound (atRound S.rounds) n f g
variable {he : 0 ≤ fee} {hu : 0 ≤ u} {radix : S.radix=2^k}
variable {run : Epochs G hu he (h:=h) (C:=C) («Ht»:=Ht) (t:=S.rounds) S.height
      (initial X S.copies s (S.groupCount 0) k (S.initialDigits radix))}
    {c : (Epochs.finish G hu he run).Choice} (br : Branch X G S radix R run c)
local notation "P" => (Σ _ : Fin S.copies,Fin (Fintype.card (Port pins X.width)))
local notation "bits" => (fun _ : P=>s*1)
variable {W : MarkedWorld F 0 P bits} {i z D z' D' : ℕ} {rate : ℝ}
    {prior : Reached W G price fee S k i z D wire s} {T : StageInput W G rate fee}
    {nonneg : 0 ≤ fee} {choice : (T.result nonneg).Choice} {norm : Normalize ((T.result nonneg).state choice)}
    {next : Reached norm.result G price fee S k (i+1) z' D' wire s}
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

open DescentLocalArchiveOrder.PaddedOrigin DescentScalarVenueMask DescentPacking.PackedMatch.Local.Stage
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
open DescentOrdinaryOriginMask
variable {w shelfHeader headerBase pos code exec}

/-- Splitting the whole previous group into a new group and a block commutes with
both casts in the registered W. This keeps its origin and newborn fields as well as its book. -/
theorem source_axes_group {D k₀ K c c' H G' J' a n n' mb₀:ℕ}
    (cap:c=c') (width:n=n') (groups:G'=J') (pull:Fin J'→Fin G')
    (order:∀y,y.cast groups.symm=pull y) (v:Values D k₀ K c H G' a n mb₀) :
    onSourceAxes cap width id (groupValues groups v)=onSourceAxes cap width pull v:=by
  subst J'
  have eqn:pull=id:=funext (fun y=>(order y).symm)
  subst pull
  rfl

include before tail cut in
theorem cut_acquired_axes (age:i<S.length) (order:stores.rotor=peer_)
    (width:(rc₀).size+2=ports.operandBits) :
    let axes:=selected_w_axes X G S br ticket before tail cut ports op tailBits drift degree payload seats root ordinary
    let pull:=fun y:Fin GS=>(S.groupDigits age radix).symm (finProdFinEquiv.symm y)
    let oldWords:=fun pg x h y=>((entry₀).oldInput (v₀) stores.inputs floor₀ (mat₀) stores.old pg x h (pull y)).cast
      (congrArg (fun a:ℕ=>2^(a*ports.nodes)) width)
    let bornWords:=fun pg x (t:Fin trueCap) party h y=>((entry₀).bornInput (v₀) stores.inputs floor₀ (mat₀) stores.parts pg
      x (t.cast axes.1.symm) party h (pull y)).cast (congrArg (2^·) width)
    (fun pg l=>onSourceAxes axes.1 axes.2.2 id (stores.books pg l))=
      acquiredReferences (cap:=prior) («mb»:=mb) age radix ports (v₀) stores.oldFit axes.2.1 rfl rfl width
        ((entry₀).clip.core.values stores.parts stores.active) (fun h _=>stores.hubs h) ((entry₀).roleValues (v₀) stores.roles)
        oldWords bornWords:=by
  intro axes pull oldWords bornWords
  refine Eq.trans ?_ (selected_acquired_references X G S br ticket before tail cut ports op tailBits drift degree payload seats root ordinary age stores.oldFit stores.inputs stores.old stores.parts stores.roles
    stores.active stores.hubs stores.ranks stores.names width)
  funext pg l
  let rowFor := fun (rho : Fin H₀ → Fin deg₀ → Option (Fin H₀)) =>
    (entry₀).registeredValues (v₀) stores.inputs floor₀ (mat₀) stores.old stores.parts stores.roles
      (Gather.reaching rho) ((entry₀).venueWord (v₀) stores.parts stores.active stores.hubs rho stores.width)
      stores.names stores.ranks pg l
  have source : stores.books pg l = groupValues stores.groups (rowFor peer_) :=
    (stores.registered pg l).trans (congrArg (fun rho => groupValues stores.groups (rowFor rho)) order)
  exact (congrArg (onSourceAxes axes.1 axes.2.2 id) source).trans
    (source_axes_group axes.1 axes.2.2 stores.groups pull (split_source age radix stores.groups) (rowFor peer_))

open DescentLocalArchiveOrder DescentKernelHistory DescentRetainedRangeDigits
variable (B : BitDescription W) (places : DatePorts.RangeRoom ports prior B)
    (enough : Fintype.card prior.V≤ports.operandHosts)
theorem cut_prior_header_inputs (precision : 2≤ports.operandBits)
    (packed : ports.operandBits*ports.nodes*ports.operandLanes≤w)
    (j : Fin (vx₀).operands) (f₀ : Fin 4) (x : Block k) (h₀ : Fin (Fintype.card prior.V)) (groupIndex : Fin OG) :
    ((entry₀).oldInput (v₀) stores.inputs floor₀ (mat₀) stores.old (DescentOperandStateBanks.page (f₀.castLE (by decide : 4≤7)) j)
        x (h₀.castLE stores.oldFit) groupIndex).val=
      (DatePorts.physicalHeaderSource ports prior B places enough (wired original) j.val f₀ x h₀ groupIndex).val:=by
  have oldLayout : (entry₀).previous=ports.rangeLayout:=by
    change ports.argumentLayout (2^k)=ports.rangeLayout
    rw [places.radix]
    rfl
  have width : (entry₀).previous.size+2=ports.operandBits:=ports.argument_width _ precision
  apply acquired_prior_header_of_reads prior B ports places enough (wired original) (v₀) (entry₀) stores.inputs floor₀
    (mat₀) oldLayout width rfl rfl stores.oldFit stores.old rfl stores.oldRead
  change ((entry₀).previous.size+2)*ports.nodes*ports.operandLanes≤w
  rwa [width]



end
end Hierarchy.DescentSixParty.SeedNamed.Branch

end OAI
