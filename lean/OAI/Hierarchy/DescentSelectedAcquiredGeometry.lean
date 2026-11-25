import OAI.Hierarchy.DescentNamedCutPublishedHeaders
import OAI.Hierarchy.DescentRegisteredAcquiredGeometry
import OAI.Hierarchy.DescentAcquiredOriginSelection
import OAI.Hierarchy.DescentSelectedAcquiredRows

namespace OAI
/-! All six source columns of the chosen W share the original dated geometry. -/
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

include before tail cut in
/-- The low-address, cable capacity and population of W, expressed in the original cut's axes. -/
theorem selected_w_axes :
    (v₀).reference.capacity=trueCap ∧ (vx₀).lows=pitch₀ ∧ nb=Packed.bits pitch₀:=by
  let date:=DonorDate.atDate G S g k i p
  have chosen:ticket.donorDate=date:=donor_date_eq X G S br ticket before tail cut
  have degree_:deg₀=date.degree:=congrArg DonorDate.degree chosen
  have capacity_:trueCap=date.cap:=congrArg DonorDate.cap chosen
  have low:(vx₀).lows=pitch₀:=by
    change (2^(k+1)-1)*DescentOrdinaryVenueReturn.shapeSlots date.degree=pitch₀
    rw [←degree_]
  exact ⟨capacity_.symm,low,congrArg Packed.bits low⟩

/-- Pull back a genuine wide W value to the predecessor's old group and actual cable
capacity. This definition exposes what the casts do to every actor/rank digit. -/
def onSourceAxes {D k K cap cap' H G G' a n n' b : ℕ}
    (capacity:cap=cap') (width:n=n') (group:Fin G'→Fin G)
    (v:Values D k K cap H G a n b):Values D k K cap' H G' a n' b where
  walks:=v.walks
  old x h g:=v.old x h (group g)
  born x t who h g:=v.born x (t.cast capacity.symm) who h (group g)
  wanted h g:=(v.wanted h (group g)).cast (congrArg (2^·) width)
  venues h g j:=(v.venues h (group g) (j.cast (congrArg (DescentPackedActorMask.actors (breadth D*2^k)) capacity.symm))).cast (congrArg (2^·) width)
  counts h g:=v.counts h (group g)


private theorem value_ext {D k K cap H G a n b:ℕ}
    {left right:Values D k K cap H G a n b} (walks:left.walks=right.walks)
    (old:left.old=right.old) (born:left.born=right.born) (want:left.wanted=right.wanted)
    (venue:left.venues=right.venues) (count:left.counts=right.counts):left=right:=by
  cases left;cases right
  cases walks;cases old;cases born;cases want;cases venue;cases count
  rfl

include before tail cut in
/-- The current physical roster, donor chips, hub flag and primitive cells determine all
six aligned W columns, in exactly the attained successor group/block order. -/
theorem selected_acquired_geometry (age:i<S.length) (wide:Fintype.card prior.V≤H₀)
    (form:(entry₀).InputShape (v₀))
    (old:Pages (entry₀).previous.operands→Fin (entry₀).previous.blocks→Fin (entry₀).previous.hosts→Fin (entry₀).previous.groups→
      Cell (DescentOrdinaryPriorRetile.digits (entry₀).previous))
    (parts:Fin H₀→Fin G₀→DepotRAM.Parts (entry₀).clip.venue.socket)
    (roles:Fin (entry₀).previous.blocks→Fin (entry₀).previous.hosts→Fin G₀→Cell (roleWidth*ports.nodes))
    (active:Active) (hubs:Fin H₀→Cell 1)
    (ranks:(pop₀).donors=(v₀).reference.donors) (name:(pop₀).nameBits=nb)
    (pg:Fin (vx₀).pageCount) (l:Fin (vx₀).lows):
    let axes:=selected_w_axes X G S br ticket before tail cut ports op tailBits drift degree payload seats root ordinary
    let ar:=ordinary_publication_arities X G S br ticket before tail cut ports op tailBits drift degree payload seats root ordinary
    let peer:=hostRotor (prior.vertex.trans (Fin.castLEEmb wide)) (hostRoster prior.placement (prior.vertex.trans Fin.valEmbedding))
    let pull:=fun y:Fin GS=>(S.groupDigits age radix).symm (finProdFinEquiv.symm y)
    let clip:=(entry₀).clip
    let geom:=acquiredGeometry (cap:=prior) (fieldBits:=(v₀).reference.bits) (K₀:=ports.nodes) («mb»:=mb)
      age radix wide (clip.core.values parts active) (fun h _=>hubs h) ((entry₀).roleValues (v₀) roles) (l.cast axes.2.1)
    let realRows:=(entry₀).registeredValues (v₀) form floor₀ (mat₀) old parts roles (Gather.reaching peer)
      ((entry₀).venueWord (v₀) parts active hubs peer (congrArg₂ (·*·) ar.1 ar.2)) name ranks pg l
    onSourceAxes axes.1 axes.2.2 pull realRows={geom with
      old:=fun x h y=>realRows.old x h (pull y)
      born:=fun x t party h y=>realRows.born x (t.cast axes.1.symm) party h (pull y)}:=by
  intro axes ar peer pull clip geom realRows
  have normalized:=(entry₀).registered_acquired_geometry (v₀) form floor₀ (mat₀) old parts roles active hubs peer
    (congrArg₂ (·*·) ar.1 ar.2) name ranks pg l ar.1 ar.2
  change onSourceAxes _ _ _ _={geom with old:=_,born:=_}
  have measuredEq : realRows = _ := normalized
  rw [measuredEq]
  have own:(Packed.token (some l)).val=(Packed.token (some (l.cast axes.2.1))).val:=rfl
  apply value_ext
  · rfl
  · rfl
  · rfl
  · funext h y
    apply Fin.ext
    exact (Fin.val_cast_of_lt (n:=2^nb) (a:=(Packed.token (some l)).val) (Packed.token (some l)).isLt).trans own
  · funext h y j
    apply Fin.ext
    rfl
  · funext h y j
    rfl

end
end Hierarchy.DescentSixParty.SeedNamed.Branch

end OAI
