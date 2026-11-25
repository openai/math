import OAI.Hierarchy.DescentSelectedAcquiredGeometry
import OAI.Hierarchy.DescentGatheredRangeWord

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

open DescentOrdinaryAtomFieldRAM.ScalarOperand DescentHaloWalkRAM DescentOperandVectorArena
private def fieldWidth {D k K cap H G a b n mb : ℕ} (width:a=b) (x:Values D k K cap H G a n mb):
    Values D k K cap H G b n mb where
  walks:=x.walks
  old j h g:=(x.old j h g).cast (congrArg (fun t:ℕ=>2^(t*K)) width)
  born j t p h g:=(x.born j t p h g).cast (congrArg (2^·) width)
  wanted:=x.wanted
  venues:=x.venues
  counts:=x.counts

private theorem fieldWidth_reindex {D k K cap H G a b n mb:ℕ} (width:a=b) (x:Values D k K cap H G a n mb):
    x.reindex rfl width=fieldWidth width x:=by
  cases width
  rfl

private theorem source_words_eq {D k K cap H G a n b:ℕ}
    {left right:Values D k K cap H G a n b}
    (ww:∀h j,left.walks h j=right.walks h j)
    (oo:∀x h g,(left.old x h g).val=(right.old x h g).val)
    (bb:∀x t s h g,(left.born x t s h g).val=(right.born x t s h g).val)
    (w:∀h g,(left.wanted h g).val=(right.wanted h g).val)
    (vv:∀h g j,(left.venues h g j).val=(right.venues h g j).val)
    (cc:∀h g j,(left.counts h g j).val=(right.counts h g j).val):left=right:=by
  have hw:left.walks=right.walks:=funext fun h=>funext (ww h)
  have ho:left.old=right.old:=by funext x h g;exact Fin.ext (oo x h g)
  have hb:left.born=right.born:=by funext x t s h g;exact Fin.ext (bb x t s h g)
  have hn:left.wanted=right.wanted:=by funext h g;exact Fin.ext (w h g)
  have hv:left.venues=right.venues:=by funext h g j;exact Fin.ext (vv h g j)
  have hc:left.counts=right.counts:=by funext h g j;exact Fin.ext (cc h g j)
  cases left;cases right
  cases hw;cases ho;cases hb;cases hn;cases hv;cases hc
  rfl

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
theorem selected_acquired_references (age:i<S.length) (wide:Fintype.card prior.V≤H₀)
    (form:(entry₀).InputShape (v₀))
    (old:Pages (entry₀).previous.operands→Fin (entry₀).previous.blocks→Fin (entry₀).previous.hosts→Fin (entry₀).previous.groups→
      Cell (DescentOrdinaryPriorRetile.digits (entry₀).previous))
    (parts:Fin H₀→Fin G₀→DepotRAM.Parts (entry₀).clip.venue.socket)
    (roles:Fin (entry₀).previous.blocks→Fin (entry₀).previous.hosts→Fin G₀→Cell (roleWidth*ports.nodes))
    (active:Active) (hubs:Fin H₀→Cell 1)
    (ranks:(pop₀).donors=(v₀).reference.donors) (name:(pop₀).nameBits=nb)
    (bitsFit:(rc₀).size+2=ports.operandBits)  :
    let axes:=selected_w_axes X G S br ticket before tail cut ports op tailBits drift degree payload seats root ordinary
    let ar:=ordinary_publication_arities X G S br ticket before tail cut ports op tailBits drift degree payload seats root ordinary
    let peer:=hostRotor (prior.vertex.trans (Fin.castLEEmb wide)) (hostRoster prior.placement (prior.vertex.trans Fin.valEmbedding))
    let pull:=fun y:Fin GS=>(S.groupDigits age radix).symm (finProdFinEquiv.symm y)
    let clip:=(entry₀).clip
    let bitsAt:(v₀).reference.bits=ports.operandBits:=bitsFit
    let oldWords:=fun pg x h y=>((entry₀).oldInput (v₀) form floor₀ (mat₀) old pg x h (pull y)).cast
      (congrArg (fun a:ℕ=>2^(a*ports.nodes)) bitsAt)
    let bornWords:=fun pg x (t:Fin trueCap) party h y=>((entry₀).bornInput (v₀) form floor₀ (mat₀) parts pg
      x (t.cast axes.1.symm) party h (pull y)).cast (congrArg (2^·) bitsAt)
    let data₀:=(entry₀).venueWord (v₀) parts active hubs peer (congrArg₂ (·*·) ar.1 ar.2)
    let realRows:=fun pg l=>(entry₀).registeredValues (v₀) form floor₀ (mat₀) old parts roles (Gather.reaching peer)
      data₀ name ranks pg l
    (fun pg l=>onSourceAxes axes.1 axes.2.2 pull (realRows pg l))=
      (acquiredReferences (cap:=prior) («mb»:=mb) age radix ports (v₀) wide axes.2.1 rfl rfl bitsFit
        (clip.core.values parts active) (fun h _=>hubs h) ((entry₀).roleValues (v₀) roles)
          oldWords bornWords):=by
  intro axes ar peer pull clip bitsAt oldWords bornWords data₀ realRows
  funext pg l
  have read:=selected_acquired_geometry X G S br ticket before tail cut ports op tailBits drift degree payload seats root
    ordinary age wide form old parts roles active hubs ranks name pg l
  change onSourceAxes _ _ _ _=_ at read
  apply read.trans
  unfold acquiredReferences
  erw [fieldWidth_reindex]
  apply source_words_eq <;> intros <;> rfl

end
end Hierarchy.DescentSixParty.SeedNamed.Branch

end OAI
