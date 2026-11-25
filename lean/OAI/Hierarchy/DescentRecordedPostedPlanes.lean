import OAI.Hierarchy.DescentRecordedResetHeldPlanes
import OAI.Hierarchy.DescentNamedIngressCode
import OAI.Hierarchy.DescentPriorArchiveDate
import OAI.Hierarchy.DescentPhysicalDateHistory

namespace OAI
/-! # The final paid venue and actor bitmap in the shared dated RAM -/
namespace Hierarchy.DescentSixParty.ClosedReset.Window
open DescentCompiler DescentDenseHostOrder DescentSIMDLookup DescentActorRaster DescentPackedZip
open DescentPaidResidentCount DescentPacking.PackedMatch.Local.Stage DescentPackedColony DescentColonies
open DescentDatedAddressBook DescentCompactVenuePeers DescentResetPeerUnionRAM DescentSortedRoster
open DescentResetHostSize DescentStageEdgeReceipt DescentPackedExchange DescentHubBits DescentSixParty.Chronology
open Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM
open scoped Classical Fin.CommRing
noncomputable section
set_option hygiene false
set_option quotPrecheck false
variable {F P:Type} [Field F] {d:ℕ} {bits:P→ℕ} {W:MarkedWorld F d P bits} {G:PoweredGadget F}
  {q ε:ℝ} {S:AtomSchedule} {k i z D n h C f g cut tail wire hist:ℕ} {ctl:ResetRates G S k D n h C f g cut tail}
  {old:Reached W G q ε S k i z D wire hist} (B:ClosedReset old ctl)
  {quant H₀ H M₀ Ma M nextM precision w:ℕ}(record:B.Recorded quant)
  (oldRoom:Fintype.card old.V≤H₀)(room:Fintype.card B.next.V≤H)
local notation "Z" => B.reset
local notation "T" => B.terminals
local notation "A" => B.next.placement
local notation "cc" => (T).commonDepth
local notation "height" => GroupStage.depthBound D n f g
local notation "Q" => (DescentDenseHostOrder.roster (Z).graph ((Z).k-cc) height).card
local notation "R" => H₀*Q
local notation "G₁" => S.groupCount (i+1)
local notation "N" => Fintype.card B.next.V
local notation "vertex" => B.frame.host.symm.toEmbedding.trans old.vertex
local notation "rank" => (vertex).trans (Fin.castLEEmb oldRoom)
local notation "raw" => (Z).rawHostRank T rank
local notation "host" => B.next.vertex.trans (Fin.castLEEmb room)
variable {a:PhysicalReset} (L:DescentResetCanvasIngress.Layout) (outer:ℕ)
local notation "floor" => L.endAddress outer
variable {u:a.DateInputs floor w} (finish:u.FinalInputs) (io:DescentPacking.PackedMatch.Local.Stage.Dated.Operands)
    (pad:Chronology.NativePhase w) (calendar:ℕ→DateCode w) (initial:Memory w)
local notation "previous" => DateCode.history calendar initial i
local notation "intake" => L.phase outer w io.hubs (fun x=>io.atoms x.val) (fun j=>io.wire j.1.val j.2.val)
local notation "inputStage" => pad.image previous
local notation "fedMem" => (intake).image inputStage
local notation "inputMem" => u.throughOperandDate.nextMemory fedMem
local notation "actualOut" => DateCode.history calendar initial (i+1)
local notation "output" => a.successor
local notation "step" => a.rebased floor
local notation "input" => PhysicalReset.FinalInputs.predecessor u
local notation "venue" => (output).venue
local notation "stop₀" => (output).finalEnd step
local notation "base" => (output).fundedEnd step
local notation "key" => (⟨(a.stencilPhase u.shape floor u.count u.hub u.g u.Y).saved,0⟩:Bank)
local notation "V" => calibrated B (venue).census H₀ H M₀ Ma M nextM precision
local notation "fields" => (V).sources input base
local notation "start" => (V).denseStart base
local notation "prepared" mem => (output).funded.memory stop₀ finish.earlier key mem
local notation "paidRAM" mem => DescentFundedCensus.memory finish.jobs base (prepared mem)

/-- Read the registered reset directly in the history of the shared instruction
stream. All source words refer to its unique before-funding checkpoint. -/
theorem recorded_posted_planes
    (posted : calendar i=DateCode.withPriorArchive pad (PhysicalReset.enterCode L outer u finish io))
    (padded : pad.Runs previous)
    (ready:u.Ready) (hubFit:io.hubs.Fits w outer)
    (atomFit:∀x:Fin (2^L.k),(io.atoms x.val).Fits w outer)
    (wireFit:∀j:L.signed.Slot,(io.wire j.1.val j.2.val).Fits w outer)
    (ingressFits:L.endAddress outer<2^w)
    (cal:venue=V)(fits:finish.Room)(size:N ≤ (input).ranks.inverse.size)(fitsN:N<2^w)
    (found:Fin R→Fin 3→Option (Fin R))
    (four:∀v:B.next.V,present (selfPeers found) (raw v)=(insert v ((Z).emittedNear T v)).map raw)
    (selfFlag:∀v:B.next.V,(∀j,found (raw v) j≠some (raw v))↔v∉(Z).emittedNear T v)
    (tag:(input).tag=publicTag ctl.board k height)
    (oldPos:0<M₀)(actorPos:0<Ma)(newPos:0<M)(occupied:0<H)(live:0<chunks G₁ M)
    (rawActor:(input).actor.base+Q*(H₀*chunks (2^cc) Ma) ≤ stop₀)
    (rankEarly:(input).ranks.count.base<stop₀)(invEarly:(input).ranks.inverse.base+N ≤ stop₀)
    (forwardEarly:(input).ranks.forward.base+R ≤ stop₀)
    (peerEarly:∀j,((input).ranks.neighbor j).base+R ≤ stop₀)
    (rankFits:R ≤ (input).ranks.forward.size)(peerFits:∀j,R≤((input).ranks.neighbor j).size)
    (paid:∀j (p:Row H₀ (2^cc) M₀),(paidRAM inputMem) (((V).original base).base+j.val*(H₀*chunks (2^cc) M₀)+(row H₀ (2^cc) M₀ p).val)=
      ((data (fun u hi=>payable (precision:=precision) B record oldRoom (finProdFinEquiv (u,j)) hi) p).val:Word w))
    (actors:∀j (p:Row H₀ (2^cc) Ma),inputMem ((input).actor.base+j.val*(H₀*chunks (2^cc) Ma)+(row H₀ (2^cc) Ma p).val)=
      ((data (Recorded.realActor (reset:=B) (shapes B) (rack B oldRoom) j) p).val:Word w))
    (count:inputMem (input).ranks.count.base=(N:Word w))
    (inverse:∀v:B.next.V,inputMem ((input).ranks.inverse.base+(B.next.vertex v).val)=((raw v).val:Word w))
    (order:∀v:B.next.V,inputMem ((input).ranks.forward.base+(raw v).val)=((B.next.vertex v).val:Word w))
    (peers:∀v:B.next.V,∀j,inputMem (((input).ranks.neighbor j).base+(raw v).val)= (DescentPackedColony.target (found (raw v) j):Word w))
    (paidEnd:∀x:DescentColonies.Block k,((fields).paid x.val).base+((fields).paid x.val).size≤(V).actorStart base)
    (actorEnd:∀x:DescentColonies.Block k,((fields).alive x.val).base+((fields).alive x.val).size≤(V).peerStart base)
    (wireEnd:∀(x:DescentColonies.Block k)(j:Fin (2*(A).cap)),((input).signed x.val j.val).base+((input).signed x.val j.val).size ≤ stop₀)
    (cables:∀(x:DescentColonies.Block k)(j:Fin (2*(A).cap)),Reads ((input).signed x.val j.val)
      (fun a t=>DescentSignedCableCodec.encode (Prepare.signed (A) (B.next.order.trans Fin.valEmbedding)
        S B.next.valid (Function.Embedding.refl _) host x j a t)) M inputMem) :
    (DatePorts.reset a floor u).held B.next (a.endAddress floor) actualOut ∧
      ∀x:DescentColonies.Block k,Reads ((output).terminalActor step x.val)
        (Venue.actual B.next.placement (Function.Embedding.refl _) host x) nextM actualOut :=by
  obtain ⟨entry,_⟩:=L.any outer io.hubs _ _ inputStage hubFit atomFit wireFit ingressFits
  obtain ⟨mid,examined,_,_⟩:=u.run_to_operands ready fedMem
  have sample : inputMem=mid:=u.throughOperandDate.nextMemory_eq examined
  obtain ⟨dst,end_,_,_⟩:=PhysicalReset.date_any finish ready fits fedMem
  have event : (DateCode.withPriorArchive pad (PhysicalReset.enterCode L outer u finish io)).Runs previous dst:=padded.then (entry.then end_)
  have done_ : actualOut=dst:=(calendar i).nextMemory_eq (posted.symm ▸ event)
  exact recorded_date_held_planes B record oldRoom room finish cal fits size fitsN found four selfFlag tag
    inputMem oldPos actorPos newPos occupied live rawActor rankEarly invEarly forwardEarly peerEarly
    rankFits peerFits paid actors count inverse order peers paidEnd actorEnd wireEnd cables
    (sample.symm ▸ examined) (done_.symm ▸ end_)

end
end Hierarchy.DescentSixParty.ClosedReset.Window

end OAI
