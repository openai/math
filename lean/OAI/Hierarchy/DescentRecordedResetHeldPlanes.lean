import OAI.Hierarchy.DescentRecordedResetHeld
import OAI.Hierarchy.DescentRecordedDateActorPlanes
import OAI.Hierarchy.DescentTerminalDatedScanBefore

namespace OAI
/-! # Register and single-block occupancy readback at the same final reset -/
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
variable {a:PhysicalReset}{floor:ℕ}{u:a.DateInputs floor w}(finish:u.FinalInputs)
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

theorem recorded_date_held_planes
    (cal:venue=V)(fits:finish.Room)(size:N ≤ (input).ranks.inverse.size)(fitsN:N<2^w)
    (found:Fin R→Fin 3→Option (Fin R))
    (four:∀v:B.next.V,present (selfPeers found) (raw v)=(insert v ((Z).emittedNear T v)).map raw)
    (selfFlag:∀v:B.next.V,(∀j,found (raw v) j≠some (raw v))↔v∉(Z).emittedNear T v)
    (tag:(input).tag=publicTag ctl.board k height)(m:Memory w)
    (oldPos:0<M₀)(actorPos:0<Ma)(newPos:0<M)(occupied:0<H)(live:0<chunks G₁ M)
    (rawActor:(input).actor.base+Q*(H₀*chunks (2^cc) Ma) ≤ stop₀)
    (rankEarly:(input).ranks.count.base<stop₀)(invEarly:(input).ranks.inverse.base+N ≤ stop₀)
    (forwardEarly:(input).ranks.forward.base+R ≤ stop₀)
    (peerEarly:∀j,((input).ranks.neighbor j).base+R ≤ stop₀)
    (rankFits:R ≤ (input).ranks.forward.size)(peerFits:∀j,R≤((input).ranks.neighbor j).size)
    (paid:∀j (p:Row H₀ (2^cc) M₀),(paidRAM m) (((V).original base).base+j.val*(H₀*chunks (2^cc) M₀)+(row H₀ (2^cc) M₀ p).val)=
      ((data (fun u hi=>payable (precision:=precision) B record oldRoom (finProdFinEquiv (u,j)) hi) p).val:Word w))
    (actors:∀j (p:Row H₀ (2^cc) Ma),m ((input).actor.base+j.val*(H₀*chunks (2^cc) Ma)+(row H₀ (2^cc) Ma p).val)=
      ((data (Recorded.realActor (reset:=B) (shapes B) (rack B oldRoom) j) p).val:Word w))
    (count:m (input).ranks.count.base=(N:Word w))
    (inverse:∀v:B.next.V,m ((input).ranks.inverse.base+(B.next.vertex v).val)=((raw v).val:Word w))
    (order:∀v:B.next.V,m ((input).ranks.forward.base+(raw v).val)=((B.next.vertex v).val:Word w))
    (peers:∀v:B.next.V,∀j,m (((input).ranks.neighbor j).base+(raw v).val)= (DescentPackedColony.target (found (raw v) j):Word w))
    (paidEnd:∀x:DescentColonies.Block k,((fields).paid x.val).base+((fields).paid x.val).size≤(V).actorStart base)
    (actorEnd:∀x:DescentColonies.Block k,((fields).alive x.val).base+((fields).alive x.val).size≤(V).peerStart base)
    (wireEnd:∀(x:DescentColonies.Block k)(j:Fin (2*(A).cap)),((input).signed x.val j.val).base+((input).signed x.val j.val).size ≤ stop₀)
    (cables:∀(x:DescentColonies.Block k)(j:Fin (2*(A).cap)),Reads ((input).signed x.val j.val)
      (fun a t=>DescentSignedCableCodec.encode (Prepare.signed (A) (B.next.order.trans Fin.valEmbedding)
        S B.next.valid (Function.Embedding.refl _) host x j a t)) M m)
    {seed out : Memory w} (toOperands : u.throughOperandDate.Runs seed m)
    (toEnd : (PhysicalReset.date finish).Runs seed out) :
    (DatePorts.reset a floor u).held B.next (a.endAddress floor) out ∧
    ∀x:DescentColonies.Block k,Reads ((output).terminalActor step x.val)
      (Venue.actual B.next.placement (Function.Embedding.refl _) host x) nextM out := by
  refine ⟨recorded_date_held B record oldRoom room finish cal fits size fitsN found four selfFlag tag m
    oldPos actorPos newPos occupied live rawActor rankEarly invEarly forwardEarly peerEarly rankFits peerFits
    paid actors count inverse order peers paidEnd actorEnd wireEnd cables toOperands toEnd,?_⟩
  have kept:=PhysicalReset.date_venue_below finish fits toOperands toEnd
  have original:=recorded_date_actor_planes B oldRoom room finish cal fits size fitsN m actorPos newPos
    occupied live rawActor rankEarly invEarly actors count inverse actorEnd
  have nk:(venue).next.k=k:=by rw [cal]; rfl
  have nh:(venue).next.hosts=H:=by rw [cal]; rfl
  have ng:(venue).next.groups=G₁:=by rw [cal]; rfl
  have nl:(venue).next.lanes=nextM:=by rw [cal]; rfl
  intro x pos
  have dim:=(output).terminal_actor_room step fits.successor.return_.roof
    (x.cast (congrArg (2^·) nk).symm)
  have within:(row H G₁ nextM pos).val<((output).terminalActor step x.val).size:=by
    apply (row H G₁ nextM pos).isLt.trans_le
    simpa only [nh,ng,nl,Fin.val_cast] using dim.2
  have page : (((V).next.transported fields ((V).venueStart base)).alive x.val) =
      (output).terminalActor step x.val :=by
    exact (congrArg (fun v:ResetVenue=>
      (v.next.transported (v.sources input base) (v.venueStart base)).alive x.val) cal).symm
  have recorded:=original x pos
  rw [page] at recorded
  exact (kept _ ((Nat.add_lt_add_left within _).trans_le dim.1)).trans recorded

end
end Hierarchy.DescentSixParty.ClosedReset.Window

end OAI
