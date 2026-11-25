import OAI.Hierarchy.DescentNamedRecordedVenue
import OAI.Hierarchy.DescentPhysicalResetDateVenue

namespace OAI
/-! # Original issued reset fields at the actual selected final stage -/
namespace Hierarchy.DescentSixParty.ClosedReset.Window
open DescentCompiler DescentDenseHostOrder DescentSIMDLookup DescentActorRaster DescentPackedZip
open DescentPaidResidentCount DescentPacking.PackedMatch.Local.Stage DescentPackedColony DescentColonies
open DescentDatedAddressBook DescentCompactVenuePeers DescentResetPeerUnionRAM DescentSortedRoster
open DescentResetHostSize DescentStageEdgeReceipt DescentPackedExchange DescentHubBits DescentSixParty.Chronology
open Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM
open scoped Classical Fin.CommRing
noncomputable section
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

/-- The two funding passes preserve the physical actor, peer and signed shelves issued
by the earlier root/operand phases. -/
theorem prior_funding_frame (m:Memory w)(fits:finish.Room)(x:ℕ)(hx:x<stop₀):
    (paidRAM m) x=m x:=by
  have first_:=((output).funded.any stop₀ finish.earlier key m fits.earlier fits.saved fits.fund).2.2
  have second_:=(DescentFundedCensus.any finish.jobs fits.jobs (prepared m)).2.2
  have bound:stop₀≤base:=(output).funded.room stop₀
  exact (second_ x (.inl (hx.trans_le bound))).trans (first_ x (.inl hx))

/-- The incoming memory here is the actual completed operand phase. Only the paid
columns are received from the later funding pass; every other datum is taken at the
original checkpoint before funding. -/
theorem recorded_date_image
    (cal:venue=V)(fits:finish.Room)(size:N≤(input).ranks.inverse.size)(fitsN:N<2^w)
    (found:Fin R→Fin 3→Option (Fin R))
    (four:∀v:B.next.V,present (selfPeers found) (raw v)=(insert v ((Z).emittedNear T v)).map raw)
    (selfFlag:∀v:B.next.V,(∀j,found (raw v) j≠some (raw v))↔v∉(Z).emittedNear T v)
    (tag:(input).tag=publicTag ctl.board k height)(m:Memory w)
    (oldPos:0<M₀)(actorPos:0<Ma)(newPos:0<M)(occupied:0<H)(live:0<chunks G₁ M)
    (rawActor:(input).actor.base+Q*(H₀*chunks (2^cc) Ma) ≤ stop₀)
    (rankEarly:(input).ranks.count.base<stop₀)(invEarly:(input).ranks.inverse.base+N ≤ stop₀)
    (forwardEarly:(input).ranks.forward.base+R ≤ stop₀)
    (peerEarly:∀j,((input).ranks.neighbor j).base+R ≤ stop₀)
    (rankFits:R≤(input).ranks.forward.size)(peerFits:∀j,R≤((input).ranks.neighbor j).size)
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
        S B.next.valid (Function.Embedding.refl _) host x j a t)) M m):
    stageVenue B.next room ((venue).next.operands ((venue).sources input base) ((venue).venueStart base))
      nextM precision ((venue).endAddress base) (B.next.venueRoster room) (finish.venueImage m):=by
  have fitRaw:(venue).RunRoom input base N w:=ResetVenue.RunRoom.actual venue input base fits.successor N size fitsN
  rw [cal] at fitRaw
  have prior:stop₀ ≤ start:=((output).funded.room stop₀).trans ((V).census.room base)
  have keep (x hx):=(prior_funding_frame finish m fits x hx)
  have seen (j:Fin Q)(p:Row H₀ (2^cc) Ma):
      (paidRAM m) ((input).actor.base+j.val*(H₀*chunks (2^cc) Ma)+(row H₀ (2^cc) Ma p).val)=
        ((data (Recorded.realActor (reset:=B) (shapes B) (rack B oldRoom) j) p).val:Word w):=by
    have qn:=Nat.mul_le_mul_right (H₀*chunks (2^cc) Ma) j.isLt
    rw [Nat.succ_mul] at qn
    have index:=(row H₀ (2^cc) Ma p).isLt
    exact (keep _ (by omega)).trans (actors j p)
  have copied (x:DescentColonies.Block k)(j:Fin (2*(A).cap)):
      Reads ((input).signed x.val j.val) (fun a t=>DescentSignedCableCodec.encode
        (Prepare.signed (A) (B.next.order.trans Fin.valEmbedding) S B.next.valid
          (Function.Embedding.refl _) host x j a t)) M (paidRAM m):=by
    intro rowId
    have depth_:=(fitRaw.return_.signed x j).2
    have pos:=(row H G₁ M rowId).isLt.trans_le depth_
    exact (keep _ ((Nat.add_lt_add_left pos _).trans_le (wireEnd x j))).trans (cables x j rowId)
  let fundedState : Memory w := paidRAM m
  change stageVenue B.next room ((venue).next.operands ((venue).sources input base) ((venue).venueStart base))
    nextM precision ((venue).endAddress base) (B.next.venueRoster room)
    (((venue).phase input base w).image fundedState)
  rw [cal]
  apply recorded_venue B record oldRoom room _ input base found four selfFlag tag (paidRAM m) fitRaw
    oldPos actorPos newPos occupied live (rawActor.trans prior) (rankEarly.trans_le prior)
    (invEarly.trans prior) (forwardEarly.trans prior) (fun j=>(peerEarly j).trans prior)
    rankFits peerFits paid seen ((keep _ rankEarly).trans count)
    (fun v=>(keep _ ((Nat.add_lt_add_left (B.next.vertex v).isLt _).trans_le invEarly)).trans (inverse v))
    (fun v=>(keep _ ((Nat.add_lt_add_left (raw v).isLt _).trans_le forwardEarly)).trans (order v))
    (fun v j=>(keep _ ((Nat.add_lt_add_left (raw v).isLt _).trans_le (peerEarly j))).trans (peers v j))
    paidEnd actorEnd (fun x j=>(wireEnd x j).trans prior) copied

end
end Hierarchy.DescentSixParty.ClosedReset.Window

end OAI
