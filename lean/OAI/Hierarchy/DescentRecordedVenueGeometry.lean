import OAI.Hierarchy.DescentDatedVenueReturn
import OAI.Hierarchy.DescentResetVenueRoster
import OAI.Hierarchy.DescentResetVenueActorRead
import OAI.Hierarchy.DescentResetVenueSigned

namespace OAI
/-! # A recorded reset's original sparse census, actor occupancy and three physical neighbors -/
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
variable (shape:DescentFundedCensus.Shape)
def calibrated (oldH newH oldM actorM rawM nextM precision:ℕ):ResetVenue:=
  ⟨shape,quantityDims B precision oldH newH oldM rawM,⟨k,newH,G₁,3,(A).cap,precision,rawM,rawM,rawM,nextM⟩,actorM⟩
local notation "V" => calibrated B shape H₀ H M₀ Ma M nextM precision
variable (input:ResetVenue.Earlier)(base:ℕ)
local notation "fields" => (V).sources input base
local notation "Φ" => DescentVenueQuantityPlanes.phase (V).dense ((V).paidLayout input base) w
local notation "α" => DescentVenueQuantityPlanes.phase (V).actorDims ((V).actorLayout input base) w
local notation "π" => DescentCompactVenuePeers.phase input.ranks ((V).peerStart base) R H w input.tag
local notation "start" => (V).denseStart base

theorem recorded_venue
    (found:Fin R→Fin 3→Option (Fin R))
    (four:∀v:B.next.V,present (selfPeers found) (raw v)=(insert v ((Z).emittedNear T v)).map raw)
    (selfFlag:∀v:B.next.V,(∀j,found (raw v) j≠some (raw v))↔v∉(Z).emittedNear T v)
    (tag:input.tag=publicTag ctl.board k height)(m:Memory w)(fit:(V).RunRoom input base N w)
    (oldPos:0<M₀)(actorPos:0<Ma)(newPos:0<M)(occupied:0<H)(live:0<chunks G₁ M)
    (rawActor:input.actor.base+Q*(H₀*chunks (2^cc) Ma) ≤ start)
    (rankEarly:input.ranks.count.base<start)(invEarly:input.ranks.inverse.base+N ≤ start)
    (forwardEarly:input.ranks.forward.base+R ≤ start)
    (peerEarly:∀j,(input.ranks.neighbor j).base+R ≤ start)
    (rankFits:R ≤ input.ranks.forward.size)(peerFits:∀j,R≤(input.ranks.neighbor j).size)
    (paid:∀j (p:Row H₀ (2^cc) M₀),m (((V).original base).base+j.val*(H₀*chunks (2^cc) M₀)+(row H₀ (2^cc) M₀ p).val)=
      ((data (fun u hi=>payable (precision:=precision) B record oldRoom (finProdFinEquiv (u,j)) hi) p).val:Word w))
    (actors:∀j (p:Row H₀ (2^cc) Ma),m (input.actor.base+j.val*(H₀*chunks (2^cc) Ma)+(row H₀ (2^cc) Ma p).val)=
      ((data (Recorded.realActor (reset:=B) (shapes B) (rack B oldRoom) j) p).val:Word w))
    (count:m input.ranks.count.base=(N:Word w))
    (inverse:∀v:B.next.V,m (input.ranks.inverse.base+(B.next.vertex v).val)=((raw v).val:Word w))
    (order:∀v:B.next.V,m (input.ranks.forward.base+(raw v).val)=((B.next.vertex v).val:Word w))
    (peers:∀v:B.next.V,∀j,m ((input.ranks.neighbor j).base+(raw v).val)= (DescentPackedColony.target (found (raw v) j):Word w))
    (paidEnd:∀x:DescentColonies.Block k,((fields).paid x.val).base+((fields).paid x.val).size≤(V).actorStart base)
    (actorEnd:∀x:DescentColonies.Block k,((fields).alive x.val).base+((fields).alive x.val).size≤(V).peerStart base)
    (wireEnd:∀(x:DescentColonies.Block k)(j:Fin (2*(A).cap)),(input.signed x.val j.val).base+(input.signed x.val j.val).size ≤ start)
    (cables:∀(x:DescentColonies.Block k)(j:Fin (2*(A).cap)),Reads (input.signed x.val j.val)
      (fun a t=>DescentSignedCableCodec.encode (Prepare.signed (A) (B.next.order.trans Fin.valEmbedding)
        S B.next.valid (Function.Embedding.refl _) host x j a t)) M m):
    stageVenue B.next room ((V).next.operands fields ((V).venueStart base)) nextM precision
      ((V).endAddress base) (B.next.venueRoster room) (((V).phase input base w).image m):=by
  let pm:=(Φ).image m
  let am:=(α).image pm
  have ps:=((V).steps base).1
  have keepP (j:ℕ)(low:j<start):pm j=m j:=(DescentVenueQuantityPlanes.any _ _ m fit.paid).2 j (.inl low)
  have keep (j:ℕ)(low:j<start):am j=m j:=
    ((DescentVenueQuantityPlanes.any _ _ pm fit.actors).2 j (.inl (low.trans_le ps))).trans (keepP j low)
  have invRoom (u:B.next.V):input.ranks.inverse.base+(B.next.vertex u).val<start:=
    (Nat.add_lt_add_left (B.next.vertex u).isLt _).trans_le invEarly
  have numeric (u:B.next.V):((Z).denseHostRank T rank u).val=(B.next.vertex u).val:=
    dense_physical B oldRoom u
  obtain ⟨out,path,read,_⟩:=quantity_source B record oldRoom room ((V).paidLayout input base) m fit.paid
    oldPos newPos occupied live paid count (fun v=>by rw [numeric];apply inverse)
  have same:out=pm:=ProtocolRAM.exec_unique _ m _ _ path (DescentVenueQuantityPlanes.any _ _ m fit.paid).1
  subst out
  have seen:=actor_quantity_source (M₀:=Ma) (M:=M) B oldRoom room ((V).actorLayout input base) pm fit.actors
    actorPos newPos occupied live (fun j p=>by
      have qn:=Nat.mul_le_mul_right (H₀*chunks (2^cc) Ma) j.isLt
      rw [Nat.succ_mul] at qn
      have v:=(row H₀ (2^cc) Ma p).isLt
      have low : input.actor.base + j.val * (H₀ * chunks (2^cc) Ma) +
          (row H₀ (2^cc) Ma p).val < start := by omega
      exact (keepP _ low).trans (actors j p)) ((keepP _ rankEarly).trans count)
    (fun v=>by rw [numeric];exact (keepP _ (invRoom v)).trans (inverse v))
  let dir:=rosterDirectory B oldRoom room found four selfFlag
  have stored:dir.Stored input.ranks am:=resident_directory B oldRoom room found four selfFlag input.ranks am fit.roster
    fit.paid.inverseSize rankFits peerFits ((keep _ rankEarly).trans count)
    (fun u=>(keep _ (invRoom u)).trans (inverse u))
    (fun u=>(keep _ ((Nat.add_lt_add_left (raw u).isLt _).trans_le forwardEarly)).trans (order u))
    (fun u j=>(keep _ ((Nat.add_lt_add_left (raw u).isLt _).trans_le (peerEarly j))).trans (peers u j))
  apply (V).returned input base B.next room m fit rfl rfl newPos newPos newPos paidEnd actorEnd wireEnd
  · exact read
  · exact seen
  · intro u j
    have yes:=(dir.sorted input.ranks ((V).peerStart base) input.tag am fit.roster stored fit.peerEnd u j).1
    rwa [reset_peer B oldRoom room found four selfFlag record u j] at yes
  · intro u
    have yes:=(dir.sorted input.ranks ((V).peerStart base) input.tag am fit.roster stored fit.peerEnd u 0).2
    apply yes.trans
    apply congrArg (fun n : ℕ => (n : Word w))
    rw [tag]
    exact reset_hub B oldRoom room found four selfFlag u
  · exact cables

end
end Hierarchy.DescentSixParty.ClosedReset.Window

end OAI
