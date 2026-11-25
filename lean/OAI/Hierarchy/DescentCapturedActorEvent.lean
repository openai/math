import OAI.Hierarchy.DescentPostedActorEvent
import OAI.Hierarchy.DescentPostedPaidActors
import OAI.Hierarchy.DescentPostedPeerRows
import OAI.Hierarchy.DescentPostedSignedRows

namespace OAI
/-! # A captured neighbor roster and reached ranked windows issue the next physical venue -/
namespace Hierarchy.DescentSixParty.ClosedReset.Window
open DescentCompiler DescentDenseHostOrder DescentSIMDLookup DescentActorRaster DescentPackedZip
open DescentPaidResidentCount DescentPacking.PackedMatch.Local.Stage DescentPackedColony DescentColonies
open DescentDatedAddressBook DescentCompactVenuePeers DescentResetPeerUnionRAM DescentSortedRoster
open DescentSharedCableNames DescentResetLocalRoster DescentResetFieldAssembler DescentResetCandidatePair
open DescentResetRankedWindows
open DescentResetHostSize DescentStageEdgeReceipt DescentPackedExchange DescentHubBits DescentSixParty.Chronology
open Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false
variable {F P:Type} [Field F] [Fintype P] {d:ℕ} {bits:P→ℕ} {W:MarkedWorld F d P bits} {G:PoweredGadget F}
  {q ε:ℝ} {S:AtomSchedule} {k i z D n h C f g cut tail wire hist:ℕ} {ctl:ResetRates G S k D n h C f g cut tail}
  {old:Reached W G q ε S k i z D wire hist} (B:ClosedReset old ctl)
  {quant H₀ M₀ Ma M nextM precision w:ℕ}(record:B.Recorded quant)
  (oldRoom:Fintype.card old.V≤H₀)
local notation "H" => S.hostSize (i+1)
local notation "room" => B.next.valid.host
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
variable {u:a.DateInputs (L.endAddress outer) w} (finish:u.FinalInputs) (io:DescentPacking.PackedMatch.Local.Stage.Dated.Operands)
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
local notation "venue₀" => calibrated B (venue).census H₀ H M₀ Ma M nextM precision
local notation "fields" => (venue₀).sources input base
local notation "start" => (venue₀).denseStart base
local notation "prepared" mem:arg => (output).funded.memory stop₀ finish.earlier key mem
local notation "paidRAM" mem:arg => DescentFundedCensus.memory finish.jobs base (prepared mem)

variable {I U : MarkedWorld F d P bits} {z₀ D₀ len zl Dl : ℕ}
    {first : Reached I G q ε S k 0 z₀ D₀ wire hist} {last : Reached U G q ε S k len zl Dl wire hist}
    {path : Path first last} (before : Path first old) (after_ : Path B.next last)
    (cutAt : (before.reset B).append after_=path)
local notation "event_" => (Path.Event.reset before B after_ cutAt : path.Event i)


local notation "rec_" => (output).receiver
local notation "pop_" => (output).front.peer.hosts
local notation "st_" => (output).sheetsStart step
local notation "sh_" => u.sectors
local notation "h_" => sheetHeader B st_ (sh_).pageBits
local notation "key_" => sheetOriginal B st_ (sh_).pageBits
local notation "sp_" => (output).rankPorts step
local notation "rank_mem" ok:arg m:arg => ((output).rankPortPhase step w).image (u.candidateEntry ok m)
def renumberPeer {U V : ℕ} (width : U=V) (f : Fin U→Fin 3→Option (Fin U))
    (v : Fin V) (j : Fin 3) : Option (Fin V) := (f (v.cast width.symm) j).map (Fin.cast width)
theorem renumber_observed {U V : ℕ} (width : U=V) (f : Fin U→Fin 3→Option (Fin U))
    (g : Fin V→Fin 3→Option (Fin V))
    (read : ∀h j,f h j=(g (h.cast width) j).map (Fin.cast width.symm)) : renumberPeer width f=g:=by
  subst V
  funext v j
  simp [renumberPeer,read]

private theorem renumber_value {U V : ℕ} (eqn : U=V) (f : Fin U→Fin 3→Option (Fin U)) (v : Fin V) (j : Fin 3) :
    DescentPackedColony.target (renumberPeer eqn f v j)=DescentPackedColony.target (f (v.cast eqn.symm) j):=by
  subst V
  simp [renumberPeer]
omit [Fintype P] in
private theorem canonical_cables {blocks rooms groups width capacity : ℕ} (shape : blocks=2^k)
    (space : rooms=H) (gg : groups=G₁) (cap : capacity=(A).cap) (pitch : width=M)
    (bank : ℕ→ℕ→Bank) (m : Memory w)
    (got : ∀(x : Fin blocks)(j : Fin (2*capacity)),DescentPackedColony.Reads (bank x.val j.val)
      (fun h g=>DescentSignedCableCodec.encode (Prepare.signed (A) (B.next.order.trans Fin.valEmbedding)
        S B.next.valid (Function.Embedding.refl _) (B.next.vertex.trans (Fin.castLEEmb ((room).trans_eq space.symm)))
        (x.cast shape) (j.cast (congrArg (2*·) cap)) h (Fin.cast gg g))) width m) :
    ∀(x : DescentColonies.Block k)(j : Fin (2*(A).cap)),DescentPackedColony.Reads (bank x.val j.val)
      (fun h g=>DescentSignedCableCodec.encode (Prepare.signed (A) (B.next.order.trans Fin.valEmbedding)
        S B.next.valid (Function.Embedding.refl _) host x j h g)) M m:=by
  subst blocks;subst rooms;subst groups;subst width;subst capacity;exact got

omit [Fintype P] in
theorem captured_actor_event
    (posted : calendar i=DateCode.withPriorArchive pad (PhysicalReset.enterCode L outer u finish io))
    (padded : pad.Runs previous)
    (ready:u.Ready) (hubFit:io.hubs.Fits w outer)
    (atomFit:∀x:Fin (2^L.k),(io.atoms x.val).Fits w outer)
    (wireFit:∀j:L.signed.Slot,(io.wire j.1.val j.2.val).Fits w outer)
    (ingressFits:L.endAddress outer<2^w)
    (cal:venue=venue₀)(fits:finish.Room)(size:N ≤ (input).ranks.inverse.size)(fitsN:N<2^w)
    (actorMem : Memory w) (cutState : u.throughOperandDate.Runs fedMem (u.sheetsResult ready actorMem))
    {oldHosts : ℕ} (captured : u.MeasuredChannels oldHosts) (seen : PhysicalReset.DateInputs.CaptureRoom captured actorMem)
    (rawSize : pop_=R)
    (four : ∀v:B.next.V,present (selfPeers (renumberPeer rawSize captured.near)) (raw v)=
      (insert v ((Z).emittedNear T v)).map raw)
    (rawNear : ∀v:B.next.V,present (renumberPeer rawSize captured.near) (raw v)=((Z).emittedNear T v).map raw)
    (tag:(input).tag=publicTag ctl.board k height)
    (oldPos:0<M₀)(actorPos:0<Ma)(newPos:0<M)(occupied:0<H)(live:0<chunks G₁ M)
    (rawActor:(input).actor.base+Q*(H₀*chunks (2^cc) Ma) ≤ stop₀)
    (rankEarly:(input).ranks.count.base<stop₀)(invEarly:(input).ranks.inverse.base+N ≤ stop₀)
    (forwardEarly:(input).ranks.forward.base+R ≤ stop₀)
    (peerEarly:∀j,((input).ranks.neighbor j).base+R ≤ stop₀)
    (rankFits:R ≤ (input).ranks.forward.size)(peerFits:∀j,R≤((input).ranks.neighbor j).size)
    (funded : (∀j (p:Row H₀ (2^cc) M₀),(paidRAM inputMem) (((venue₀).original base).base+j.val*(H₀*chunks (2^cc) M₀)+(row H₀ (2^cc) M₀ p).val)=
      ((data (fun u hi=>payable («precision»:=precision) B record oldRoom (finProdFinEquiv (u,j)) hi) p).val:Word w)) ∧
      (∀j (p:Row H₀ (2^cc) Ma),inputMem ((input).actor.base+j.val*(H₀*chunks (2^cc) Ma)+(row H₀ (2^cc) Ma p).val)=
      ((data (Recorded.realActor (reset:=B) (shapes B) (rack B oldRoom) j) p).val:Word w)) ∧
      (inputMem (input).ranks.count.base=(N:Word w)) ∧
      (∀v:B.next.V,inputMem ((input).ranks.inverse.base+(B.next.vertex v).val)=((raw v).val:Word w)) ∧
      (∀v:B.next.V,inputMem ((input).ranks.forward.base+(raw v).val)=((B.next.vertex v).val:Word w)))
    (paidEnd:∀x:DescentColonies.Block k,((fields).paid x.val).base+((fields).paid x.val).size≤(venue₀).actorStart base)
    (actorEnd:∀x:DescentColonies.Block k,((fields).alive x.val).base+((fields).alive x.val).size≤(venue₀).peerStart base)
    (wireEnd:∀(x:DescentColonies.Block k)(j:Fin (2*(A).cap)),((input).signed x.val j.val).base+((input).signed x.val j.val).size ≤ stop₀)
    (hx : (rec_).blocks=2^k) (hj : (rec_).candidates=totalLocal B) (gg : (rec_).groups=G₁)
    (hhost : (rec_).hosts=H) (pitch : (rec_).lanes=M) (cap : (rec_).capacity=(A).cap)
    (degree : u.degree=(A).degree)
    (digits : max ((A).degree+1) ((A).cap+1)<2^(output).assemblerBits)
    (prior : (sh_).before=publicBefore D k n height (S.groupWidth k tail i) old.placement.cap (programCount ctl.board height))
    (slot : ∀j,(sh_).sourceSlot j=publicSourceSlot D k n height old.placement.cap
      (programCount ctl.board height) (rec_).candidates j.val)
    (earned : RankSources B (b:=(output).assemblerBits) (t:=(output).ticketBits) (M:=(rec_).lanes)
      (rackOf B (B.next.vertex.trans (Fin.castLEEmb ((room).trans_eq hhost.symm)))) sp_ h_ key_ (rank_mem ready actorMem)) :
    (DatePorts.reset a floor u).held B.next (a.endAddress floor) actualOut ∧
      (nextM=S.groupCount (i+1) → (event_).actorPlanes (fun x=>(output).terminalActor step x.val) actualOut) :=by
  let found:=renumberPeer rawSize captured.near
  have chosen : inputMem=u.sheetsResult ready actorMem:=u.throughOperandDate.nextMemory_eq cutState
  have peers (v:B.next.V) (j:Fin 3) :
      inputMem (((input).ranks.neighbor j).base+(raw v).val)=(DescentPackedColony.target (found (raw v) j):Word w):=by
    rw [chosen,renumber_value]
    exact u.captured_operand_peer ready captured actorMem seen ((raw v).cast rawSize.symm) j
  have issued:=posted_operand_signed B u hx hj gg prior slot ((room).trans_eq hhost.symm) ready actorMem earned cap degree digits
  have cables:=canonical_cables B hx hhost gg cap pitch (input).signed (u.sheetsResult ready actorMem) issued
  obtain ⟨paid,actors,count,inverse,order⟩:=funded
  exact posted_actor_event B record oldRoom L outer finish io pad calendar initial before after_ cutAt
    posted padded ready hubFit atomFit wireFit ingressFits cal fits size fitsN found four
    (emitted_self_flag raw found ((Z).emittedNear T) rawNear) tag oldPos actorPos newPos occupied live rawActor
    rankEarly invEarly forwardEarly peerEarly rankFits peerFits paid actors count inverse order peers
    paidEnd actorEnd wireEnd (chosen.symm ▸ cables)

end
end Hierarchy.DescentSixParty.ClosedReset.Window

end OAI
