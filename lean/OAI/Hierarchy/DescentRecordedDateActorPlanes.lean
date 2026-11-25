import OAI.Hierarchy.DescentRecordedVenueDateImage
import OAI.Hierarchy.DescentStageVenueActorPlanes

namespace OAI
/-! # True individual group and block populations in the final reset RAM -/
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

theorem recorded_date_actor_planes
    (cal:venue=V)(fits:finish.Room)(size:N≤(input).ranks.inverse.size)(fitsN:N<2^w)
    (m:Memory w)(actorPos:0<Ma)(newPos:0<M)(occupied:0<H)(live:0<chunks G₁ M)
    (rawActor:(input).actor.base+Q*(H₀*chunks (2^cc) Ma) ≤ stop₀)
    (rankEarly:(input).ranks.count.base<stop₀)(invEarly:(input).ranks.inverse.base+N ≤ stop₀)
    (actors:∀j(p:Row H₀ (2^cc) Ma),m ((input).actor.base+j.val*(H₀*chunks (2^cc) Ma)+(row H₀ (2^cc) Ma p).val)=
        ((data (Recorded.realActor (reset:=B) (shapes B) (rack B oldRoom) j) p).val:Word w))
    (count:m (input).ranks.count.base=(N:Word w))
    (inverse:∀v:B.next.V,m ((input).ranks.inverse.base+(B.next.vertex v).val)=((raw v).val:Word w))
    (actorEnd:∀x:DescentColonies.Block k,((fields).alive x.val).base+((fields).alive x.val).size≤(V).peerStart base):
    ∀x:DescentColonies.Block k,Reads ((((V).next.transported fields ((V).venueStart base)).alive x.val))
      (fun h g=>actualBit B room h g x) nextM (finish.venueImage m):=by
  have safe:(venue).RunRoom input base N w:=ResetVenue.RunRoom.actual venue input base fits.successor N size fitsN
  rw [cal] at safe
  let m₀:=paidRAM m
  let paid:=DescentVenueQuantityPlanes.phase (V).dense ((V).paidLayout input base) w
  let act:=DescentVenueQuantityPlanes.phase (V).actorDims ((V).actorLayout input base) w
  let mp:=paid.image m₀
  let ma:=act.image mp
  let ranker:=DescentCompactVenuePeers.phase (input).ranks ((V).peerStart base) R H w (input).tag
  have early:stop₀ ≤ start:=((output).funded.room stop₀).trans ((V).census.room base)
  have below (address:ℕ)(ha:address<stop₀):mp address=m address:=
    ((DescentVenueQuantityPlanes.any _ _ m₀ safe.paid).2 address (.inl (ha.trans_le early))).trans
      (prior_funding_frame finish m fits address ha)
  have seen:=actor_quantity_source (M₀:=Ma) (M:=M) B oldRoom room ((V).actorLayout input base) mp safe.actors
    actorPos newPos occupied live (fun j p=>by
      have qn:=Nat.mul_le_mul_right (H₀*chunks (2^cc) Ma) j.isLt
      rw [Nat.succ_mul] at qn
      have nrows:=(row H₀ (2^cc) Ma p).isLt
      exact (below ((input).actor.base + j.val * (H₀*chunks (2^cc) Ma) + (row H₀ (2^cc) Ma p).val) (by omega)).trans (actors j p)) ((below _ rankEarly).trans count)
    (fun v=>by rw [dense_physical B oldRoom v]
               exact (below _ ((Nat.add_lt_add_left (B.next.vertex v).isLt _).trans_le invEarly)).trans (inverse v))
  have left:=(DescentCompactVenuePeers.any (input).ranks ((V).peerStart base) R H w (input).tag ma safe.roster safe.peerEnd).2
  have imageEq : finish.venueImage m = ((V).phase input base w).image m₀ :=
    congrArg (fun plan : ResetVenue => (plan.phase input base w).image m₀) cal
  rw [imageEq]
  apply (V).next.phase_actor_plane fields ((V).venueStart base) (ranker.image ma) safe.return_ newPos
  intro x p
  have within:=(row H G₁ M p).isLt.trans_le (safe.return_.alive x).2
  exact (left _ (.inl ((Nat.add_lt_add_left within _).trans_le (actorEnd x)))).trans (seen x p)

end
end Hierarchy.DescentSixParty.ClosedReset.Window

end OAI
