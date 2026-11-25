import OAI.Hierarchy.DescentRecordedVenueDateImage
import OAI.Hierarchy.DescentResetVenuePaidSource

namespace OAI
/-! # The original funded source for reset primitive and metadata reads -/
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
local notation "prepared" mem:arg => (output).funded.memory stop₀ finish.earlier key mem
local notation "paidRAM" mem:arg => DescentFundedCensus.memory finish.jobs base (prepared mem)

theorem recorded_paid_at_venue
    (cal:venue=V)(fits:finish.Room)(size:N≤(input).ranks.inverse.size)(fitsN:N<2^w)
    (m:Memory w)(oldPos:0<M₀)(newPos:0<M)(occupied:0<H)(live:0<chunks G₁ M)
    (rankEarly:(input).ranks.count.base<stop₀)(invEarly:(input).ranks.inverse.base+N≤ stop₀)
    (paid:∀j (p:Row H₀ (2^cc) M₀),(paidRAM m)
      (((venue).original base).base+j.val*(H₀*chunks (2^cc) M₀)+(row H₀ (2^cc) M₀ p).val)=
      ((data (fun u hi=>payable (precision:=precision) B record oldRoom (finProdFinEquiv (u,j)) hi) p).val:Word w))
    (count:m (input).ranks.count.base=(N:Word w))
    (inverse:∀v:B.next.V,m ((input).ranks.inverse.base+(B.next.vertex v).val)=((raw v).val:Word w))
    (paidEnd:∀x:DescentColonies.Block k,((fields).paid x.val).base+((fields).paid x.val).size≤(V).actorStart base):
    ∀x:DescentColonies.Block k,Source (.lookup (((venue).sources input base).paid x.val) .row)
      (fun h g=>Census.count (A) (Equiv.refl _) host precision h g x) M (finish.venueImage m):=by
  have fitRaw:(venue).RunRoom input base N w:=ResetVenue.RunRoom.actual venue input base fits.successor N size fitsN
  rw [cal] at fitRaw
  have keep:=prior_funding_frame finish m fits
  have index (v:B.next.V):(input).ranks.inverse.base+(B.next.vertex v).val<stop₀:=
    (Nat.add_lt_add_left (B.next.vertex v).isLt _).trans_le invEarly
  obtain ⟨done_,ran,read,_⟩:=quantity_source B record oldRoom room ((V).paidLayout input base) (paidRAM m)
    fitRaw.paid oldPos newPos occupied live paid ((keep _ rankEarly).trans count) (fun v=>by
      rw [dense_physical B oldRoom v];exact (keep _ (index v)).trans (inverse v))
  have ident:=ProtocolRAM.exec_unique _ (paidRAM m) done_ _ ran
    (DescentVenueQuantityPlanes.any (V).dense ((V).paidLayout input base) (paidRAM m) fitRaw.paid).1
  let fundedState : Memory w := paidRAM m
  change ∀x:DescentColonies.Block k,Source (.lookup (((venue).sources input base).paid x.val) .row)
    (fun h g=>Census.count (A) (Equiv.refl _) host precision h g x) M (((venue).phase input base w).image fundedState)
  rw [cal]
  apply (V).paid_source_after input base B.next room (paidRAM m) fitRaw rfl paidEnd
  exact ident ▸ read

end
end Hierarchy.DescentSixParty.ClosedReset.Window

end OAI
