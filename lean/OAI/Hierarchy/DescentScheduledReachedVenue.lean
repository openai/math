import OAI.Hierarchy.DescentReachedPostedActorPlanes
import OAI.Hierarchy.DescentRegisteredSelectedReady
import OAI.Hierarchy.DescentScheduledEstimatorWords
import OAI.Hierarchy.DescentRecordedCensusMass
import OAI.Hierarchy.DescentResetActorWordCalibration

namespace OAI
/-! # The selected reset returns every original venue register after the two prior-archive passes -/
namespace Hierarchy.DescentDatedAddressBook.PhysicalReset
open DescentSixParty DescentCompiler DescentPacking.PackedMatch.Local.Stage DescentPackedWalsh
open DescentSIMDLookup DescentGL DescentResetGates DescentFundedCensus DescentColonies DescentSixParty.Chronology
open DescentSixParty.ClosedReset.Window ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.Routing
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false
set_option hygiene false
variable {F X : Type} [Field F] [Fintype X] {d : ℕ} {bits : X→ℕ}
  {W W₀ W₁ : MarkedWorld F d X bits} {G : PoweredGadget F} {q ε : ℝ} {S : AtomSchedule}
  {k age z wire hist D n h C f g cut tail p : ℕ} {input : Reached W G q ε S k age z D wire hist}
  {ctl : ResetRates G S k D n h C f g cut tail} (B : ClosedReset input ctl)
  {z₀ D₀ len zl Dl : ℕ} {first : Reached W₀ G q ε S k 0 z₀ D₀ wire hist}
  {last : Reached W₁ G q ε S k len zl Dl wire hist} {path : Path first last}
  (before : Path first input) (after_ : Path B.next last) (joined : (before.reset B).append after_=path)
  (accepted : B.Recorded p)
local notation "evt" => (Path.Event.reset before B after_ joined : path.Event age)
variable (drift degree payload : ℕ) (ord : ℕ→Dated.Ordinary) (s Z : ℕ)
    (ports : DatePorts) (floor w : ℕ)
local notation "op" => RotorSpec.ofRates ctl
local notation "cap" => ((capCalendar G.b S.rounds g S.height).take age).prod*256
local notation "oldExp" => NativePitch.resetCut S k tail p f payload age
local notation "nextM" => NativePitch.incoming S k tail p f payload ord (age+1)
local notation "token" => DescentPrimitivePalette.printedBits G s Z op
local notation "old" => ports.venue
local notation "io" => ports.io
local notation "pitch" => receiverCut G S ctl.board k tail age p f g drift degree payload oldExp nextM C ctl.bitsR
  ports.operandLanes ports.roleLanes token old
local notation "M" => 2^pitch
local notation "at₁" => scheduledAtPorts G S ctl.board k tail age p f g drift degree payload ord op s Z ports floor
local notation "a" => (at₁).inner
local notation "floor₁" => ports.priorStart k floor
local notation "prev" => (ports.afterPad k floor).archive
local notation "start" => (a).stageStart floor₁
local notation "out" => (a).successor
local notation "span" => S.groupWidth k tail age+k
local notation "precision" => S.localWalshBits p span f (quota S.rounds)
local notation "priorFit" => preceding_cut S k tail p f payload age
local notation "selectFit" => scheduled_cut_origin G S ctl.board k tail age p f g drift degree payload ord op s Z
  ports.operandLanes ports.roleLanes old
local notation "pad" => priorArchivePhase G S ctl.board k tail age p f g drift degree payload ord op s Z ports floor w
local notation "tape" => ScheduledCodeRoom G S ctl.board k tail age p f g drift degree payload ord op s Z
  ports.operandLanes ports.roleLanes old io floor₁ w prev
variable (capacity : (old).cap=cap) (space : tape)
local notation "u" => DatePorts.resetInputs G S ctl.board k tail age p f g drift degree payload ord op s Z ports floor w space
local notation "done" => FinalInputs.fromArchive G S ctl.board k tail age p f g drift degree payload pitch oldExp M
  nextM C ctl.bitsR ports.operandLanes ports.roleLanes token old io floor₁ w selectFit selectFit priorFit
  (prev).count space.prepared space.scene prev s Z op capacity
local notation "move" => DatePorts.resetDate G S ctl.board k tail age p f g drift degree payload ord op s Z ports floor w capacity space
local notation "regs" => DatePorts.resetPorts G S ctl.board k tail age p f g drift degree payload ord op s Z ports floor w space
variable (calendar : ℕ→DateCode w) (boot : Memory w)
local notation "mem" => DateCode.history calendar boot age
local notation "padded" => (pad).image mem

include accepted in
set_option maxHeartbeats 850000 in
omit [Fintype X] in
theorem DateInputs.scheduled_reached_venue
    (ready : (u).Ready ∧ (done).Room) (gr : z=S.grainAt G.b p (age+1))
    (fee : wire=S.epochPower^S.priceExponent) (history : hist=S.firstWidth G.b p)
    (branch : G.b≤2^S.capGain) (positive : 0<p) (elapsed : 0<age) (sorted : SourceSorted W input.order)
    (degreeAt : (old).degree=D) (capAt : (old).cap=input.placement.cap)
    (homes : (old).hosts=S.hostSize age) (clusters : (old).groups=S.groupCount age)
    (blocks : (old).k=k) (width : (old).paidBits=S.censusBits p) (batch : (old).lanes=2^oldExp)
    (headroom : ports.HeaderRoom w floor) (wireRoom : ports.WireRoom w floor) (paid : ports.PaidRoom w floor)
    (seen : stageVenue input input.valid.host io (old).lanes (old).paidBits floor₁ (input.venueRoster input.valid.host) padded)
    (count : padded ports.archive.count.base=(Fintype.card input.V:Word w))
    (sites : 0<S.initialSites) (word : payload≤w) (small : 8*(out).groupWidth≤payload) (ceiling : (at₁).fullEnd<2^w)
    (walsh : k≤laneBits span payload precision)
    (estimator : ResetEstimatorWords (S.hostSize age) span precision (S.censusBits p) (old).degree w)
    (amounts : ResetActorWords h D n k f g w) (lanes : M≤w)
    (posted : calendar age=move) (entered : (pad).Runs mem) :
    (regs).held B.next ((a).endAddress start) (DateCode.history calendar boot (age+1)) ∧
    (nextM=S.groupCount (age+1)→(evt).actorPlanes (fun x=>(out).terminalActor ((a).rebased start) x.val)
      (DateCode.history calendar boot (age+1))) :=by
  have cap₀:=capAt.symm.trans capacity
  have ⟨score,head,host⟩:=scheduled_estimator_words G S ctl.board k tail age p f g drift degree payload ord op
    s Z ports floor w estimator
  have ⟨live,stock,arrival⟩:=posted_census_limits B p positive gr fee branch cap₀
  have later:= (at₁).stages.1
  have hr:=headroom.mono later
  have wr:=wireRoom.mono later
  have pr:=paid.mono later
  have oldPos : 0<(old).lanes:=batch.symm ▸ Nat.two_pow_pos _
  have firstRoom : start<2^w:=((a).occupied start).1.trans_lt (((a).occupied start).2.1.trans_lt
    (((a).occupied start).2.2.trans_lt ceiling))
  have wires (x : Block k) (j : Fin (2*input.placement.cap)) :=
    wr (x.cast (congrArg (2^·) blocks).symm) (j.cast (congrArg (2*·) capAt).symm)
  have addresses (j:(a).ingress.signed.Slot) : ((io).wire j.1.val j.2.val).Fits w floor₁:=by
    apply (wr (j.1.cast (congrArg (2^·) blocks).symm) (j.2.cast (congrArg (2*·) capacity).symm)).1
  have issued : IssuedBanks io (old).hosts (S.groupCount age) (old).lanes :=
    clusters ▸ pr.issued
  have census := named_operand_geometry B p drift degree payload pitch oldExp M nextM ctl.bitsR
    (ResetOutput.Prior.atDate G S age p drift ports.operandLanes ports.roleLanes token old) ((a).rebased start)
    degreeAt blocks homes cap₀ (Nat.two_pow_pos _)
  obtain ⟨_,_,_,_,_,_,peerExtent,_,_⟩:=census
  have hostPos : 0<S.hostSize (age+1):=by
    rw [AtomSchedule.hostSize,ctl.radix]
    positivity
  have groupPos : 0<S.groupCount (age+1):=by
    rw [AtomSchedule.groupCount,ctl.base,ctl.radix]
    positivity
  have chunkPos : 0<chunks (S.groupCount (age+1)) M:=by
    apply Nat.div_pos _ (Nat.two_pow_pos _)
    omega
  exact DateInputs.fromNamed_venue_and_last_actors accepted drift degree payload pitch oldExp M nextM
    ports.operandLanes ports.roleLanes token old io floor₁ w selectFit selectFit priorFit (prev).count
    (prev).nodeBase (prev).arguments (prev).seed space.prepared space.scene done pad calendar boot
    before after_ joined degreeAt ready.1 gr fee cap₀ history branch seen hr.count count
    (fun x j => by
      change ((io).wire x.val j.val).Fits w floor₁ ∧
        S.hostSize age * chunks (S.groupCount age) (old).lanes ≤ ((io).wire x.val j.val).size
      have wireFit := wires x j
      change ((io).wire x.val j.val).Fits w floor₁ ∧
        (old).hosts * chunks (old).groups (old).lanes ≤ ((io).wire x.val j.val).size at wireFit
      simpa only [homes,clusters] using wireFit) oldPos width firstRoom walsh score live
    (degreeAt.symm ▸ amounts.degree) head host (degreeAt.symm ▸ amounts.ranks) (degreeAt.symm ▸ amounts.actor)
    (degreeAt.symm ▸ amounts.successor) lanes homes.symm clusters blocks capAt batch (Nat.two_pow_pos _)
    rfl rfl rfl ready.2 issued hr.hubs (fun x=>pr.stock x.val) addresses rfl rfl small word ceiling
    amounts.depth (by unfold quota;omega) (by
      change _ < 2^(old).paidBits
      rw [width]
      exact stock) (by
      change _ < 2^(old).paidBits
      rw [width]
      exact arrival) posted entered
    hostPos chunkPos peerExtent rfl rfl (homes ▸ hr.hosts) amounts.board elapsed sorted

end
end Hierarchy.DescentDatedAddressBook.PhysicalReset

end OAI
