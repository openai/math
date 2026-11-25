import OAI.Hierarchy.DescentNamedPostedRotation
import OAI.Hierarchy.DescentProfiledSnapshotWordRoom
import OAI.Hierarchy.DescentScheduledEstimatorWords
import OAI.Hierarchy.DescentRegisteredGeometry
import OAI.Hierarchy.DescentNamedPacketRootLimits
import OAI.Hierarchy.DescentChosenRotorMenu

namespace OAI
/-! # Reading the saved basis at a reset with the selected physical schedule -/
namespace Hierarchy.DescentSixParty.Chronology.DatePorts
open DescentDatedAddressBook DescentDatedAddressBook.PhysicalReset DescentCompiler
open DescentPacking.PackedMatch.Local.Stage DescentPackedWalsh DescentSIMDLookup DescentResetGates
open Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM DescentColonies
open ThreeFlat.Routing
noncomputable section
set_option quotPrecheck false
set_option hygiene false
set_option maxRecDepth 8192
set_option maxHeartbeats 500000
open scoped Fin.CommRing
variable {F : Type} [Field F] (G : PoweredGadget F) (S : AtomSchedule) {n d : ℕ}
    (board : NonlinearExpanders.Graph n d) (k tail age p f gain drift degree h : ℕ)
    (ordinary : ℕ→Dated.Ordinary) (op : RotorSpec) (s Z : ℕ) (prev : DatePorts) (floor w : ℕ)
local notation "cap" => ((capCalendar G.b S.rounds gain S.height).take age).prod*256
local notation "oldExp" => NativePitch.resetCut S k tail p f h age
local notation "nextM" => NativePitch.incoming S k tail p f h ordinary (age+1)
local notation "token" => DescentPrimitivePalette.printedBits G s Z op
local notation "cut" => receiverCut G S board k tail age p f gain drift degree h oldExp nextM op.C op.w
  prev.operandLanes prev.roleLanes token prev.venue
local notation "fits" => scheduled_cut_origin G S board k tail age p f gain drift degree h ordinary op s Z
  prev.operandLanes prev.roleLanes prev.venue
local notation "priorFits" => preceding_cut S k tail p f h age
local notation "innerFloor" => prev.priorStart k floor
local notation "earlier" => (prev.afterPad k floor).archive
local notation "publisher" => priorArchivePhase G S board k tail age p f gain drift degree h ordinary op s Z prev floor w
local notation "layout" => previousArchiveLayout G S board k tail age p f gain drift degree h ordinary op s Z prev floor
local notation "a" => (scheduledAtPorts G S board k tail age p f gain drift degree h ordinary op s Z prev floor).inner
local notation "room" => ScheduledCodeRoom G S board k tail age p f gain drift degree h ordinary op s Z
  prev.operandLanes prev.roleLanes prev.venue prev.io innerFloor w earlier
variable (capacity : prev.venue.cap=cap) (space : room)

local notation "inputs" => resetInputs G S board k tail age p f gain drift degree h ordinary op s Z prev floor w space
local notation "issued" => resetDate G S board k tail age p f gain drift degree h ordinary op s Z prev floor w capacity space
local notation "L₀" => (a).ingress
local notation "phase" => (L₀).phase innerFloor w prev.io.hubs (fun x=>prev.io.atoms x.val)
  (fun j=>prev.io.wire j.1.val j.2.val)

local notation "finish" => resetFinalInputs G S board k tail age p f gain drift degree h ordinary op s Z prev floor w capacity space


local notation "outer" => scheduledAtPorts G S board k tail age p f gain drift degree h ordinary op s Z prev floor
local notation "E₀" => (a).estimator ((a).stageStart innerFloor)
variable {X : Type} {d₀ : ℕ} {b₀ : X→ℕ} {W : MarkedWorld F d₀ X b₀} {q ε : ℝ}
  {z D C cut₀ : ℕ} {input : Reached W G q ε S k age z D (S.epochPower^S.priceExponent) (S.firstWidth G.b p)}
  {ctl : ResetRates G S k D n d C f gain cut₀ tail} (B : ClosedReset input ctl)

theorem earned_reset_rotation (accepted : B.Recorded p) (boardAt : board=ctl.board)
    (opAt : op=RotorSpec.ofRates ctl) (gr : z=S.grainAt G.b p (age+1)) (branch : G.b≤2^S.capGain)
    (degreeAt : prev.venue.degree=D) (dated : D=atRound S.rounds)
    (capAt : prev.venue.cap=input.placement.cap) (hostAt : prev.venue.hosts=S.hostSize age)
    (groupAt : prev.venue.groups=S.groupCount age) (keyAt : prev.venue.k=k)
    (oldPos : 0<prev.venue.lanes) (oldWidth : prev.venue.paidBits=S.censusBits p)
    (headerRoom : prev.HeaderRoom w floor) (oldWires : prev.WireRoom w floor) (oldPaid : prev.PaidRoom w floor)
    (ready : (inputs).Ready) (fitted : (finish).Room) (roof : (outer).fullEnd<2^w)
    (scalars : SnapshotWordRoom S n d k tail p f gain h w) (lanes : 2^cut≤w)
    (calendar : ℕ→DateCode w) (boot : Memory w) (printed : calendar age=issued)
    (padded : (publisher).Runs (DateCode.history calendar boot age))
    (population : (publisher).image (DateCode.history calendar boot age) prev.archive.count.base=(Fintype.card input.V:Word w))
    (seen : stageVenue input input.valid.host prev.io prev.venue.lanes prev.venue.paidBits innerFloor
      (input.venueRoster input.valid.host) ((publisher).image (DateCode.history calendar boot age))) :
    DateCode.history calendar boot (age+1) ((NativeDate.reset (F:=F) (P:=Unit) (a)).saved innerFloor)=
      ((DescentExterior.matrixCode B.frame.basis).val:Word w) :=by
  subst board
  subst op
  let board:=ctl.board
  let op:=RotorSpec.ofRates ctl
  have ordered := (outer).stages.1
  have head := headerRoom.mono ordered
  have wires := oldWires.mono ordered
  have paid := oldPaid.mono ordered
  have coordinates (x : DescentColonies.Block k) (j : Fin (2*input.placement.cap)) :
      (prev.io.wire x.val j.val).Fits w innerFloor ∧
      S.hostSize age*chunks (S.groupCount age) prev.venue.lanes ≤ (prev.io.wire x.val j.val).size :=by
    have actual:=wires (x.cast (congrArg (2^·) keyAt.symm))
      (j.cast (congrArg (2*·) capAt.symm))
    simp only [hostAt,groupAt,Fin.val_cast] at actual
    exact actual
  have cap₀:=capAt.symm.trans capacity
  have mass : 0< input.placement.wire*(input.placement.z*G.b)*input.placement.cap:=by
    rw [input.edges,input.grain,cap₀,gr]
    exact Nat.mul_pos (Nat.mul_pos (Nat.pow_pos (Nat.two_pow_pos _))
      (Nat.mul_pos (S.grain_positive G.base_pos accepted.positive _) G.base_pos))
      (Nat.mul_pos (Chronology.DonorDate.prefix_cap_pos G.b S.rounds gain S.height age G.base_pos) (by decide))
  have dc:=degreeAt.trans dated
  have est:=scalars.estimator age B.age.le
  rw [←dc] at est
  obtain ⟨score,heading,hostBits⟩:=scheduled_estimator_words G S ctl.board k tail age p f gain drift degree h
    ordinary (RotorSpec.ofRates ctl) s Z prev floor w est
  have active:=(a).occupied ((a).stageStart innerFloor)
  have first : (a).stageStart innerFloor<2^w :=((active.1.trans active.2.1).trans active.2.2).trans_lt roof
  apply PhysicalReset.DateInputs.fromNamed_posted_rotation accepted drift degree h cut oldExp (2^cut) nextM
    prev.operandLanes prev.roleLanes token prev.venue prev.io innerFloor w fits fits priorFits (earlier).count
    (earlier).nodeBase (earlier).arguments (earlier).seed space.prepared space.scene degreeAt ready publisher calendar
    boot finish fitted gr rfl cap₀ rfl branch seen head.count population coordinates oldPos oldWidth first
    (scalars.lanes age B.age.le) score mass (by simpa only [dc] using scalars.actor.degree)
    heading hostBits (by simpa only [dc] using scalars.actor.ranks)
    (by simpa only [dc] using scalars.actor.actor) (by simpa only [dc] using scalars.actor.successor)
    lanes printed padded head.hubs (fun x=>paid.stock x.val)
  intro j
  exact (coordinates j.1 (j.2.cast (congrArg (2*·) cap₀.symm))).1

end
end Hierarchy.DescentSixParty.Chronology.DatePorts

end OAI
