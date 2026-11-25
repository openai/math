import OAI.Hierarchy.DescentNamedFreshHeaders
import OAI.Hierarchy.DescentMatchedFreshPanelsAt
import OAI.Hierarchy.DescentIssuedResetShape

namespace OAI
/-! The four reached operand headers at every newly installed chronological reset node. -/
namespace Hierarchy.DescentSixParty.Chronology.RegisterTimeline
open DescentDatedAddressBook DescentDatedAddressBook.PhysicalReset DescentSixParty DescentCompiler
open DescentPacking.PackedMatch.Local.Stage DescentPackedWalsh DescentSIMDLookup DescentResetGates
open DescentPackedColony DescentBundleHistory DescentKernelHistory DescentLocalArchiveOrder DescentOperandStateBanks DescentPrimitivePalette
open DescentPackedZip DescentOrdinaryHostPad DescentRetainedRangeDigits
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
noncomputable section
set_option quotPrecheck false
set_option maxHeartbeats 1600000
set_option maxRecDepth 8000
open scoped Fin.CommRing
variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits}
    {G : PoweredGadget F} {q ε : ℝ} {S : AtomSchedule} {k age z D n₁ h₁ C f₁ g₁ cut tail₁ wire hist : ℕ}
    {input : Reached W G q ε S k age z D wire hist} {ctl : ResetRates G S k D n₁ h₁ C f₁ g₁ cut tail₁}
    {n h f g tail : ℕ} (board₀ : NonlinearExpanders.Graph n h) (op₀ : RotorSpec)
    (B : ClosedReset input ctl) (p drift degree payload w : ℕ) (ordinary : ℕ→Dated.Ordinary)
    (cursor : Position)
local notation "op" => op₀
local notation "s₀" => S.firstWidth G.b p
local notation "Z₀" => S.grainAt G.b p 0
local notation "board" => board₀
local notation "old" => cursor.ports.venue
local notation "io" => cursor.ports.io
local notation "cap" => ((capCalendar G.b S.rounds g S.height).take age).prod*256
local notation "oldExp" => NativePitch.resetCut S k tail p f payload age
local notation "nextM" => NativePitch.incoming S k tail p f payload ordinary (age+1)
local notation "oldL" => cursor.ports.operandLanes
local notation "roleL" => cursor.ports.roleLanes
local notation "token" => DescentPrimitivePalette.printedBits G s₀ Z₀ op
local notation "rcut" => receiverCut G S board k tail age p f g drift degree payload oldExp nextM (op).C (op).w
  oldL roleL token old
local notation "base" => cursor.ports.priorStart k cursor.floor
local notation "history" => (cursor.ports.afterPad k cursor.floor).archive
local notation "outer" => scheduledAtPorts G S board k tail age p f g drift degree payload ordinary op s₀ Z₀
  cursor.ports cursor.floor
local notation "a" => (outer).inner
local notation "v" => (a).successor
local notation "fits" => scheduled_cut_origin G S board k tail age p f g drift degree payload ordinary op s₀ Z₀ oldL roleL old
local notation "priorFits" => preceding_cut S k tail p f payload age
local notation "publisher" => priorArchivePhase G S board k tail age p f g drift degree payload ordinary op s₀ Z₀
  cursor.ports cursor.floor w
variable (space : ScheduledCodeRoom G S board₀ k tail age p f g drift degree payload ordinary op₀
      (S.firstWidth G.b p) (S.grainAt G.b p 0) cursor.ports.operandLanes cursor.ports.roleLanes
      cursor.ports.venue cursor.ports.io (cursor.ports.priorStart k cursor.floor) w (cursor.ports.afterPad k cursor.floor).archive)
local notation "u" => DatePorts.resetInputs G S board k tail age p f g drift degree payload ordinary op s₀ Z₀
  cursor.ports cursor.floor w space
local notation "ports" => cursor.ports
variable (oldA:Archive W) {R:ℕ} (number:Local oldA.bit) (shape:WorldShape p R oldA.bit)

open DescentDatedPriorOperand DescentSixParty.ClosedReset.Window
variable (paid:B.Recorded p) (hp:0<p) (one:1≤R) (unitPos:0<B.reset.unit)
    (whole:p∣B.reset.unit) (wide:max 1 (max B.reset.width (C*B.reset.width))≤R) (pin:P→ℕ)
local notation "nextB" => (resetArchive B p hp whole oldA).bit
local notation "nextShape" => reset_shape_at hp one B oldA shape unitPos whole wide
local notation "nextNum" => DescentLocalArchiveOrder.reset B p hp whole oldA number
local notation "ports₁" => DatePorts.reset a ((a).stageStart base) u
variable (places : DatePorts.RangeRoom
    (DatePorts.reset (scheduledAtPorts G S board₀ k tail age p f g drift degree payload ordinary op₀
      (S.firstWidth G.b p) (S.grainAt G.b p 0) cursor.ports cursor.floor).inner
      ((scheduledAtPorts G S board₀ k tail age p f g drift degree payload ordinary op₀
        (S.firstWidth G.b p) (S.grainAt G.b p 0) cursor.ports cursor.floor).inner.stageStart (cursor.ports.priorStart k cursor.floor))
      (DatePorts.resetInputs G S board₀ k tail age p f g drift degree payload ordinary op₀
        (S.firstWidth G.b p) (S.grainAt G.b p 0) cursor.ports cursor.floor w space))
    B.next (resetArchive B p hp whole oldA).bit)
variable (height:0<S.height) (grain:z=S.grainAt G.b p (age+1)) (gain:G.b≤2^S.capGain)
include paid height grain gain in
theorem matched_fresh_headers (hn:n₁=n) (hh:h₁=h) (hf:f₁=f) (hg:g₁=g) (ht:tail₁=tail)
    (hb:HEq ctl.board board₀) (ho:RotorSpec.ofRates ctl=op₀) (degreeAt:(old).degree=D)
    (ready:(u).Ready) (mem:Memory w) (capAt:input.placement.cap=cap) (actorMem:Memory w)
    (elapsed:0<age) (sorted:SourceSorted W input.order)
    («fields»:MatchedFreshInputsAt board₀ op₀ B p drift degree payload w ordinary cursor space
      hn hh hf hg ht hb ho ready actorMem)
    (orig:MatchedPublicOriginsAt board₀ op₀ B p drift degree payload w ordinary cursor space
      hn hh hf hg ht hb ho degreeAt ready mem capAt actorMem)
    (small:2*(v).receiver.candidates<2^(v).receiver.queryBits) (axes:(ports₁).rangeLayout=(v).rangeLayout)
    (choice:∀i,DatePorts.OrdinalRead u ready small actorMem i) :
    DatePorts.SevenOriginHeaders u B.next nextB nextNum places nextShape hp pin ready small axes actorMem choice
      (resetOrigin B hp whole oldA) Sum.inr:=by
  let qcut:=rcut
  let oldCut:=oldExp
  let nextLane:=nextM
  let bits₀:=token
  let entry:=(publisher).image mem
  have fitted:=fits
  have oldFits:=priorFits
  subst n
  subst h
  subst f
  subst g
  subst tail
  cases (eq_of_heq hb : ctl.board=board₀)
  cases ho
  obtain ⟨μ,measured,origin⟩:=orig
  exact DateInputs.fromNamed_fresh_headers (B:=B) paid drift degree payload qcut oldCut (2^qcut) nextLane
    oldL roleL bits₀ old io base w fitted fitted oldFits (history).count (history).nodeBase
    (history).arguments (history).seed (NamedCodeRoom.prepared space) (NamedCodeRoom.scene space) ready actorMem
    hp one unitPos whole wide oldA shape degreeAt capAt grain height gain elapsed sorted number pin places
    small axes choice «fields» entry μ measured origin

end
end Hierarchy.DescentSixParty.Chronology.RegisterTimeline

end OAI
