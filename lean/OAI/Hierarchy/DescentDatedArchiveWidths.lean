import OAI.Hierarchy.DescentDatePortArchiveWidths
import OAI.Hierarchy.DescentRegisteredOrdinaryStep
import OAI.Hierarchy.DescentCalibratedResetChart
import OAI.Hierarchy.DescentSeedPriorWordWidths

namespace OAI
/-! # The seven operand banks and primitive tape returned to the next physical date -/
namespace Hierarchy.DescentSixParty.Chronology.DatePorts
open DescentCompiler DescentDatedAddressBook DescentDatedSeedStartup DescentPacking.PackedMatch.Local.Stage
open DescentPrimitivePalette DescentDatedOperandReadPipeline ProtocolRAM
noncomputable section
set_option quotPrecheck false
variable {F : Type} [Field F] (G : PoweredGadget F) (S : AtomSchedule) (op : RotorSpec)

/-- The actual register pitch and digit format at a cut. The seed has a single node,
and every later date emits the booked, padded number of node digits. -/
theorem initial_widths {c nP p : ℕ} (X : Catalyst.Approximation F c nP) (R h k tail gain drift degree f quota base field wire hist H groups : ℕ) :
    let l:=selectedLayout G S h k tail gain p drift degree f quota base field wire hist
    ArchiveWidths G S op (initial G op X R l k H groups h (S.grainAt G.b p 0)) k tail p drift degree h 0 :=by
  intro l
  have q:=seed_data G op S h k tail gain p drift degree f quota base field wire hist (S.grainAt G.b p 0)
  refine ⟨rfl,rfl,rfl,?_,?_⟩
  · change l.operandBits*1*l.operandLanes≤h/2
    simpa only [Nat.mul_one] using q.1
  · change printedBits G l.seedWidth (S.grainAt G.b p 0) op*1*Primitive.paletteLanes G op l.seedWidth (S.grainAt G.b p 0) h k≤h/2
    simpa only [Nat.mul_one] using q.2

section Ordinary
variable {P : Type} {d k i z D z' D' wire hist : ℕ} {q ε u : ℝ} {bits : P→ℕ} {W : MarkedWorld F d P bits}
    {prevWorld : Reached W G q ε S k i z D wire hist} {he : 0≤ε} {T : StageInput W G u ε}
    {choice : (T.result he).Choice} {n : Normalize ((T.result he).state choice)}
    {next : Reached n.result G q ε S k (i+1) z' D' wire hist}
    (prior : DatePorts) (ticket : OrdinaryLink prevWorld he T choice n next)
    (gain tail p f drift degree h seats root : ℕ) (ordinary : ℕ→Dated.Ordinary)
local notation "book" => OrdinaryBooks.atDate G S op gain k i p tail drift degree h seats prior
local notation "b" => (book).onTicket ticket gain tail p f h seats prior.venue.lanes prior.io.roster ordinary
local notation "A" => (b).datedEntry prior ((b).stageStart root)

theorem ordinary_widths :
    ArchiveWidths G S op (ordinaryPorts prior ticket op gain tail p f drift degree h seats root ordinary)
      k tail p drift degree h (i+1) :=by
  let other:=purchase ((b).withFundedArguments 0 (A)).ticketReadGeometry
  have packed:=((b).funded_final_widths (A) other).2
  let donor:=DonorDate.atDate G S gain k i p
  have printed:=DescentOrdinaryPalette.Configuration.return_at G S op p h donor.degree k donor.cap prior.nodes S.retainedNodes prior.roleLanes
  exact ⟨rfl,(OrdinaryBooks.record_width G S op gain k i p tail drift degree h seats prior).1,rfl,packed,printed⟩

end Ordinary

section Reset
variable {n d : ℕ} (board : NonlinearExpanders.Graph n d) (k tail age p f g drift degree h : ℕ)
    (ordinary : ℕ→Dated.Ordinary) (oldOperand oldPrimitive : ℕ) (old : StageVenueTail.Date)
    (wire : ℕ→ℕ→Bank) (roster : Bank) (floor : ℕ)
local notation "tag" => printedBits G (S.firstWidth G.b p) (S.grainAt G.b p 0) op
local notation "a" => PhysicalReset.scheduled G S board k tail age p f g drift degree h ordinary op
  (S.firstWidth G.b p) (S.grainAt G.b p 0) oldOperand oldPrimitive old wire roster floor

theorem reset_widths {w : ℕ} (u : (a).DateInputs ((a).stageStart floor) w)
    (tables : ∀x,x∈(a).successor.receiverUnits→x*(a).successor.receiver.lanes≤h/2) :
    ArchiveWidths G S op (reset (a) ((a).stageStart floor) u) k tail p drift degree h (age+1) :=by
  let v:=(a).successor
  have packed:=tables (v.nodeBits*v.nodes+v.nodeBits) (by change _∈v.receiverUnits;simp [ResetOutput.receiverUnits])
  have printed:=tables (v.primitive.chart.bits*v.primitive.chart.nodes+v.primitive.chart.bits)
    (by change _∈v.receiverUnits;simp [ResetOutput.receiverUnits])
  refine ⟨rfl,rfl,rfl,(Nat.mul_le_mul_right _ (Nat.le_add_right ..)).trans packed,?_⟩
  exact (Nat.mul_le_mul_right _ (Nat.le_add_right ..)).trans printed

end Reset

theorem ArchiveWidths.previous {ports : DatePorts} {k tail p drift degree h age : ℕ}
    (x : ArchiveWidths G S op ports k tail p drift degree h age) :
    let b:=printedBits G (S.firstWidth G.b p) (S.grainAt G.b p 0) op
    let prior:=ResetOutput.Prior.atDate G S age p drift ports.operandLanes ports.roleLanes b ports.venue
    (DescentOperandWidth.recordBits G S k tail drift degree p*prior.nodes)*ports.operandLanes≤h/2 ∧
      (b*prior.nodes)*ports.roleLanes≤h/2 :=by
  change _*(if age=0 then 1 else S.retainedNodes)*_≤h/2 ∧ _*(if age=0 then 1 else S.retainedNodes)*_≤h/2
  rw [←x.nodes,←x.digits]
  exact ⟨x.operands,x.roles⟩

end
end Hierarchy.DescentSixParty.Chronology.DatePorts

end OAI
