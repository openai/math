import OAI.Hierarchy.DescentRegisteredDateLedger
import OAI.Hierarchy.DescentRegisteredStageCalibration

namespace OAI
/-! Recover each original ordinary or reset tariff directly from its named
branch instruction, including the empty choice used when there is no cut. -/
namespace Hierarchy.DescentSixParty.Chronology.RegisterTimeline
open DescentCompiler TerminalScale DescentDatedAddressBook PhysicalReset DescentPacking.PackedMatch.Local.Stage
open scoped Classical BigOperators
noncomputable section
variable {F P : Type} [Field F] [Fintype P] {G : PoweredGadget F} {S : AtomSchedule}
    {bits : P→ℕ} {d k wire hist final w : ℕ} {q ε : ℝ} {C : Type*}
    (traces : C→RunTrace G q ε S k wire hist final bits d) {n degree : ℕ}
    (b : Menu n degree) (initial : Position)
set_option quotPrecheck false
local notation "here" i => calendar (w:=w) traces b initial i
local notation "machine" => instruction (w:=w) traces b initial

def ordinaryBill (i amount : ℕ) (e : RunTrace.Events traces i) : Prop :=by
  obtain ⟨_,e⟩:=e
  cases e with
  | ordinary before t after eqn=>
    let pos:=here i
    exact ∀(live : 0 < k) (room : DatePorts.OrdinaryCodeRoom pos.ports t b.op b.gain b.tail
      b.p b.f b.drift b.degreeLimit b.payload (b.seats i) pos.floor b.ordinary w),
      (DatePorts.ordinaryDate pos.ports t b.op b.gain b.tail b.p b.f b.drift b.degreeLimit b.payload
        (b.seats i) pos.floor b.ordinary w (b.profile i) b.header live room).tariff ≤ amount
  | reset before closed after joined=>exact True

def resetBill (i amount : ℕ) (e : RunTrace.Events traces i) : Prop :=by
  obtain ⟨_,e⟩:=e
  cases e with
  | ordinary before ticket after joined=>exact True
  | reset before t after eqn=>
    let pos:=here i
    exact ∀(cap : pos.ports.venue.cap=((capCalendar G.b S.rounds b.gain S.height).take i).prod*256)
      (space : ScheduledCodeRoom G S b.board k b.tail i b.p b.f b.gain b.drift b.degreeLimit b.payload
        b.ordinary b.op (S.firstWidth G.b b.p) (S.grainAt G.b b.p 0) pos.ports.operandLanes pos.ports.roleLanes
        pos.ports.venue pos.ports.io (pos.ports.priorStart k pos.floor) w (pos.ports.afterPad k pos.floor).archive),
      (resetMove (G:=G) (S:=S) b k i w pos cap space).code.tariff ≤ amount

omit [Fintype P] in
theorem ordinaryBill_mono {i amount larger : ℕ} (e : RunTrace.Events traces i) (le : amount ≤ larger)
    (funded : ordinaryBill traces b initial (w:=w) i amount e) : ordinaryBill traces b initial (w:=w) i larger e :=by
  obtain ⟨_,e⟩:=e
  cases e with
  | ordinary before ticket after joined=>intro pos room;exact (funded pos room).trans le
  | reset before closed after joined=>trivial

omit [Fintype P] in
theorem resetBill_mono {i amount larger : ℕ} (e : RunTrace.Events traces i) (le : amount ≤ larger)
    (funded : resetBill traces b initial (w:=w) i amount e) : resetBill traces b initial (w:=w) i larger e :=by
  obtain ⟨_,e⟩:=e
  cases e with
  | ordinary before ticket after joined=>trivial
  | reset before closed after joined=>intro cap space;exact (funded cap space).trans le

theorem date_quote_mono (host groups h rows J led rate share led' rate' share' : ℕ)
    (a : led ≤ led') (b : rate ≤ rate') (c : share ≤ share') :
    host*h*(led*scale J rate)+host*groups*(led*scale J rate)+share*rows ≤
      host*h*(led'*scale J rate')+host*groups*(led'*scale J rate')+share'*rows :=by
  have price:=Nat.mul_le_mul a (short_mono J b)
  exact Nat.add_le_add (Nat.add_le_add (Nat.mul_le_mul_left _ price) (Nat.mul_le_mul_left _ price))
    (Nat.mul_le_mul_right _ c)

omit [Fintype P] in
theorem paid_cut (i amount : ℕ) (e : RunTrace.Events traces i) (move : Move w)
    (issuedAt : issued traces b i e (here i) move)
    (ordinary : ordinaryBill traces b initial (w:=w) i amount e)
    (reset : resetBill traces b initial (w:=w) i amount e) : move.code.tariff ≤ amount :=by
  obtain ⟨_,e⟩:=e
  cases e with
  | ordinary before t after eqn=>
    obtain ⟨live,room,rfl⟩:=issuedAt
    exact ordinary live room
  | reset before t after eqn=>
    obtain ⟨cap,room,rfl⟩:=issuedAt
    exact reset cap room

omit [Fintype P] in
/-- No computation gets charged for the terminal boundary or charged twice
for the meter. The original initialization stays in the native boot receipt. -/
theorem paid_calendar (t J f g reset M τ h ratio p lead exponent share saving : ℕ)
    (config : S=stageNumbers G t J f g reset M (tail τ J))
    (positive : 0 < h) (sites : 0 < M) (width : w ≤ ratio*h)
    (paid : ∀i < S.length,∀e : RunTrace.Events traces i,
      let cost:=S.hostSize i*h*(lead*scale J exponent)+S.hostSize i*(S.groupCount i*S.radix)*(lead*scale J exponent)+
        share*(M/(2^J)^saving)
      ordinaryBill traces b initial (w:=w) i cost e ∧ resetBill traces b initial (w:=w) i cost e)
    (rooms : let R:=(lead+share+137*ratio)*scale J exponent
      ((S.length+1)*(R+1))*h ≤ p*2^(tail τ J) ∧ (S.length+1)*(2^S.hostGain)^S.length*R*2^J ≤ p) :
    (∑i∈Finset.range S.length,(machine i).tariff)*2^J ≤ 2*(M*(S.copies*p)) :=by
  apply funded_issue traces b initial t J f g reset M τ h ratio p lead exponent share saving config positive sites width
    (fun i hi e move active=>paid_cut traces b initial i _ e move active (paid i hi e).1 (paid i hi e).2)
    rooms.1 rooms.2

open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure in
omit [Fintype P] in
theorem executed_calendar (boot : Procedure w)
    (ticks J M p : ℕ)
    (dates : (∑i∈Finset.range S.length,(machine i).tariff)*2^J ≤ 2*(M*(S.copies*p))) :
    (DateCode.afterTicks ticks machine S.length+
      7*DescentStaticWordColumn.names (DateCode.afterBoot boot machine S.length))*w*2^J ≤
      ((ticks+7*DescentStaticWordColumn.names boot)*w)*2^J+2*(M*(S.copies*p)) :=by
  rw [DateCode.boot_bill,Nat.add_mul]
  exact Nat.add_le_add_left dates _

end
end Hierarchy.DescentSixParty.Chronology.RegisterTimeline

end OAI
