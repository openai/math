import OAI.Hierarchy.DescentRecordedRotorLayers
import OAI.Hierarchy.DescentOccurrenceAllowance
import OAI.Hierarchy.DescentResetRootWordPrice
import OAI.Hierarchy.DescentPackedResetRotorRoles

namespace OAI
/-! # The real reset root stores one opcode per layer and calendar grain batch -/
namespace Hierarchy.DescentSixParty.ClosedReset
open DescentCompiler DescentRecordedRotorLayers DescentDatedAddressBook.ResetMiddle
open scoped Classical
noncomputable section
variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {G : PoweredGadget F}
  {q ε : ℝ} {S : AtomSchedule} {k i z wire hist : ℕ} {W : MarkedWorld F d P bits}
  {D n h C f g cut tail : ℕ} {input : Reached W G q ε S k i z D wire hist}
  {ctl : ResetRates G S k D n h C f g cut tail} (B : ClosedReset input ctl)
local notation "T" => S.epochPower

def paidBatchExponent (S : AtomSchedule) (instruction f : ℕ) :=
  Nat.clog 2 (instruction*(42*2^f)+1)+S.localCapacityExponent+S.localGrainExponent

def calendarBatchCount (S : AtomSchedule) (n packet f cap b date : ℕ) :=
  layers n packet f cap*ResetInput.calendarLanes S b date

/-- The time index for this calendar is the one for which the actual incoming
gadget width is grainAt times its base. -/
theorem attained_batch_count {p : ℕ} (r : B.Recorded p) (date : ℕ) (grain : z=S.grainAt G.b p date)
    (side : Bool) (host : B.reset.placement.Good) :
    (B.reset.circuit side host).layers*(B.reset.unit/p)=calendarBatchCount S n ctl.bitsR f input.placement.cap G.b date:=by
  have fit:=ResetInput.calendar_fit B.reset S G.b p date (B.unit.trans (congrArg (·*G.b) grain))
  rw [DescentRecordedRotorLayers.recorded B r side host,fit,Nat.mul_div_cancel _ r.positive]
  rfl

include B in
theorem calendar_batch_paid (instruction date : ℕ) (gadget : G.b≤2^S.capGain) :
    instruction*calendarBatchCount S n ctl.bitsR f input.placement.cap G.b date≤T^paidBatchExponent S instruction f:=by
  let capRoom:=T^S.localCapacityExponent
  let grains:=T^S.localGrainExponent
  let price:=instruction*(42*2^f)
  let e:=Nat.clog 2 (price+1)
  have big:2≤T:=Nat.one_lt_two_pow ctl.height.ne'
  have capPositive:1≤capRoom:=Nat.pow_pos (by omega)
  have capPaid:input.placement.cap≤capRoom:=S.local_capacity ctl.height B.age.le input.valid.capacity
  have capTally:input.placement.cap+1≤2*capRoom:=by omega
  have grainPaid:ResetInput.calendarLanes S G.b date≤grains:=
    (S.grain_le_first G.b 1 date G.base_pos).trans (by simpa [grains] using S.first_width_payload ctl.height gadget 1)
  have priceRoom:price≤T^e:= (Nat.le_succ _).trans ((Nat.le_pow_clog (by decide) _).trans (Nat.pow_le_pow_left big _))
  have layerPaid : layers n ctl.bitsR f input.placement.cap≤21*2^f*(input.placement.cap+1):=by
    have div_:=Nat.div_le_self (10*2^f*input.placement.cap) (2^n*ctl.bitsR)
    unfold layers
    nlinarith [Nat.two_pow_pos f]
  calc
    instruction*calendarBatchCount S n ctl.bitsR f input.placement.cap G.b date
        ≤ instruction*((21*2^f*(2*capRoom))*grains) := Nat.mul_le_mul_left _
          (Nat.mul_le_mul (layerPaid.trans (Nat.mul_le_mul_left _ capTally)) grainPaid)
    _ = (price*capRoom)*grains:=by dsimp only [price];ring
    _ ≤ (T^e*capRoom)*grains := Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ priceRoom)
    _ = _ := by simp only [paidBatchExponent,pow_add,capRoom,grains,e,price]

theorem canonical_root_paid {p : ℕ} (r : B.Recorded p) (date : ℕ) (grain : z=S.grainAt G.b p date)
    (gadget : G.b≤2^S.capGain) (side : Bool) (host : B.reset.placement.Good) :
    let codeBits:=DescentPackedResetRotorRoles.roleBits n
    rootWord ctl.board k (GroupStage.depthBound D n f g) f input.placement.cap C ctl.bitsR codeBits
      ((B.reset.circuit side host).layers*(B.reset.unit/p)) ≤
      T^(Nat.clog 2 (rootCoefficient ctl.board (GroupStage.depthBound D n f g) f C ctl.bitsR+1)+
        max (S.fallbackExponent cut) (paidBatchExponent S codeBits f)):=by
  dsimp only
  apply B.root_word_paid
  rw [B.attained_batch_count r date grain side host]
  exact B.calendar_batch_paid _ date gadget

end
end Hierarchy.DescentSixParty.ClosedReset

end OAI
