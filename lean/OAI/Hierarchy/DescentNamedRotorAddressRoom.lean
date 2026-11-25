import OAI.Hierarchy.DescentRecordedRotorBatchRoom
import OAI.Hierarchy.DescentResetRetainedCalendarWidths
import OAI.Hierarchy.DescentRotorOperandQueryROM

namespace OAI
/-! # The whole attained rotor address range fits the named date's local node strip -/
namespace Hierarchy.DescentSixParty.ClosedReset
open DescentCompiler DescentRecordedRotorLayers
open scoped Classical
noncomputable section
variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {G : PoweredGadget F}
  {q ε : ℝ} {S : AtomSchedule} {k i z wire hist : ℕ} {W : MarkedWorld F d P bits}
  {D n h C f g cut tail : ℕ} {input : Reached W G q ε S k i z D wire hist}
  {ctl : ResetRates G S k D n h C f g cut tail} (B : ClosedReset input ctl)
local notation "T" => S.epochPower

/-- The last available calendar capacity step pays the factor (2^f) in
the actual rotor layer count. The fixed remaining factor fits the original
node price exponent, independently of the date or the selected root. -/
theorem named_rotor_address_room {p : ℕ} (recorded : B.Recorded p) (date : ℕ)
    (grain : z=S.grainAt G.b p date) (growth : G.b≤2^S.capGain)
    (side : Bool) (root : B.reset.placement.Good) :
    (B.reset.circuit side root).layers*(B.reset.unit/p)≤S.retainedNodes:=by
  let capRoom:=T^S.localCapacityExponent
  let pieces:=T^S.localGrainExponent
  have big : 2≤T:=Nat.one_lt_two_pow ctl.height.ne'
  have capPos : 1≤capRoom:=Nat.pow_pos (by omega)
  have fstep : f≤S.capGain:=by
    have room:=ctl.cap
    rw [ctl.gain] at room
    exact (Nat.le_add_right f _).trans room
  have cap : 2^f*input.placement.cap≤capRoom:=by
    apply S.local_capacity (i:=i+1) ctl.height (Nat.succ_le_of_lt B.age)
    calc
      _ ≤ 2^f*2^(8+S.capGain*i):=Nat.mul_le_mul_left _ input.valid.capacity
      _ = 2^(f+(8+S.capGain*i)):=(pow_add ..).symm
      _ ≤ 2^(8+S.capGain*(i+1)):=Nat.pow_le_pow_right (by decide) (by rw [Nat.mul_succ];omega)
  have layersFit : layers n ctl.bitsR f input.placement.cap≤21*capRoom:=by
    have d:=Nat.div_le_self (10*2^f*input.placement.cap) (2^n*ctl.bitsR)
    have cost:=Nat.mul_le_mul_left 10 cap
    rw [←Nat.mul_assoc] at cost
    unfold layers
    omega
  have grainFit : ResetInput.calendarLanes S G.b date≤pieces:=
    (S.grain_le_first G.b 1 date G.base_pos).trans (by simpa [pieces] using S.first_width_payload ctl.height growth 1)
  have fixedCost : 21≤T^5:=(show 21≤2^5 by decide).trans (Nat.pow_le_pow_left big _)
  have price : 5+S.localGrainExponent≤S.priceExponent:=by
    unfold DescentCompiler.AtomSchedule.localGrainExponent DescentCompiler.AtomSchedule.priceExponent atomExponent
    omega
  rw [B.attained_batch_count recorded date grain side root]
  change layers n ctl.bitsR f input.placement.cap*ResetInput.calendarLanes S G.b date≤T^S.localTokenExponent
  calc
    _ ≤ (21*capRoom)*pieces:=Nat.mul_le_mul layersFit grainFit
    _ ≤ (T^5*capRoom)*pieces:=Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ fixedCost)
    _ = T^(5+S.localGrainExponent+S.localCapacityExponent):=by simp only [pow_add,capRoom,pieces];ring
    _ ≤ T^S.localTokenExponent:=Nat.pow_le_pow_right (by omega) (Nat.add_le_add_right price _)

theorem named_rotor_shape_room {p : ℕ} (recorded : B.Recorded p) (date : ℕ)
    (grain : z=S.grainAt G.b p date) (growth : G.b≤2^S.capGain)
    (field query lanes : ℕ) (side : Bool) (root : B.reset.placement.Good) :
    (B.reset.circuit side root).layers*(B.reset.unit/p)≤
      (Window.rotorQueryShape B (B.reset.unit/p) S.retainedNodes field query lanes).addresses:=
  B.named_rotor_address_room recorded date grain growth side root

end
end Hierarchy.DescentSixParty.ClosedReset

end OAI
