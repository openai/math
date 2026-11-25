import OAI.Hierarchy.DescentReachedResetHeaderRoom
import OAI.Hierarchy.DescentNamedResetOutput
import OAI.Hierarchy.DescentClosedReset

namespace OAI
/-! A true successor cable fits the actual issued reset operand word at every field. -/
namespace Hierarchy.DescentSixParty.ClosedReset.Window
open DescentCompiler DescentDatedAddressBook DescentLocalArchiveOrder DescentKernelHistory DescentBundleHistory
open DescentOperandStateBanks
noncomputable section
set_option quotPrecheck false

variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits}
  {G : PoweredGadget F} {q ε : ℝ} {S : AtomSchedule}
  {k age grain oldDegree wire hist n h C f g cut tail p R : ℕ}
  {incoming : Reached W G q ε S k age grain oldDegree wire hist}
  {ctl : ResetRates G S k oldDegree n h C f g cut tail} (B : ClosedReset incoming ctl)
  (archive : BitDescription B.reblock.result) (rank : Local archive) (shape : WorldShape p R archive)
  (hp : 0<p) (pin : P→ℕ) (slots : ℕ) (x : NodeOrder.All archive) (j : ℕ)
  (positive : 0<S.height) (grainAt : grain=S.grainAt G.b p (age+1)) (base : G.b≤2^S.capGain)
  (drift degree payload e previous M nextM packet : ℕ) (old : ResetOutput.Prior) (start : ℕ)
local notation "chart" => ResetOutput.fromBoard G S ctl.board k tail age p f g drift degree payload e previous M nextM
  C packet old start
local notation "physical" => Reached.argumentPointer B.next archive rank shape hp pin slots x j

include positive grainAt base in
theorem original_cable_header_fits (peer serial chunk : ℕ)
    (cable : physical=Pointer.cable peer serial chunk) (field : Fin 4) :
    (physical).header field<2^(chart).receiver.valueBits:=by
  have maximum : 3≤DescentOperandWidth.raw S:=by
    unfold DescentOperandWidth.raw
    omega
  have cover : 3≤DescentOperandWidth.bound G S drift degree:=
    maximum.trans ((Nat.le_max_left ..).trans ((Nat.le_max_right ..).trans (Nat.le_max_right ..)))
  have trueField:=Reached.argument_cable_header_room B.next hp x.1 archive rank shape pin slots x.2 j
    (k:=k) (tail:=tail) (drift:=drift) (upper:=degree) B.age positive grainAt base cover peer serial chunk cable field
  exact trueField.trans_le (Nat.pow_le_pow_right (by decide)
    (show DescentOperandWidth.s G S k tail drift degree ≤ DescentOperandWidth.recordBits G S k tail drift degree p
      from Nat.le_max_left ..))

end
end Hierarchy.DescentSixParty.ClosedReset.Window

end OAI
