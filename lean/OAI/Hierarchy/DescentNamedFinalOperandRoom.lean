import OAI.Hierarchy.DescentNamedPreflightFormat
import OAI.Hierarchy.DescentTerminalPrimitivePrivateFields

namespace OAI
/-! # The three packed operand widths on the original terminal schedule -/
namespace Hierarchy.DescentSixParty.SeedNamed.Branch
open DescentCompiler DescentTerminalPointerDigits DescentTerminalPrimitiveArena
open scoped Classical
noncomputable section
set_option quotPrecheck false
variable {F : Type} [Field F] {cp P : ℕ} (X : Catalyst.Approximation F cp P) (G : PoweredGadget F) (S : AtomSchedule)
variable (k g p tail boundary drift : ℕ) (op : RotorSpec) (headers paid : ℕ)
local notation "fmt" => geometryFormat G S k g p tail boundary drift op headers paid
local notation "spec" => preflightSpec X G S k g p tail fmt
local notation "groups" => S.groupCount S.length
local notation "nodes" => S.epochPower^S.localTokenExponent
local notation "cap" => NativeBranch.privateSlotCapacity G S drift
local notation "width" => DescentSignedCableCodec.width (spec).degree (spec).cap

private theorem pointer_fits (s : Shape) (start w : ℕ) (n : 0<s.columns) (room : s.finish start<2^w) :
    s.pointerBits≤w :=by
  have shelf : 2^s.pointerBits ≤ fee s.columns s.pointerBits :=
    (Nat.le_mul_of_pos_left _ n).trans (Nat.le_add_right ..)
  have copies : fee s.columns s.pointerBits ≤ 2 * fee s.columns s.pointerBits :=
    Nat.le_mul_of_pos_left _ (by decide)
  rw [s.exact_end] at room
  exact ((Nat.pow_lt_pow_iff_right (by decide : 1 < 2)).mp
    ((((shelf.trans copies).trans (Nat.le_add_left ..)).trans (Nat.le_add_right ..)).trans_lt room)).le

/-- The pointer lookup, per-node argument family, and signed wing words all
fit the original machine word at the terminal mask allocation. -/
theorem final_operand_widths (origin w : ℕ) (room : (spec).maskBase origin<2^w) :
    (spec).scalar.pointerBits≤w ∧
    (Nat.clog 2 (boundary+cap+1)*(nodes*cap))*groups≤w ∧ width*groups≤w :=by
  obtain ⟨_,_,wc,cb,be,ec,el,ld,dm⟩:=(spec).layers origin
  have fit : (spec).scalar.finish ((spec).primitive origin)<2^w :=by
    change (spec).weights origin<2^w
    omega
  have pattern := pointer_fits (spec).scalar ((spec).primitive origin) w
    (geometry_positive G S X k g p tail boundary drift op headers paid) fit
  have count : groups*actualSpan G S op boundary p drift≤w:=
    (spec).scalar.count_word_fits ((spec).primitive origin) fit
  have args : Nat.clog 2 (boundary+cap+1)*(nodes*cap)≤actualSpan G S op boundary p drift :=by
    rw [Nat.mul_comm (Nat.clog 2 _),actualSpan,DescentTerminalVertexFields.size]
    omega
  have signed : width*groups≤(spec).scalar.pointerBits :=
    (input_bounds groups nodes (S.groupWidth k tail 0+k) (k*S.length) (2^(8+S.capGain*S.length))
      (Nat.clog 2 (nodes+1)) (Nat.clog 2 (cap+1))
      (DescentOperandWidth.recordBits G S k tail drift 3 p) width).2.2.2.2.2
  exact ⟨pattern,by rw [Nat.mul_comm _ groups];exact (Nat.mul_le_mul_left _ args).trans count,signed.trans pattern⟩

end
end Hierarchy.DescentSixParty.SeedNamed.Branch

end OAI
