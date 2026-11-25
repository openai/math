import OAI.Hierarchy.DescentOperandWidth
import OAI.Hierarchy.DescentSignedCableFields

namespace OAI
/-! The three candidate-bearing components of a cable refer to the actual outgoing neighbor and lane. -/
namespace Hierarchy.DescentOperandWidth
open DescentSixParty DescentCompiler DescentCompiler.TerminalScale DescentSharedCableNames DescentOperandStateBanks
noncomputable section

theorem cable_head_lt {D cap coeff : ℕ} (u : Stage.Live D cap) (last : ℕ) (span : Span) (f : Field)
    (ptr : f.val<3) (one : 1<2^coeff) (degree : D≤2^coeff) (capacity : cap≤2^coeff) :
    (Pointer.cable u.neighbor.val (u.wire.val-u.within.val) last).fields span f<2^coeff := by
  have near := u.neighbor.isLt.trans_le degree
  have used := (Nat.sub_le u.wire.val u.within.val).trans_lt (u.wire.isLt.trans_le capacity)
  have head (i : Fin 3) :
      (Pointer.cable u.neighbor.val (u.wire.val-u.within.val) last).fields span
        (⟨i.val,i.isLt.trans (by decide : 3<7)⟩ : Field)<2^coeff := by
    fin_cases i <;> first | exact one | exact near | exact used
  exact head ⟨f.val,ptr⟩

variable {F : Type} [Field F] (G : PoweredGadget F) (S : AtomSchedule)

/-- The actual scheduled degree limit and capacity tariff suffice for every earlier or
newly produced cable. Neither the chunk nor the span enters the three fields in question. -/
theorem cable_head_record {k tail drift degree p D cap j : ℕ} (u : Stage.Live D cap) (last : ℕ)
    (span : Span) (f : Field) (ptr : f.val<3) (deg : D≤degree) (age : j≤S.length)
    (capacity : cap≤2^(8+S.capGain*j)) :
    (Pointer.cable u.neighbor.val (u.wire.val-u.within.val) last).fields span f<
      2^(recordBits G S k tail drift degree p) := by
  have wideS : s G S k tail drift degree≤recordBits G S k tail drift degree p := Nat.le_max_left ..
  have wide := Nat.pow_le_pow_right (n:=2) (by decide) wideS
  have degBound : degree≤bound G S drift degree :=
    (Nat.le_max_right (raw S) degree).trans ((Nat.le_max_right ..).trans (Nat.le_max_right ..))
  have degreeRoom : degree<2^(s G S k tail drift degree) := numeric G S degBound
  have capRoom := cableName G S (k:=k) (tail:=tail) (drift:=drift) (degree:=degree)
    (outgoing:=cap) (role:=0) age capacity (by decide)
  have head : 1<2^(s G S k tail drift degree) := by
    have two := DescentOperandWidth.wide G S k tail drift degree
    have four : 2^2≤2^(s G S k tail drift degree) := Nat.pow_le_pow_right (by decide) two
    omega
  apply cable_head_lt u last span f ptr (head.trans_le wide) (deg.trans (degreeRoom.le.trans wide))
  have room : cap≤2^(s G S k tail drift degree) :=by omega
  exact room.trans wide

end
end Hierarchy.DescentOperandWidth

end OAI
