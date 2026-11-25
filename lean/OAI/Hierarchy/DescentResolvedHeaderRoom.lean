import OAI.Hierarchy.DescentOperandStateCodec

namespace OAI
/-! Bounds on a resolved header from its concrete input fields and the outgoing serial. -/
namespace Hierarchy.DescentOperandStateBanks.Pointer
open DescentPackedOperand DescentSIMDLookup
open scoped Classical Fin.CommRing
noncomputable section
variable {s : ℕ}

private theorem labels_small : 2<2^(s+2) :=by
  have scale : 2^2≤2^(s+2) := Nat.pow_le_pow_right (by decide) (by omega)
  omega

theorem private_header_room (n:ℕ) (fits:n<2^(s+2)) (f:Fin 4) :
    (Pointer.privateWord n).header f<2^(s+2) :=by
  have tags:=labels_small (s:=s)
  fin_cases f <;> simp [Pointer.header]; omega

private theorem pin_room {id chunk:ℕ} (idRoom:id<2^(s+2)) (low:chunk<2^(s+2)) (f:Fin 4) :
    (Pointer.pin id chunk).header f<2^(s+2) :=by
  have tags:=labels_small (s:=s)
  fin_cases f <;> simp [Pointer.header] <;> omega

private theorem cable_room {p n c:ℕ} (peer:p<2^(s+2)) (serial:n<2^(s+2)) (low:c<2^(s+2)) (f:Fin 4) :
    (Pointer.cable p n c).header f<2^(s+2) :=by
  have tags:=labels_small (s:=s)
  fin_cases f <;> simp [Pointer.header] <;> omega

/-- The marked cable's outgoing serial is the only sum in the public four-field decoder. -/
theorem resolved_header_room (a:Fragment s) (wire:∀p n c,resolve a=.cable p n c→n<2^(s+2)) (f:Fin 4) :
    (Pointer.ofKey 0 (resolve a)).header f<2^(s+2) :=by
  have zero : 0<2^(s+2) := Nat.two_pow_pos _
  cases mode:a.kind with
  | carried =>
    simpa [resolve,mode,Pointer.ofKey] using private_header_room 0 zero f
  | pin =>
    simpa [resolve,mode,Pointer.ofKey] using pin_room a.name.isLt a.chunk.isLt f
  | cable =>
    cases one:a.firstCapture with
    | true => simpa [resolve,mode,one,Pointer.ofKey] using private_header_room 0 zero f
    | false =>
      cases two:a.secondCapture with
      | true => simpa [resolve,mode,one,two,Pointer.ofKey] using private_header_room 0 zero f
      | false =>
        cases paid:a.marked with
        | false =>
          simpa [resolve,mode,one,two,paid,Pointer.ofKey] using cable_room a.peer.isLt a.start.isLt a.chunk.isLt f
        | true =>
          have wrote : resolve a=.cable a.peer.val (a.start.val+a.chunk.val/a.grain.val)
              (a.chunk.val%a.grain.val) := by simp [resolve,mode,one,two,paid]
          rw [wrote]
          exact cable_room a.peer.isLt (wire _ _ _ wrote) ((Nat.mod_le ..).trans_lt a.chunk.isLt) f

end
end Hierarchy.DescentOperandStateBanks.Pointer

end OAI
