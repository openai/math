import OAI.Hierarchy.DescentDatedTicketOccurrence
import OAI.Hierarchy.DescentDatedOperandCoordinateBooks
import OAI.Hierarchy.DescentDatedMatcherRead
import OAI.Hierarchy.DescentResetStemMux

namespace OAI
/-! # Ordinary operand tickets at the physical path, donor, and role selected by the matcher -/
namespace Hierarchy.DescentDatedOperandCoordinates.Ticket
open DescentSIMDLookup
open DescentPacking.PackedMatch.Local.Stage
open scoped Fin.CommRing
noncomputable section

variable {B C P d : ℕ}

/-- The old source block, its outgoing ordinal and its eleven-way role. This
is definitionally the physical donor material seat. -/
abbrev SocketSeat (B C : ℕ) := Fin B × Fin C × Fin 11

def seatNo (z : SocketSeat B C) : Fin (B*(C*11)) :=
  finProdFinEquiv (z.1,finProdFinEquiv z.2)

/-- The matcher uses two signed banks per donor block. Only the old outgoing
slot and its role enter the smaller, eleven-role raw material bank. -/
def anchor (birth : Bool) (z : SocketSeat B C) :=
  anchorColumns C (z.1.val*(2*C)+z.2.1.val,if birth then 0 else z.2.2.val)

theorem anchor_at (birth : Bool) (z : SocketSeat B C) :
    let role:=if birth then 0 else z.2.2.val
    anchor birth z= ![1+z.1.val,1+z.2.1.val,role,1+11*z.2.1.val+role,
      1+11*(z.1.val*C+z.2.1.val)+role] := by
  have lo : z.2.1.val<2*C := by have:=z.2.1.isLt;omega
  have hdiv : (z.1.val*(2*C)+z.2.1.val)/(2*C)=z.1.val := by
    rw [Nat.mul_comm z.1.val (2*C),Nat.mul_add_div (by omega),Nat.div_eq_of_lt lo,Nat.add_zero]
  simp only [anchor,anchorColumns,hdiv,Nat.mul_add_mod_of_lt lo]

def socket (p : Fin P) (birth : Bool) (z : SocketSeat B C) :=
  rawSocket P (B*(C*11)) (if birth then 2 else 1) (p.val+1) (anchor birth z 4)
    (if birth then z.2.2.val else 0)

theorem socket_at (p : Fin P) (birth : Bool) (z : SocketSeat B C) :
    socket p birth z=(finProdFinEquiv (p,seatNo z)).val+1 := by
  have head : anchor birth z 4=(z.1.val*C+z.2.1.val)*11+(if birth then 0 else z.2.2.val)+1 := by
    rw [anchor_at]
    change 1+11*(z.1.val*C+z.2.1.val)+_=_
    omega
  unfold socket
  rw [head]
  cases birth
  · exact raw_at p z.1 z.2.1 z.2.2
  · simpa only [seatNo,Prod.eta,Bool.false_eq_true,ite_true,ite_false,Nat.add_zero] using born_raw_at p z.1 z.2.1 z.2.2

/-- The bounded matcher read is the five-column anchor of the decoded seat.
Its target side may have redirected to the first donor of a selected pair. -/
theorem matcher_at (shape : DescentPacking.PackedMatch.Shape) (packet : Cell shape.outputBits)
    (target : Bool) (key : ℕ) (small : key<2^shape.digit) (z : SocketSeat B C) (birth : Bool)
    (chosen : retarget (topologyRecord shape packet) target key =
      (z.1.val*(2*C)+z.2.1.val,if birth then 0 else z.2.2.val)) (i : Fin 5) :
    anchorField shape C i packet (anchorQuery shape.digit key target) =
      (anchor birth z i : Cell (shape.digit+4)) := by
  rw [anchor_read shape C key i packet target small,chosen]
  rfl

/-- Apply the actual bounded raw-coordinate gate. Retained actors use the
reached path; newborns use the predecessor path and the measured mouth role. -/
theorem gate_socket (p : Fin P) (birth : Bool) (z : SocketSeat B C) (v : Fin 5→Cell d)
    (cause : (v 0).val=if birth then 2 else 1)
    (path : (if birth then (v 1).val+1 else (v 2).val)=p.val+1)
    (key : (v 3).val=anchor birth z 4) (mouth : birth=true→(v 4).val=z.2.2.val) :
    (rawLaw P (B*(C*11)) d 0 v).val=socket p birth z := by
  have fits : socket p birth z≤P*(B*(C*11)) := by
    rw [socket_at]
    exact (finProdFinEquiv (p,seatNo z)).isLt
  unfold rawLaw
  suffices h : rawSocket P (B*(C*11)) (v 0).val (sourcePath (v 0).val (v 1).val (v 2).val) (v 3).val (v 4).val =
      socket p birth z by rw [h,digit_at fits]
  rw [cause,key]
  cases birth with
  | false =>
      change (v 2).val=p.val+1 at path
      change rawSocket P (B*(C*11)) 1 (v 2).val (anchor false z 4) (v 4).val =
        rawSocket P (B*(C*11)) 1 (p.val+1) (anchor false z 4) 0
      rw [path]; simp [rawSocket]
  | true =>
      change (v 1).val+1=p.val+1 at path
      change rawSocket P (B*(C*11)) 2 ((v 1).val+1) (anchor true z 4) (v 4).val =
        rawSocket P (B*(C*11)) 2 (p.val+1) (anchor true z 4) z.2.2.val
      rw [path,mouth rfl]

/-- The native one-based multiplexer at the mixed-radix key reads the
path/seat column, including the role within an old outgoing ticket. -/
theorem pick_at {b : ℕ} (p : Fin P) (birth : Bool) (z : SocketSeat B C)
    (q : Cell d) (present : q.val=socket p birth z) (heads : Fin (P*(B*(C*11)))→Cell b) :
    DescentResetStemMux.pick q heads=heads (finProdFinEquiv (p,seatNo z)) :=
  DescentResetStemMux.pick_actor q heads _ (present.trans (socket_at p birth z))

/-- At either kind of occupied seat, the original block, outgoing ordinal,
and effective role are the same indices used to select the six raw columns. -/
theorem seat_fields (p : Fin P) (birth : Bool) (z : SocketSeat B C)
    (key rank block start peer : ℕ) (raw : Fin 6→ℕ) (present : key=socket p birth z) :
    let got:=raw 2≠0 ∨ raw 3≠0
    fields B (if birth then 2 else 1) 1 rank block key start peer z.2.2.val (anchor birth z) raw =
      ![if got then raw 4*B+z.1.val else 0,raw 2,raw 3,if z.2.2.val=0 then raw 5 else 1,
        if got then 0 else start,if got then 0 else peer,z.2.1.val,z.2.2.val] := by
  have occupied : key≠0 := by rw [present,socket_at];omega
  have live : (if birth then 2 else 1)=1 ∨ (if birth then 2 else 1)=2 := by cases birth <;> decide
  rw [cable _ _ _ _ _ _ _ _ _ _ live occupied]
  rw [anchor_at]
  cases birth <;> simp [Nat.add_comm 1]

end
end Hierarchy.DescentDatedOperandCoordinates.Ticket

end OAI
