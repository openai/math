import OAI.Hierarchy.DescentDatedTicketOccurrence
import OAI.Hierarchy.DescentTicketFragment

namespace OAI
/-! # Reading the previous operand and the eight current numeric fields at one occurrence -/
namespace Hierarchy.DescentDatedOperandCoordinates.Ticket
open DescentSIMDLookup DescentPackedOperand DescentOperandStateBanks
open DescentPriorOperandColumns DescentOrdinaryLocalFragment
open scoped Classical Fin.CommRing
noncomputable section
variable {b : ℕ}

def side (v : Fin 8 → ℕ) (grain : Cell (b+2)) : Side b where
  donor:=(v 0:Cell (b+2))
  firstCapture:=decide (v 1≠0)
  secondCapture:=decide (v 2≠0)
  marked:=decide (v 3≠0)
  start:=(v 4:Cell (b+2))
  grain:=grain

def compiled (v : Fin 8 → ℕ) (grain : Cell (b+2)) (p : Pointer) (fit : ∀f,p.header f<2^(b+2)) :=
  route ((side v grain).withHeader p fit) (v 5:Cell (b+2)) ((11*v 6+v 7:ℕ):Cell (b+2))

theorem inherited {priorAlias : ℕ} (fit : ∀f,(Pointer.privateWord priorAlias).header f<2^(b+2))
    (blocks rank block key start peer role : ℕ) (anchor : Fin 5 → ℕ) (raw : Fin 6 → ℕ) (grain : Cell (b+2))
    (room : rank*blocks+block < 2^(b+2)) :
    resolve (compiled (fields blocks 1 0 (rank+1) block key start peer role anchor raw) grain (.privateWord priorAlias) fit)=
      .carried (rank*blocks+block) priorAlias :=by
  rw [private_word]
  simp [-Nat.cast_add,-Nat.cast_mul,compiled,route,side,Side.withHeader,Pointer.header,resolve,Fin.val_cast_of_lt room]

theorem exterior_word (actor blocks prev block key start peer role port j : ℕ)
    (anchor : Fin 5 → ℕ) (raw : Fin 6 → ℕ) (grain : Cell (b+2))
    (fit : ∀f,(Pointer.pin port j).header f<2^(b+2)) :
    resolve (compiled (fields blocks actor 2 prev block key start peer role anchor raw) grain (.pin port j) fit)=
      .pin port j :=by
  simp [compiled,route,side,Side.withHeader,Pointer.header,resolve]

theorem capture_fields (blocks actor prev block key start peer mouth oldPeer oldSerial chunk : ℕ)
    (anchor : Fin 5 → ℕ) (raw : Fin 6 → ℕ) (grain : Cell (b+2))
    (fit : ∀f,(Pointer.cable oldPeer oldSerial chunk).header f<2^(b+2))
    (active : actor=1 ∨ actor=2) (present : key≠0) (second : Bool)
    (firstFlag : raw 2=(!second).toNat) (secondFlag : raw 3=second.toNat)
    (rootRoom : raw 4*blocks+(anchor 0-1)<2^(b+2))
    (nameRoom : 11*(anchor 1-1)+(if actor=2 then mouth else anchor 2)<2^(b+2)) :
    let v:=fields blocks actor 1 prev block key start peer mouth anchor raw
    let mk:=if second then Key.second else Key.first
    resolve (compiled v grain (.cable oldPeer oldSerial chunk) fit)=
      mk (raw 4*blocks+(anchor 0-1)) 0 (11*(anchor 1-1)+(if actor=2 then mouth else anchor 2)) chunk :=by
  cases second <;>
    simp [-Nat.cast_add,-Nat.cast_mul,compiled,side,Side.withHeader,route,resolve,cable blocks actor prev block key start peer mouth anchor raw active present,
      firstFlag,secondFlag,Bool.toNat,Pointer.header,Fin.val_cast_of_lt rootRoom,Fin.val_cast_of_lt nameRoom]

theorem surviving_fields (blocks actor prev block key start peer mouth oldPeer oldSerial chunk : ℕ)
    (anchor : Fin 5 → ℕ) (raw : Fin 6 → ℕ) (grain : Cell (b+2))
    (fit : ∀f,(Pointer.cable oldPeer oldSerial chunk).header f<2^(b+2))
    (active : actor=1 ∨ actor=2) (present : key≠0) (one : raw 2=0) (two : raw 3=0) :
    let role:=if actor=2 then mouth else anchor 2
    let marked:=decide ((if role=0 then raw 5 else 1)≠0)
    let v:=fields blocks actor 1 prev block key start peer mouth anchor raw
    resolve (compiled v grain (.cable oldPeer oldSerial chunk) fit)=
      resolve (Public.fragment marked (peer:Cell (b+2)) (start:Cell (b+2))
        (⟨chunk,show chunk<2^(b+2) from fit 3⟩:Cell (b+2)) grain) :=by
  dsimp only
  let v:=fields blocks actor 1 prev block key start peer mouth anchor raw
  let old:=(side v grain).withHeader (.cable oldPeer oldSerial chunk) fit
  have openOne:=cable blocks actor prev block key start peer mouth anchor raw active present
  have s₁ : old.firstCapture=false:=by simp [old,Side.withHeader,side,v,openOne,one,two]
  have s₂ : old.secondCapture=false:=by simp [old,Side.withHeader,side,v,openOne,one,two]
  have actual:=surviving old (v 5:Cell (b+2)) ((11*v 6+v 7:ℕ):Cell (b+2)) rfl s₁ s₂
  simpa [compiled,old,side,Side.withHeader,v,openOne,one,two,Pointer.header] using actual

end
end Hierarchy.DescentDatedOperandCoordinates.Ticket

end OAI
