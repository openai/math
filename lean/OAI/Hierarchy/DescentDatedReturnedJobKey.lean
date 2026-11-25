import OAI.Hierarchy.DescentDatedMeasuredTicketRows
import OAI.Hierarchy.DescentIssuedOperandKeyCore
import OAI.Hierarchy.DescentDatedTicketWords

namespace OAI
/-! # The chosen cable in the returned ordinary operand job book -/
namespace Hierarchy.DescentDatedPriorOperand
open DescentOperandStateBanks DescentPackedOperand DescentSIMDLookup DescentDatedOperandCoordinates
open scoped Classical Fin.CommRing
noncomputable section
variable (l:Layout) (old:Books l) (typed:BookPointers old)
    (digits:Fin l.jobs→Fin l.hosts→Fin l.groups→Fin 8→ℕ) (grain:Cell (l.size+2))
variable (room : ∀ (j : Fin l.jobs) (h : Fin l.hosts) (g : Fin l.groups),
  11*(measuredRoles l digits j 1 h g).val+(measuredRoles l digits j 2 h g).val<2^(l.size+2))


open DescentDatedOperandReadPipeline DescentOrdinaryLocalFragment DescentPriorOperandColumns
/-- These are the fragments used by the physical resolver, with different constructors
for the two capture events and the signed surviving public route. -/
theorem returned_key (j : Fin l.jobs) (h : Fin l.hosts) (y : Fin l.groups) (prevPeer prevSerial piece : ℕ)
    (read : ∀f,(booksHeader old j h y f).val=(Pointer.cable prevPeer prevSerial piece).header f)
    (donor : ℕ) (first second marked : Bool) (start peer ordinal role : ℕ)
    (exclusive : first=true→second=false)
    (reported : digits j h y=postedVector donor first second marked start peer ordinal role)
    (donorFit : donor<2^(l.size+2)) (nameFit : 11*ordinal+role<2^(l.size+2)) :
    let pieceFit:piece<2^(l.size+2):=(read 3).ge.trans_lt (booksHeader old j h y 3).isLt
    resolve ((ofBooks old typed (measuredSides l digits grain) (measuredRoles l digits) room j).compiled h y)=
      if first then Key.first donor 0 (11*ordinal+role) piece
      else if second then Key.second donor 0 (11*ordinal+role) piece
      else resolve (Public.fragment marked (peer:Cell (l.size+2)) (start:Cell (l.size+2)) ⟨piece,pieceFit⟩ grain) :=by
  intro pieceFit
  have boolean (x : Bool) : x.toNat≤1:=by cases x <;> decide
  have flags:Ticket.Flags (digits j h y):=by
    rw [reported]
    exact ⟨boolean first,boolean second,boolean marked⟩
  have nameValue : (11*(ordinal:Cell (l.size+2))+(role:Cell (l.size+2))).val=11*ordinal+role:=by
    simpa only [Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat] using (Fin.val_cast_of_lt nameFit)
  rw [source_compiled l old typed digits grain room j h y (.cable prevPeer prevSerial piece) read flags,reported]
  cases first <;> cases second <;> try contradiction
  all_goals cases marked <;> simp [postedVector,Ticket.compiled,Ticket.side,Side.withHeader,Pointer.header,
    route,resolve,Public.fragment,Fin.val_cast_of_lt donorFit,nameValue]

end
end Hierarchy.DescentDatedPriorOperand

end OAI
