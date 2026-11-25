import OAI.Hierarchy.DescentContactTicketRun
import OAI.Hierarchy.DescentContactPreviousEnds

namespace OAI
/-! # Recovering a whole installed reservation from any one of its occupied tickets -/
namespace Hierarchy.DescentChosenRouter
open DescentGL DescentColonies DescentRotor DescentCanonicalPorts
open scoped Classical BigOperators
noncomputable section
variable {V I H A : Type} [Fintype V] [DecidableEq V] [Fintype I] [Fintype H] [Fintype A] {k m n : ℕ}
variable (P : Placement V I H A k (2^n)) (book : P.ColumnRoster m)
include book

theorem Placement.ColumnRoster.ticket_le (s : Bool) (t : Reserve P.span) :
    t.2.val≤(P.outputName m s t).2.val := by
  rw [book.read];exact Nat.le_add_left _ _

theorem Placement.ColumnRoster.translate (s : Bool) (t : Reserve P.span) (j : Fin (P.span t.1)) :
    (P.outputName m s t).2.val-t.2.val+j.val=(P.outputName m s ⟨t.1,j⟩).2.val := by
  rw [book.read,book.read]
  simp [Placement.reservedColumn]

/-- All tickets in a reservation occupy exactly the indicated half-open interval. -/
theorem Placement.ColumnRoster.contains (s : Bool) (t : Reserve P.span) (col : ℕ) :
    (∃j : Fin (P.span t.1),(P.outputName m s ⟨t.1,j⟩).2.val=col) ↔
      (P.outputName m s t).2.val-t.2.val≤col ∧ col<(P.outputName m s t).2.val-t.2.val+P.span t.1 := by
  constructor
  · rintro ⟨j,h⟩
    rw [←h,←Placement.ColumnRoster.translate P book s t j]
    exact ⟨Nat.le_add_right _ _,Nat.add_lt_add_left j.isLt _⟩
  · rintro ⟨lo,hi⟩
    let j : Fin (P.span t.1):=⟨col-((P.outputName m s t).2.val-t.2.val),by omega⟩
    exact ⟨j,(Placement.ColumnRoster.translate P book s t j).symm.trans (Nat.add_sub_of_le lo)⟩

/-- This is an observed previous grain even when the particular requested column carries zero items. -/
theorem Placement.OrderedTickets.reservation_witness {M : ℕ} {key : I↪Fin M} (seen : P.OrderedTickets key)
    (t : Reserve P.span) : ∃p,(P.ticket p).1=t.1 ∧ ∀s,
      (P.outputName m s (P.ticket p)).2.val-(P.ticket p).2.val+t.2.val=(P.outputName m s t).2.val := by
  rcases t with ⟨a,j⟩
  obtain ⟨p,hp⟩:=seen.pair_observed a
  subst a
  exact ⟨p,rfl,fun s=>Placement.ColumnRoster.translate P book s (P.ticket p) j⟩

end
end Hierarchy.DescentChosenRouter

end OAI
