import OAI.Hierarchy.DescentRegisterTypes
import OAI.Hierarchy.DescentDatedAddressBook
import OAI.Hierarchy.DescentPhysicalDateHistory

namespace OAI
/-! # Public register addresses and memory along a sequence of native dates -/
namespace Hierarchy.DescentSixParty.Chronology.RegisterTimeline
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
noncomputable section
open scoped Classical

structure Position where
  ports : DatePorts
  floor : ℕ

structure Move (w : ℕ) where
  code : DateCode w
  next : Position

variable {w : ℕ} {Cut : ℕ→Type*} (issue : ∀i,Cut i→Position→Move w→Prop)

def selected (i : ℕ) (p : Position) : Move w :=
  if h : ∃move : Move w, (∃c : Cut i,issue i c p move) ∧ p.floor ≤ move.next.floor
  then h.choose else ⟨.reset (scan w 0 0 .row) 4,p⟩

theorem selected_at (i : ℕ) (p : Position) (c : Cut i) (move : Move w)
    (issued : issue i c p move) (later : p.floor ≤ move.next.floor)
    (unique : ∀d t,issue i d p t→t=move) : selected issue i p=move :=by
  unfold selected
  split
  · rename_i h
    obtain ⟨d,hd⟩:=h.choose_spec.1
    exact unique d _ hd
  · rename_i absent
    exact (absent ⟨move,⟨c,issued⟩,later⟩).elim

theorem selected_floor (i : ℕ) (p : Position) : p.floor≤(selected issue i p).next.floor :=by
  unfold selected
  split
  · rename_i h
    exact h.choose_spec.2
  · exact Nat.le_refl _

variable (initial : Position)

def position : ℕ→Position
  | 0=>initial
  | i+1=>(selected issue i (position i)).next

def date (i : ℕ) := (selected issue i (position issue initial i)).code
def span (i : ℕ) := (position issue initial (i+1)).floor-(position issue initial i).floor

theorem position_floor (i : ℕ) : (position issue initial i).floor =
    DescentDatedAddressBook.floor initial.floor (span issue initial) i :=by
  induction i with
  | zero=>rfl
  | succ i ih=>
    rw [DescentDatedAddressBook.floor_succ,←ih,span]
    have h:=selected_floor issue i (position issue initial i)
    change (position issue initial i).floor≤(position issue initial (i+1)).floor at h
    omega

theorem date_at (i : ℕ) (c : Cut i) (move : Move w) (hit : issue i c (position issue initial i) move)
    (later : (position issue initial i).floor ≤ move.next.floor)
    (unique : ∀d t,issue i d (position issue initial i) t→t=move) :
    date issue initial i=move.code ∧ position issue initial (i+1)=move.next :=by
  have h:=selected_at issue i _ c move hit later unique
  exact ⟨congrArg Move.code h,congrArg Move.next h⟩

end
end Hierarchy.DescentSixParty.Chronology.RegisterTimeline

end OAI
