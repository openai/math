import OAI.Computability.BorderVNP.PackedSuppliedOffsetPhysical
import OAI.Computability.BorderVNP.DiagonalExternalFragmentStream

/-! # Physical ordering of the two crossing-end passes inside each supplied bank -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal.ExternalSew.Fragments

open Crossing Packing Packing.CellAddresses
open private endRow from OAI.Computability.BorderVNP.PackedCellAddresses
open private end_le_start from OAI.Computability.BorderVNP.PackedCellSlabs
open scoped Classical

variable {D C m n : ℕ} {P : Type*} {bits : P → ℕ} (N : Network D P bits)
    (cell : N.Site → Fin C) (edgeID : N.Edge ↪ Fin m) (portID : P ↪ Fin n)

/-- Source in pass zero or destination in pass one of an actual crossing wire. -/
def endpointCell (side : Bool) (e : N.CrossingEdge cell) : Fin C :=
  if side then cell (N.dst e.val) else cell (N.src e.val)

/-- The actual supplied-word index in the indicated receiving cell. -/
def endpointWord (c : Fin C) (side : Bool) (e : N.CrossingEdge cell)
    (here : endpointCell N cell side e = c) : Supplied N cell c :=
  .inl ⟨e,by cases side; exact Or.inl here; exact Or.inr here⟩

/-- Physical start of the word in the compact supplied slab of its endpoint's cell. -/
noncomputable def endpointRow [Fintype P] (side : Bool) (e : N.CrossingEdge cell) : ℕ :=
  let c := endpointCell N cell side e
  CellSlabs.start (suppliedRow N cell c edgeID portID) (suppliedWidth N cell c)
    (endpointWord N cell c side e rfl)

/-- The ordinal entering the slab prefix scan is exactly the sparse cable ID,
shifted by the whole source rectangle for a destination. -/
theorem endpointWord_id (c : Fin C) (side : Bool) (e : N.CrossingEdge cell)
    (here : endpointCell N cell side e = c) :
    suppliedRow N cell c edgeID portID (endpointWord N cell c side e here) =
      (if side then m else 0) + (edgeID e.val).val := by
  subst c
  cases side
  · let c := cell (N.src e.val)
    let b : Boundary N cell c := ⟨e,Or.inl rfl⟩
    have select : endRow N cell c edgeID b = .inl (edgeID e.val) := by simp [endRow,b,c]
    change (finSumFinEquiv (endRow N cell c edgeID b)).val = 0+(edgeID e.val).val
    rw [select,finSumFinEquiv_apply_left,Fin.val_castAdd,Nat.zero_add]
  · let c := cell (N.dst e.val)
    let b : Boundary N cell c := ⟨e,Or.inr rfl⟩
    have select : endRow N cell c edgeID b = .inr (edgeID e.val) := by simp [endRow,b,c,e.property]
    change (finSumFinEquiv (endRow N cell c edgeID b)).val = m+(edgeID e.val).val
    rw [select,finSumFinEquiv_apply_right,Fin.val_natAdd]

variable [Fintype P]

/-- Any proved common cell can be used to compare these dependent slab starts. -/
theorem endpointRow_at (c : Fin C) (side : Bool) (e : N.CrossingEdge cell)
    (here : endpointCell N cell side e = c) :
    endpointRow N cell edgeID portID side e =
      CellSlabs.start (suppliedRow N cell c edgeID portID) (suppliedWidth N cell c)
        (endpointWord N cell c side e here) := by subst c; rfl

/-- Two ordered physical endpoint row numbers give disjoint supplied intervals. -/
theorem endpointRow_le (a b : Bool) (e f : N.CrossingEdge cell)
    (same : endpointCell N cell a e = endpointCell N cell b f)
    (lt : (if a then m else 0)+(edgeID e.val).val < (if b then m else 0)+(edgeID f.val).val) :
    endpointRow N cell edgeID portID a e + N.width e.val ≤ endpointRow N cell edgeID portID b f := by
  let c := endpointCell N cell b f
  let first := endpointWord N cell c a e same
  let last := endpointWord N cell c b f rfl
  have order : suppliedRow N cell c edgeID portID first < suppliedRow N cell c edgeID portID last := by
    rw [endpointWord_id,endpointWord_id]
    exact lt
  rw [endpointRow_at N cell edgeID portID c a e same]
  exact end_le_start (suppliedRow N cell c edgeID portID) (suppliedWidth N cell c) order

/-- All source rows in a cell precede all destination rows in that cell. -/
theorem endpoint_source_before_dest (e f : N.CrossingEdge cell)
    (same : endpointCell N cell false e = endpointCell N cell true f) :
    endpointRow N cell edgeID portID false e + N.width e.val ≤ endpointRow N cell edgeID portID true f := by
  apply endpointRow_le N cell edgeID portID false true e f same
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.zero_add] using
    (edgeID e.val).isLt.trans_le (Nat.le_add_right m (edgeID f.val).val)

/-- The entire cable word lies inside the actual supplied bank of its receiving cell. -/
theorem endpointRow_fits (side : Bool) (e : N.CrossingEdge cell) :
    endpointRow N cell edgeID portID side e + N.width e.val ≤ suppliedSize N cell (endpointCell N cell side e) := by
  let c := endpointCell N cell side e
  let u := endpointWord N cell c side e rfl
  have h := CellSlabs.end_le_capacity (suppliedRow N cell c edgeID portID) (suppliedWidth N cell c) u
  refine h.trans_eq ?_
  unfold suppliedSize
  apply Finset.sum_congr _ (fun _ _ => rfl)
  exact congrArg (@Fintype.elems _) (Subsingleton.elim _ _)

end Diagonal.ExternalSew.Fragments

end BorderVNP
end Computability
end OAI
