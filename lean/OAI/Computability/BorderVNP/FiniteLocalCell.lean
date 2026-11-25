import OAI.Computability.BorderVNP.FiniteCellDirectory
import OAI.Computability.BorderVNP.DiagonalInitialGridCells

/-! # A private component at one public cell of the finite-field construction

Its sites and private cables are exactly the fine sites and whole cables inside
the cell. A crossing cable has one local port, at its endpoint in this cell.
All remaining local ports are the original external inputs attached here.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace FiniteLocalCell

open Crossing
open scoped BigOperators Classical

variable {D : ℕ} {P : Type} [Fintype P] {bits : P → ℕ} (N : Network D P bits)
    {Cell : Type} [Fintype Cell] [DecidableEq Cell] (cell : N.Site → Cell) (c : Cell)

/-- An endpoint of a crossing cable at this cell. A crossing has only one such endpoint here. -/
abbrev Boundary := {e : N.CrossingEdge cell // cell (N.src e.val) = c ∨ cell (N.dst e.val) = c}

/-- An original externally supplied port attached to a fine site inside this cell. -/
abbrev External := {p : P // cell (N.attach p) = c}

/-- Locally supplied crossing cables and original ports. -/
abbrev Port := Boundary N cell c ⊕ External N cell c

/-- The supplied words retain their original widths. -/
def portWidth : Port N cell c → ℕ :=
  Sum.elim (fun e => N.width e.val.val) (fun p => bits p.val)

/-- The one endpoint of a crossing edge lying inside the cell. -/
def endpoint (e : Boundary N cell c) : {v : N.Site // cell v = c} :=
  if hs : cell (N.src e.val.val) = c then ⟨N.src e.val.val,hs⟩
  else ⟨N.dst e.val.val,e.property.resolve_left hs⟩

/-- A tensor network for just one local box, before summing its fine private
cable words. Its internal assignment type is the cell's exact InsideAssignment. -/
abbrev network : Network D (Port N cell c) (portWidth N cell c) where
  Site := {v : N.Site // cell v = c}
  Edge := N.InsideEdge cell c
  finiteSite := inferInstance
  finiteEdge := inferInstance
  src e := ⟨N.src e.val,e.property.1⟩
  dst e := ⟨N.dst e.val,e.property.2⟩
  width e := N.width e.val
  attach := Sum.elim (endpoint N cell c) (fun p => ⟨N.attach p.val,p.property⟩)
  position v := N.position v.val
  in_ball v := N.in_ball v.val

/-- The external data at this box is precisely its incident crossing words
and attached original port words. -/
def ports (a : ∀ e : Boundary N cell c, Fin (N.width e.val.val) → Bool)
    (x : ∀ p : External N cell c, Fin (bits p.val) → Bool) : Ports (portWidth N cell c) :=
  fun q => match q with
    | .inl e => a e
    | .inr p => x p

omit [Fintype P] [Fintype Cell] in
/-- The local endpoint of the crossing cable agrees with the fine site that reads it. -/
private theorem endpoint_eq (v : {v : N.Site // cell v = c}) (e : N.Edge)
    (cross : cell (N.src e) ≠ cell (N.dst e)) (hv : N.src e = v.val ∨ N.dst e = v.val) :
    endpoint N cell c ⟨⟨e,cross⟩,hv.imp (fun h => (congrArg cell h).trans v.property)
      (fun h => (congrArg cell h).trans v.property)⟩ = v := by
  apply Subtype.ext
  rcases hv with hs | hd
  · simp only [endpoint,dite_eq_left ((congrArg cell hs).trans v.property)]
    exact hs
  · have hn : cell (N.src e) ≠ c := fun hs => cross (hs.trans ((congrArg cell hd).trans v.property).symm)
    simp only [endpoint,dite_eq_right hn]
    exact hd

/-- Restrict each fine table to the local network. An edge that stays in
the cell reads a private cable. Every other incident fine edge reads the
external word at its unique crossing port. -/
noncomputable def tables {A : Type*} (table : N.Tables A) : (network N cell c).Tables A :=
  fun v a x => table v.val (fun e =>
    if h : cell (N.src e.val) = cell (N.dst e.val) then
      let ends := e.property.imp (fun hs => (congrArg cell hs).trans v.property)
        (fun hd => (congrArg cell hd).trans v.property)
      let hs := ends.elim id (h.trans ·)
      a ⟨⟨e.val,hs,h.symm.trans hs⟩, e.property.imp (fun hh => Subtype.ext hh) (fun hh => Subtype.ext hh)⟩
    else
      x ⟨.inl ⟨⟨e.val,h⟩,e.property.imp (fun hs => (congrArg cell hs).trans v.property)
        (fun hd => (congrArg cell hd).trans v.property)⟩, endpoint_eq N cell c v _ h e.property⟩)
    (fun p => x ⟨.inr ⟨p.val,(congrArg cell p.property).trans v.property⟩,Subtype.ext p.property⟩)

omit [Fintype P] in
/-- The complete local contraction, with exactly its local assignments and
boundary lanes, equals the corresponding polynomial or field entry in the
aggregated physical cell table. -/
theorem value_eq_cellTables {A : Type*} [CommSemiring A]
    (position : Cell → {v : EuclideanSpace ℝ (Fin D) // ‖v‖ ≤ 1})
    (table : N.Tables A) (a x) :
    (network N cell c).value (tables N cell c table) (ports N cell c a x) =
      N.cellTables cell position table c a x := by
  unfold Network.value Network.cellTables
  apply Finset.sum_congr (Finset.ext fun _ => by simp)
  intro z _
  apply Finset.prod_congr (Finset.ext fun _ => by simp)
  intro v _
  apply congrArg (fun e => table v.val e (fun p => x ⟨p.val,(congrArg cell p.property).trans v.property⟩))
  funext e
  by_cases h : cell (N.src e.val) = cell (N.dst e.val) <;> simp [h,ports]

end FiniteLocalCell

end BorderVNP
end Computability
end OAI
