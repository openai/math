import OAI.Computability.BorderVNP.FiniteCellEntries
import OAI.Computability.BorderVNP.CellReportedWord
import OAI.Computability.BorderVNP.CrossingNetwork

/-! # Physical sparse entries for a finite-field bit network

Both ends of each internal lane read one and the same bank address. The local
row number follows the little-endian convention of the private cell checker.
Every scalar, including zero, is stored as an ordinary finite-field position.
A degree-three site with unit lanes therefore needs at most eight positions.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace FieldDirectory

open Crossing CellSparse
open scoped Classical BigOperators

variable {D : ℕ} {P : Type} [Fintype P] {bits : P → ℕ} (N : Network D P bits)

/-- A bit of an original internal cable or one external port. -/
abbrev Wire := (Σ e : N.Edge, Fin (N.width e)) ⊕ (Σ p : P, Fin (bits p))

/-- Number the private cable bits first, followed by the externally supplied
terminal bits. The field table reader and the sparse macro use this same order. -/
noncomputable def wireNumber : Wire N ≃ Fin (Fintype.card (Wire N)) :=
  ((Equiv.sumCongr (Fintype.equivFin _) (Fintype.equivFin _)).trans finSumFinEquiv).trans
    (finCongr (Fintype.card_sum ..).symm)

/-- Private bit positions form the initial interval of the assignment bank. -/
theorem number_internal (e : Σ k : N.Edge, Fin (N.width k)) :
    (wireNumber N (.inl e)).val = (Fintype.equivFin _ e).val := rfl

/-- Supplied port values immediately follow all private cable bits. -/
theorem number_external (p : Σ k : P, Fin (bits k)) :
    (wireNumber N (.inr p)).val = Fintype.card (Σ k : N.Edge, Fin (N.width k)) +
      (Fintype.equivFin _ p).val := rfl

/-- Original lanes incident to a site, in the domain of its local table. -/
abbrev Lane (s : N.Site) :=
  (Σ e : {e : N.Edge // N.src e = s ∨ N.dst e = s}, Fin (N.width e.val)) ⊕
  (Σ p : {p : P // N.attach p = s}, Fin (bits p.val))

/-- The endpoint and external port restrictions name a bit without copying it. -/
def wire (s : N.Site) : Lane N s → Wire N
  | .inl ⟨e,j⟩ => .inl ⟨e.val,j⟩
  | .inr ⟨p,j⟩ => .inr ⟨p.val,j⟩

/-- Fixed scalar-independent addresses of the one-copy lane names. -/
noncomputable def addresses (s : N.Site) : List ℕ :=
  List.ofFn fun i : Fin (Fintype.card (Lane N s)) => (wireNumber N (wire N s ((Fintype.equivFin (Lane N s)).symm i))).val

/-- One row of the literal site table, with all incidence and port bits decoded. -/
noncomputable def row {F : Type*} (table : N.Tables F) (s : N.Site) (k : ℕ) : F :=
  table s (fun e j => k.testBit (Fintype.equivFin (Lane N s) (.inl ⟨e,j⟩)).val)
    (fun p j => k.testBit (Fintype.equivFin (Lane N s) (.inr ⟨p,j⟩)).val)

variable {F : Type*} [Fintype F]

/-- Literal field-code positions, ordered by the private checker's row numbering. -/
noncomputable def rowIds (table : N.Tables F) (s : N.Site) : List ℕ :=
  List.ofFn fun i : Fin (2^Fintype.card (Lane N s)) => (Fintype.equivFin F (row N table s i.val)).val

/-- One stored sparse factor for an actual input site. -/
noncomputable def factor (table : N.Tables F) (s : N.Site) : Factor := .gadget (addresses N s) (rowIds N table s)

/-- The private store bound for a site having at most three incident bits. -/
theorem literal_size (table : N.Tables F) (s : N.Site) (h : Fintype.card (Lane N s) ≤ 3) :
    (addresses N s).length ≤ 3 ∧ (rowIds N table s).length ≤ 8 :=
  ⟨by simpa [addresses] using h, by simpa [rowIds] using Nat.pow_le_pow_right (by decide : 0 < 2) h⟩

/-- One physical bank carries all selected cable bits and supplied external port bits.
Unused addresses can be used by the verifier for independent auxiliary fields. -/
noncomputable def bank (a : N.Assignment) (x : Ports bits) (tail : ℕ → Bool) (j : ℕ) : Bool :=
  if h : j < Fintype.card (Wire N) then
    match (wireNumber N).symm ⟨j,h⟩ with
    | .inl ⟨e,i⟩ => a e i
    | .inr ⟨p,i⟩ => x p i
  else tail j

omit [Fintype F] in
/-- The two ends of a cable and the attached external ports all read their
original values at the address selected by the row encoding. -/
theorem row_read (a : N.Assignment) (x : Ports bits) (tail : ℕ → Bool) (table : N.Tables F) (s : N.Site) :
    row N table s (word (bank N a x tail) (addresses N s)) = N.read table a x s := by
  have digit (u : Lane N s) :
      (word (bank N a x tail) (addresses N s)).testBit (Fintype.equivFin (Lane N s) u).val =
      bank N a x tail (wireNumber N (wire N s u)).val := by
    have hu := (Fintype.equivFin (Lane N s) u).isLt
    rw [word_digit _ _ _ (by simpa only [addresses,List.length_ofFn] using hu)]
    simp [addresses]
  have atWire (u : Wire N) : bank N a x tail (wireNumber N u).val =
      u.elim (fun e => a e.1 e.2) (fun p => x p.1 p.2) := by
    rw [bank,dite_eq_left (wireNumber N u).isLt,Fin.eta,Equiv.symm_apply_apply]
    cases u <;> rfl
  unfold row Network.read
  simp only [digit,atWire,wire,Sum.elim_inl,Sum.elim_inr]

/-- The actual sparse checker returns precisely the original field table position.
This remains a successful observation when the associated scalar equals zero. -/
theorem observe_factor (table : N.Tables F) (s : N.Site) (a : N.Assignment) (x : Ports bits) (tail : ℕ → Bool) (copy : ℕ) :
    (factor N table s).observe (bank N a x tail) 0 copy = some (false, some (Fintype.equivFin F (N.read table a x s)).val) := by
  let j := word (bank N a x tail) (addresses N s)
  have hj : j < 2^Fintype.card (Lane N s) := by simpa only [j,addresses,List.length_ofFn] using word_bound (bank N a x tail) (addresses N s)
  simp only [factor,Factor.observe,Nat.zero_add]
  rw [show (fun z : ℕ => z) = id from rfl,List.map_id]
  have hr : (rowIds N table s)[j]? = some (Fintype.equivFin F (row N table s j)).val := by
    rw [List.getElem?_eq_getElem (by simpa only [rowIds,List.length_ofFn] using hj)]
    simp only [rowIds,List.getElem_ofFn]
  rw [hr]
  simp [j,row_read]

end FieldDirectory

end BorderVNP
end Computability
end OAI
