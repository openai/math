import OAI.Computability.BorderVNP.PackedCellAddresses
import OAI.Computability.BorderVNP.CrossingCellBox
import OAI.Computability.BorderVNP.CellDirectoryWire

/-! # Private one-copy factors for the initial cells

Boolean rows and selected unary uses are read directly from the fine site's wire lanes.
Each lane points into the concatenation of the cell's private guessed wires and its
supplied boundary/port bits. Copy visits reuse one stored factor at the advertised stride.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.GridBoxes

open Crossing CellSparse CellAddresses
open scoped Classical
variable {D : ℕ} {P : Type} [Fintype P] {bits : P → ℕ} (N : Network D P bits)
variable {C : Type} (cell : N.Site → C) (c : C)
variable {m n : ℕ} (edgeID : N.Edge ↪ Fin m) (portID : P ↪ Fin n)

/-- The private guessed slab followed by the cell's supplied arguments. -/
noncomputable def stride := guessedSize N cell c + suppliedSize N cell c

/-- An individual fine input has one actual relative address within this cell copy. -/
noncomputable def lane (v : {v : N.Site // cell v = c}) :
    CellBox.Lane N v.val → Fin (stride N cell c)
  | .inl ⟨e,k⟩ => finSumFinEquiv (wire N cell c edgeID portID v e k)
  | .inr ⟨p,k⟩ => finSumFinEquiv (.inr (port N cell c edgeID portID v p k))

/-- The bank of a cell copy is obtained by concatenation, so that a shared internal
wire always reads the same bit at its two endpoints. -/
noncomputable def copyBits (g : Fin (guessedSize N cell c) → Bool)
    (x : Fin (suppliedSize N cell c) → Bool) (i : Fin (stride N cell c)) : Bool :=
  (finSumFinEquiv.symm i).elim g x

/-- A Boolean check is a local table. A unary factor tests its actual selected wire
against the use bit supplied for this copy in the external report. -/
inductive Rule (N : Network D P bits) (v : N.Site) where
  | truth (table : (CellBox.Lane N v → Bool) → Bool)
  | unary (selected : CellBox.Lane N v) (report : Port)

/-- Truth-table rows in little-endian lane order, with the empty-input row included. -/
noncomputable def boolRows {L : Type} {d : ℕ} (order : L ≃ Fin d) (f : (L → Bool) → Bool) : List Bool :=
  List.ofFn fun k : Fin (2^d) => f (fun l => finTwoEquiv (finFunctionFinEquiv.symm k (order l)))

/-- Actual private factor passed to the sparse cell reader. The source order and
relative addresses are fixed independently of the copy count. -/
noncomputable def ruleFactor (v : {v : N.Site // cell v = c})
    (order : CellBox.Lane N v.val ≃ Fin (Fintype.card (CellBox.Lane N v.val))) :
    Rule N v.val → Factor
  | .truth f => .truth (List.ofFn fun i => (lane N cell c edgeID portID v (order.symm i)).val)
      (boolRows order f)
  | .unary l report => .unary (lane N cell c edgeID portID v l).val report

/-- Truth of the private factor on an actual assignment at the given offset and copy. -/
noncomputable def accepts (v : {v : N.Site // cell v = c}) (bank : ℕ → Bool) (off copy : ℕ) :
    Rule N v.val → Bool
  | .truth f => f (fun l => bank (off+(lane N cell c edgeID portID v l).val))
  | .unary l report => bank (off+(lane N cell c edgeID portID v l).val) == bank (report.atBit copy 0)

/-- The local sparse reader passes exactly the specified Boolean table or unary use
check at the physical addresses. Such initial factors have neither a sign nor a gadget ID. -/
theorem observe_rule (v : {v : N.Site // cell v = c})
    (order : CellBox.Lane N v.val ≃ Fin (Fintype.card (CellBox.Lane N v.val)))
    (a : Rule N v.val) (bank : ℕ → Bool) (off copy : ℕ) :
    (ruleFactor N cell c edgeID portID v order a).observe bank off copy =
      if accepts N cell c edgeID portID v bank off copy a then some (false,none) else none := by
  cases a with
  | unary l report => simp [ruleFactor,Factor.observe,accepts]
  | truth f =>
    let addr (i) := (lane N cell c edgeID portID v (order.symm i)).val
    let bs (i) := finTwoEquiv.symm (bank (off+addr i))
    let row := finFunctionFinEquiv bs
    have hw : word bank ((List.ofFn addr).map (off + ·)) = row.val := by
      rw [List.map_ofFn]
      exact CellSparse.word_ofFn _ _
    have hf : (boolRows order f)[row.val]? = some (f fun l => bank (off+(lane N cell c edgeID portID v l).val)) := by
      rw [List.getElem?_eq_getElem (by simpa only [boolRows,List.length_ofFn] using row.isLt)]
      simp only [boolRows,List.getElem_ofFn,Fin.eta,row,bs,addr,Equiv.symm_apply_apply,Equiv.apply_symm_apply]
    change (if (boolRows order f)[word bank ((List.ofFn addr).map (off + ·))]? = some true
      then some (false,none) else none) = _
    rw [hw,hf]
    cases hb : f (fun l => bank (off+(lane N cell c edgeID portID v l).val)) <;> simp [accepts,hb]

/-- The serialized one-copy factor uses at most fourteen scalar words at degree three.
Unary uses need one relative wire address and the three fields of the report port. -/
theorem factor_words_le (v : {v : N.Site // cell v = c})
    (order : CellBox.Lane N v.val ≃ Fin (Fintype.card (CellBox.Lane N v.val)))
    (degree : Fintype.card (CellBox.Lane N v.val) ≤ 3) (a : Rule N v.val) :
    (Packet.factor (ruleFactor N cell c edgeID portID v order a)).length ≤ 14 := by
  cases a with
  | unary => simp [Packet.factor,Packet.port,ruleFactor]
  | truth =>
    have hh := Nat.pow_le_pow_right (by decide : 0 < 2) degree
    simp only [Packet.factor,Packet.vector,ruleFactor,boolRows,List.length_append,List.length_cons,
      List.length_nil,List.length_map,List.length_ofFn]
    omega

end Packing.GridBoxes

end BorderVNP
end Computability
end OAI
