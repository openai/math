import OAI.Computability.BorderVNP.FiniteLocalCellFactors
import OAI.Computability.BorderVNP.PackedBottomBoxInterpreter
import OAI.Computability.BorderVNP.PackedGridBoxRead
import OAI.Computability.BorderVNP.PackedBottomBoxValue

/-! # Finite scalar table positions on the concrete fine grid slab

Each retained fine site stores the genuine finite field row IDs and the
physical within-cell guessed or supplied lane of every input bit. Zero is
a valid scalar entry, and a zero-input site still stores its one table row.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.FiniteBottom

open Crossing CellSparse CellAddresses GridBoxes Inherited
open scoped BigOperators Classical

variable {D m n s : ℕ} {P C : Type} [Fintype P] {bits : P → ℕ}
  (N : Network D P bits) (cell : N.Site → C) (v : C)
  (siteID : N.Site ↪ Fin s) (edgeID : N.Edge ↪ Fin m) (portID : P ↪ Fin n)
  {F : Type*} [Field F] [Fintype F]

/-- Actual field scalar at an allocated finite table ID. -/
noncomputable def scalarValue (F : Type*) [Field F] [Fintype F] : ℕ → F :=
  FieldPowers.entry (Fintype.equivFin F).symm

/-- Encoding and reading a finite field element also recovers the value zero. -/
theorem scalarValue_code (a : F) : scalarValue F (Fintype.equivFin F a).val = a := by
  simp [scalarValue,FieldPowers.entry]

/-- Physical fine lanes in the exact order used by the little-endian row directory. -/
noncomputable def scalarAddresses (z : {i : N.Site // cell i = v}) : List ℕ :=
  List.ofFn fun i : Fin (Fintype.card (FieldDirectory.Lane N z.val)) =>
    (lane N cell v edgeID portID z ((Fintype.equivFin _).symm i)).val

/-- One immutable gadget factor for a fine site, storing the true field row IDs. -/
noncomputable def scalarFactor (T : N.Tables F) (z : {i : N.Site // cell i = v}) : Factor :=
  .gadget (scalarAddresses N cell v edgeID portID z) (FieldDirectory.rowIds N T z.val)

/-- The single-copy directory lists every retained fine site in physical site-name order. -/
noncomputable def scalarFactors (T : N.Tables F) : List Factor :=
  (siteList N cell v siteID).map (scalarFactor N cell v edgeID portID T)

omit [Field F] in
/-- Reading a sparse site selects exactly the row indexed by its current fine
lanes, at the supplied absolute offset and copy number. -/
theorem observe_scalarFactor (T : N.Tables F) (z : {i : N.Site // cell i = v})
    (bank : ℕ → Bool) (off copy : ℕ) :
    (scalarFactor N cell v edgeID portID T z).observe bank off copy =
      some (false,some (Fintype.equivFin F (CellBox.localRow N T z.val
        (fun l => bank (off+(lane N cell v edgeID portID z l).val)))).val) := by
  let wires := (scalarAddresses N cell v edgeID portID z).map (off+·)
  let j := word bank wires
  have len : wires.length = Fintype.card (FieldDirectory.Lane N z.val) := by
    simp [wires,scalarAddresses]
  have hj : j < 2^Fintype.card (FieldDirectory.Lane N z.val) := len ▸ word_bound bank wires
  have digit (l : FieldDirectory.Lane N z.val) :
      j.testBit (Fintype.equivFin (FieldDirectory.Lane N z.val) l).val =
        bank (off+(lane N cell v edgeID portID z l).val) := by
    have h := word_digit bank wires (Fintype.equivFin (FieldDirectory.Lane N z.val) l).val
      (len.symm ▸ (Fintype.equivFin _ l).isLt)
    simpa [wires,scalarAddresses,j] using h
  unfold scalarFactor Factor.observe
  change (FieldDirectory.rowIds N T z.val)[j]?.map _ = _
  rw [List.getElem?_eq_getElem (by simpa [FieldDirectory.rowIds] using hj)]
  simp only [FieldDirectory.rowIds,List.getElem_ofFn,Option.map_some,FieldDirectory.row,
    CellBox.localRow,digit]

omit [Field F] in
/-- The complete immutable scalar portion can never reject due to a missing field entry. -/
theorem scalarFactors_present (T : N.Tables F) (bank : ℕ → Bool) (off copy : ℕ) :
    ∀ f ∈ scalarFactors N cell v siteID edgeID portID T, (f.observe bank off copy).isSome = true := by
  intro f hf
  obtain ⟨z,_,rfl⟩ := List.mem_map.mp hf
  simp [observe_scalarFactor]

/-- Reading the encoded scalar at a copy's real bank position gives its original
table value on the concatenated fine guessed and supplied bits. -/
theorem read_scalarFactor (T : N.Tables F) (z : {i : N.Site // cell i = v}) (bank : ℕ → Bool) (off copy : ℕ)
    (g : Fin (guessedSize N cell v) → Bool) (x : Fin (suppliedSize N cell v) → Bool)
    (h : ∀ i : Fin (stride N cell v), bank (off+i.val) = copyBits N cell v g x i)
    (values : ℕ → F) (lookup : ∀ a : F, values (Fintype.equivFin F a).val = a) :
    ((scalarFactor N cell v edgeID portID T z).observe bank off copy).elim 0
      (fieldEntry values) =
      T z.val (fun e k => (wire N cell v edgeID portID z e k).elim g x)
        (fun p k => x (port N cell v edgeID portID z p k)) := by
  rw [observe_scalarFactor]
  simp only [fieldEntry, Bool.false_eq_true, ite_false, Option.elim_some, one_mul, lookup, CellBox.localRow]
  congr 1 <;> funext e k <;> rw [h] <;>
    simp only [GridBoxes.lane,copyBits,Equiv.symm_apply_apply,Sum.elim_inr]

omit [Fintype P] in
private theorem siteList_prod {Y : Type*} [CommMonoid Y] (f : {i : N.Site // cell i = v} → Y) :
    ((siteList N cell v siteID).map f).prod = ∏ i, f i := by
  let order := (Function.Embedding.subtype (fun i => cell i = v)).trans siteID
  let := LinearOrder.lift' order order.injective
  let e := (Fintype.orderIsoFinOfCardEq {i : N.Site // cell i = v} rfl).toEquiv
  change ((List.ofFn e).map f).prod = _
  rw [List.map_ofFn,List.prod_ofFn]
  exact e.prod_comp f

/-- Every fine site is visited once in the ordinary field product of an immutable copy. -/
theorem scalarFactors_product (T : N.Tables F) (bank : ℕ → Bool) (off copy : ℕ)
    (g : Fin (guessedSize N cell v) → Bool) (x : Fin (suppliedSize N cell v) → Bool)
    (h : ∀ i : Fin (stride N cell v), bank (off+i.val) = copyBits N cell v g x i)
    (values : ℕ → F) (lookup : ∀ a : F, values (Fintype.equivFin F a).val = a) :
    ((scalarFactors N cell v siteID edgeID portID T).map (fun f =>
      (f.observe bank off copy).elim 0 (fieldEntry values))).prod =
      CellAddresses.factor N cell v edgeID portID T g x := by
  rw [scalarFactors,List.map_map,siteList_prod]
  exact Finset.prod_congr rfl fun z _ => read_scalarFactor N cell v edgeID portID T z bank off copy g x h values lookup

end Packing.FiniteBottom

end BorderVNP
end Computability
end OAI
