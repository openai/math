import OAI.Computability.BorderVNP.CoverAddressCoding
import OAI.Computability.BorderVNP.CoverDeckTower
import OAI.Computability.BorderVNP.ParseBatchVerifierCountWords

/-!
# Binary keys for sparse product-cover tables

A product residue is keyed by the concatenated canonical quaternion address
wires of its factors. Sorting records by these keys needs one row per residue
even when many binary keys do not encode a tile.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cover.AddressCircuit

open BorderVNP.StackFrame

/-- Width of the ordinary binary sort key for a product residue. -/
abbrev keyWidth (q d : ℕ) := q * (width d * 3)

/-- Fixed ordering of the product factor, quaternion position, and symbol. -/
def keySlots (q d : ℕ) : Fin q × Slots (width d) ≃ Fin (keyWidth q d) :=
  let symbol : Option Bool ≃ Fin 3 :=
    (Equiv.optionCongr finTwoEquiv.symm).trans (finSuccEquiv 2).symm
  let slot := (Equiv.prodCongr (Equiv.refl (Fin (width d))) symbol).trans finProdFinEquiv
  (Equiv.prodCongr (Equiv.refl (Fin q)) slot).trans finProdFinEquiv

/-- Flattened product-address wires in numerical sort order. -/
def keyWord (q d : ℕ) (x : Fin q → Deck d) (b : Fin (keyWidth q d)) : Bool :=
  let i := (keySlots q d).symm b
  deckWires d (x i.1) i.2

@[simp] theorem keyWord_slot (q d : ℕ) (x : Fin q → Deck d) (i : Fin q) (j : Slots (width d)) :
    keyWord q d x (keySlots q d (i,j)) = deckWires d (x i) j := by simp [keyWord]

/-- A sparse numerical key directly readable from the quaternion wires. -/
noncomputable def productKey (q d : ℕ) : (Fin q → Deck d) ↪ Fin (2^(keyWidth q d)) where
  toFun x := ParseBatchCounts.numberWords _ (keyWord q d x)
  inj' := by
    intro x y h
    have hword := (ParseBatchCounts.numberWords _).injective h
    funext i
    apply deckWires_injective
    funext j
    simpa using congrFun hword (keySlots q d (i,j))

@[simp] theorem encode_productKey (q d : ℕ) (x : Fin q → Deck d) :
    (ParseBatchCounts.numberWords _).symm (productKey q d x) = keyWord q d x := by
  exact (ParseBatchCounts.numberWords _).symm_apply_apply _

end Cover.AddressCircuit

end BorderVNP
end Computability
end OAI
