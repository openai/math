import OAI.Computability.VPVNP.CompressorRecordPreimageScan
import OAI.Computability.VPVNP.PackingPreimages
import Mathlib.Data.Nat.Count

/-!
# Typed placement fibers in the physical descriptor table

Numbering sites transports the placement function to words in the old-site array. A full
preimage scan stores precisely the old identifiers mapping to each new owner. The number
of records in that row equals the cardinality of the original placement fiber, so the
native scan's capacity condition follows directly from the combinatorial bound.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords

open BurstRAM
open scoped Count

variable {w : ℕ}

/-- Size of the physical prefix list equals the size of the filtered ordinal set. -/
theorem preimagePrefix_card (place : Word w → Word w) (owner : Word w) (k : ℕ) :
    (preimagePrefix place owner k).length =
      Fintype.card {i : Fin k // place (Fin.ofNat (2 ^ w) i.val) = owner} := by
  let P (i : ℕ) := place (Fin.ofNat (2 ^ w) i) = owner
  have hc : (preimagePrefix place owner k).length = Nat.count P k := by
    simp [preimagePrefix, ← List.countP_eq_length_filter, List.countP_map, Nat.count, P, Function.comp_def]
    congr 1
  rw [hc, Nat.count_eq_card_fintype]
  apply Fintype.card_congr
  exact ⟨fun i => ⟨⟨i.val, i.prop.1⟩, i.prop.2⟩,
    fun i => ⟨i.val.val, i.val.prop, i.prop⟩, fun _ => rfl, fun _ => rfl⟩

variable {Old New : Type*} {oldCount newCount : ℕ}

/-- Read a placement as numeric identifiers in the chosen site order. -/
def encodedPlacement (oldOrder : Old ≃ Fin oldCount) (newOrder : New ≃ Fin newCount)
    (place : Old → New) (i : Word w) : Word w :=
  if h : i.val < oldCount then Fin.ofNat (2 ^ w) (newOrder (place (oldOrder.symm ⟨i.val, h⟩))).val
  else 0

theorem encodedPlacement_eq (oldOrder : Old ≃ Fin oldCount) (newOrder : New ≃ Fin newCount)
    (place : Old → New) (ho : oldCount ≤ 2^w) (hn : newCount ≤ 2^w) (j : Fin oldCount) :
    (encodedPlacement oldOrder newOrder place (Fin.ofNat (2^w) j.val)).val =
      (newOrder (place (oldOrder.symm j))).val := by
  simp [encodedPlacement, Nat.mod_eq_of_lt (j.isLt.trans_le ho),
    Nat.mod_eq_of_lt ((newOrder (place (oldOrder.symm j))).isLt.trans_le hn)]

/-- The preimage bound on the mathematical layout is the exact length of the
corresponding physical row. This also applies to repeated role occurrences by
numbering the occurrences themselves. -/
theorem encodedPlacement_rowLength (oldOrder : Old ≃ Fin oldCount) (newOrder : New ≃ Fin newCount)
    (place : Old → New) (ho : oldCount ≤ 2^w) (hn : newCount ≤ 2^w) (v : New)
    [Fintype Old] [DecidableEq New] :
    (preimagePrefix (encodedPlacement oldOrder newOrder place)
      (Fin.ofNat (2 ^ w) (newOrder v).val) oldCount).length =
      Fintype.card {u : Old // place u = v} := by
  rw [preimagePrefix_card]
  let target := Fin.ofNat (2 ^ w) (newOrder v).val
  have ht : target.val = (newOrder v).val := Nat.mod_eq_of_lt ((newOrder v).isLt.trans_le hn)
  have hg (j : Fin oldCount) :
      encodedPlacement oldOrder newOrder place (Fin.ofNat (2 ^ w) j.val) = target ↔
      place (oldOrder.symm j) = v := by
    rw [Fin.ext_iff, encodedPlacement_eq oldOrder newOrder place ho hn j, ht]
    exact Fin.val_injective.eq_iff.trans newOrder.injective.eq_iff
  apply Fintype.card_congr
  exact {
    toFun := fun i => ⟨oldOrder.symm i.val, (hg _).mp i.prop⟩
    invFun := fun u => ⟨oldOrder u.val, (hg _).mpr (by simpa using u.prop)⟩
    left_inv := fun i => Subtype.ext (oldOrder.apply_symm_apply i.val)
    right_inv := fun u => Subtype.ext (oldOrder.symm_apply_apply u.val) }

end CompressorRecords

end VPVNP
end Computability
end OAI
