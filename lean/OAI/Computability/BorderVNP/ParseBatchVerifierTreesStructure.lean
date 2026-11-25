import OAI.Computability.BorderVNP.ParseBatchVerifierTreesAssembly
import OAI.Computability.BorderVNP.ParseBatchCheckPacked

/-! # Structure validity on raw bit arrays, field arrays and decoded record lists -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace ParseBatchTrees

open VPVNP BorderVNP.ParseRecords

variable {m g n rows : ℕ}

/-- The typed array produced by successful per-row decoding agrees with the decoded
record list in the same physical order. -/
theorem readBlock_of_rows (bs : Fin rows → BitSlot (recordWidth m g n) → Bool)
    (a : Fin rows → GrammarLabel (Fin m × Bool) (Fin g) n)
    (ha : ∀ i, unpack m g n (fieldsOfBits (bs i)) = some (a i)) :
    readBlock m g n (List.ofFn bs) = some (List.ofFn a) := by
  rw [readBlock_eq_some_iff, List.map_ofFn]
  exact congrArg List.ofFn (funext (fun i => unpack_bits_iff.mp (ha i)))

/-- Reading the raw bit block gives exactly the decoded typed array and its
per-slot canonical format checks. -/
theorem readBlock_iff_rows (bs : Fin rows → BitSlot (recordWidth m g n) → Bool)
    (rs : List (GrammarLabel (Fin m × Bool) (Fin g) n)) :
    readBlock m g n (List.ofFn bs) = some rs ↔
      ∃ a : Fin rows → GrammarLabel (Fin m × Bool) (Fin g) n,
        rs = List.ofFn a ∧ ∀ i, unpack m g n (fieldsOfBits (bs i)) = some (a i) := by
  constructor
  · intro h
    have hc := readBlock_eq_some_iff.mp h
    have hl : rows = rs.length := by simpa using congrArg List.length hc
    let a (i : Fin rows) := rs[i.val]'(hl ▸ i.isLt)
    have he : rs = List.ofFn a := by
      symm
      apply List.ext_getElem
      · simpa using hl
      · intro j hj hk; simp only [List.getElem_ofFn, a]
    rw [he, List.map_ofFn] at hc
    exact ⟨a, he, fun i => unpack_bits_iff.mpr (congrFun (List.ofFn_injective hc) i)⟩
  · rintro ⟨a, rfl, ha⟩
    exact readBlock_of_rows bs a ha

/-- The same structure predicate using an array of labels and explicit local
decoding instead of the list decoder. -/
theorem structure_iff_rows (d : Fin n) (h : Fin g)
    (bs : Fin (2*d.val+1) → BitSlot (recordWidth m g n) → Bool) :
    Structure d h bs ↔
      ∃ a : Fin (2*d.val+1) → GrammarLabel (Fin m × Bool) (Fin g) n,
        (∀ i, unpack m g n (fieldsOfBits (bs i)) = some (a i)) ∧ Valid d h (List.ofFn a) := by
  constructor
  · rintro ⟨rs, hd, hv⟩
    obtain ⟨a, rfl, ha⟩ := (readBlock_iff_rows bs rs).mp hd
    exact ⟨a, ha, hv⟩
  · rintro ⟨a, ha, hv⟩
    exact ⟨List.ofFn a, readBlock_of_rows bs a ha, hv⟩

private theorem read_fields (bits : List (BitSlot (recordWidth m g n) → Bool)) :
    unpackRows m g n (bits.map fieldsOfBits) = readBlock m g n bits := by
  induction bits with
  | nil => rfl
  | cons b bs ih =>
    simp only [List.map_cons, unpackRows, readBlock, List.mapM_cons] at ih ⊢
    rw [ih]
    cases unpack m g n (fieldsOfBits b) <;>
      cases bs.mapM (fun b => unpack m g n (fieldsOfBits b)) <;> rfl

/-- The executable packed structure checker has the precise raw-bit acceptance
predicate needed for composing with the leaf circuit. -/
theorem structure_iff_checkPacked (d : Fin n) (h : Fin g)
    (bs : Fin (2*d.val+1) → BitSlot (recordWidth m g n) → Bool) :
    Structure d h bs ↔ checkPacked m d h (List.ofFn (fieldsOfBits ∘ bs)) = true := by
  rw [checkPacked, ← List.map_ofFn, read_fields, Option.any_eq_true]
  simp only [check_iff_valid, Structure]

end ParseBatchTrees

end BorderVNP
end Computability
end OAI
