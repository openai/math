import OAI.Computability.VPVNP.RAMSerialization

/-!
# Consecutive record intervals in a sorting exchange

Each site sends a block of `4H` five-word records. A validator can parse and
check its incident sorting field one record at a time, by reading the bit
interval beginning at offset `i * 5 * w`. This gives the same records and
canonicality check as the serialized block format.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RAMSerialization

/-- The physical interval occupied by the five words of the `i`th record. -/
def recordSlice (H w : ℕ) (bits : Fin (RAMLayout.blockBits H w) → Bool) (i : Fin (4 * H))
    (j : Fin (5 * w)) : Bool :=
  bits ⟨i.val * 5 * w + j.val, by
    calc
      i.val * 5 * w + j.val < (i.val + 1) * (5 * w) := by
        rw [Nat.add_mul, Nat.one_mul, Nat.mul_assoc]
        exact Nat.add_lt_add_left j.isLt _
      _ ≤ (4 * H) * (5 * w) := Nat.mul_le_mul_right _ i.isLt
      _ = RAMLayout.blockBits H w := (Nat.mul_assoc ..).symm⟩

theorem recordSlice_at (H w : ℕ) (bits : Fin (RAMLayout.blockBits H w) → Bool) (i : Fin (4 * H))
    (j : Fin 5) (t : Fin w) :
    recordSlice H w bits i (finProdFinEquiv (j, t)) =
      bits (finProdFinEquiv (finProdFinEquiv (i, j), t)) := by
  apply congrArg bits
  apply Fin.ext
  change i.val * 5 * w + (t.val + w * j.val) = t.val + w * (j.val + 5 * i.val)
  ring

/-- Parsing the physical slice reads the corresponding entry of the full
block parser on every input, including malformed encodings. -/
theorem blockParse_slice (H : ℕ) {w : ℕ} (hw : 2 ≤ w)
    (bits : Fin (RAMLayout.blockBits H w) → Bool) (i : Fin (4 * H)) :
    (recordFormat hw).parse ((arrayBits 5 w).symm (recordSlice H w bits i)) =
      (blockFormat H hw).parse ((arrayBits (4 * H * 5) w).symm bits) i := by
  unfold RAMLayout.blockBits at bits
  simp only [blockFormat, Format.replicate]
  apply congrArg (recordFormat hw).parse
  funext j
  apply (wordBits w).injective
  funext t
  rw [← arrayBits_at, Equiv.apply_symm_apply, recordSlice_at H w bits i j t, ← arrayBits_at,
    Equiv.apply_symm_apply]

/-- Slicing an encoded block gives the encoding of its corresponding slot. -/
theorem blockEncode_slice (H : ℕ) {w : ℕ} (hw : 2 ≤ w)
    (records : Fin (4 * H) → Option (WordRecord w)) (i : Fin (4 * H)) :
    recordSlice H w ((blockFormat H hw).encode records) i = (recordFormat hw).encode (records i) := by
  funext u
  obtain ⟨⟨j, t⟩, rfl⟩ := finProdFinEquiv.surjective u
  refine (recordSlice_at H w ((blockFormat H hw).encode records) i j t).trans ?_
  simp only [Format.encode, arrayBits_at, blockFormat, Format.replicate, Equiv.symm_apply_apply]

/-- A block passes its re-encoding test precisely when every physical slice
is the canonical encoding of a record or an empty slot. -/
theorem blockCanonical_iff (H : ℕ) {w : ℕ} (hw : 2 ≤ w)
    (bits : Fin (RAMLayout.blockBits H w) → Bool) :
    bits = (blockFormat H hw).encode ((blockFormat H hw).parse ((arrayBits _ w).symm bits)) ↔
      ∀ i, ∃ r, recordSlice H w bits i = (recordFormat hw).encode r := by
  let records := (blockFormat H hw).parse ((arrayBits (4 * H * 5) w).symm bits)
  constructor
  · intro he i
    refine ⟨records i, ?_⟩
    exact (congrArg (fun b ↦ recordSlice H w b i) he).trans (blockEncode_slice H hw records i)
  · intro hs
    have sameSlice (i : Fin (4 * H)) :
        recordSlice H w bits i = recordSlice H w ((blockFormat H hw).encode records) i := by
      rw [blockEncode_slice, show records i = _ from (blockParse_slice H hw bits i).symm]
      obtain ⟨r, hr⟩ := hs i
      rw [hr]
      simp [Format.encode, Format.parse_words]
    funext u
    obtain ⟨⟨p, t⟩, rfl⟩ := finProdFinEquiv.surjective u
    obtain ⟨⟨i, j⟩, rfl⟩ := finProdFinEquiv.surjective p
    exact (recordSlice_at H w bits i j t).symm.trans <|
      (congrFun (sameSlice i) (finProdFinEquiv (j, t))).trans (recordSlice_at H w _ i j t)

end RAMSerialization

end VPVNP
end Computability
end OAI
