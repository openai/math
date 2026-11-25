import OAI.Computability.BorderVNP.ParseBatchRecordBits
import OAI.Computability.BorderVNP.ParseBatchRecordsQuery

/-! # Bijection of bit assignments with the parses counted by a coefficient query -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace ParseRecords

open VPVNP VPVNP.ParseGrammar

variable {m g n : ℕ}

/-- Decode each fixed-size record in a guessed list. A malformed record rejects the entire
list. -/
def readBlock (m g n : ℕ) (bs : List (BitSlot (recordWidth m g n) → Bool)) :
    Option (List (GrammarLabel (Fin m × Bool) (Fin g) n)) :=
  bs.mapM (fun b => unpack m g n (fieldsOfBits b))

/-- Successful word decoding permits precisely the canonical bit encodings, slot by slot. -/
theorem readBlock_eq_some_iff {bs : List (BitSlot (recordWidth m g n) → Bool)}
    {rs : List (GrammarLabel (Fin m × Bool) (Fin g) n)} :
    readBlock m g n bs = some rs ↔ bs = rs.map packBits := by
  induction bs generalizing rs with
  | nil => cases rs <;> simp [readBlock]
  | cons b bs ih =>
    rw [readBlock, List.mapM_cons]
    change ((unpack m g n (fieldsOfBits b)).bind (fun t =>
      (readBlock m g n bs).bind (fun ts => some (t :: ts)))) = some rs ↔ _
    simp only [Option.bind_eq_some_iff, unpack_bits_iff, ih, Option.some.injEq]
    constructor
    · rintro ⟨t, rfl, ts, rfl, rfl⟩
      rfl
    · cases rs with
      | nil => simp
      | cons t ts =>
        rintro he
        obtain ⟨hb, hbs⟩ := List.cons.inj he
        exact ⟨t, hb, ts, hbs, rfl⟩

/-- The complete test on a fixed-length block of bit guesses. The same dummy-padded
multiset comparison is used for all tree shapes. -/
def CheckedBits (d : Fin n) (h : Fin g) (x : Fin m → Bool)
    (bs : Fin (2*d.val+1) → BitSlot (recordWidth m g n) → Bool) : Prop :=
  ∃ rs, readBlock m g n (List.ofFn bs) = some rs ∧ Valid d h rs ∧
    Matches d (fun i => (i,x i)) rs

/-- The raw bits in the physical slot of an ordered tree. -/
def treeBits (d : Fin n) (h : Fin g) (p : OrderedParse (Fin m × Bool) (Fin g) d.val) :
    Fin (2*d.val+1) → BitSlot (recordWidth m g n) → Bool :=
  fun i => packBits ((encode d h p)[i.val]'((encode_length d h p).symm ▸ i.isLt))

/-- As a list the guessed block has exactly the bits of the preorder records. -/
theorem ofFn_treeBits (d : Fin n) (h : Fin g) (p : OrderedParse (Fin m × Bool) (Fin g) d.val) :
    List.ofFn (treeBits d h p) = (encode d h p).map packBits := by
  apply List.ext_getElem
  · simp [encode_length]
  · intro i hi hj
    simp only [List.getElem_ofFn, List.getElem_map, treeBits]

/-- Guessing all `(2d−1)(2+6w)` node bits and enforcing the local and padded-leaf checks
counts each parse choice exactly once, including in positive characteristic. Here the
degree is one more than the layer `d.val`. -/
noncomputable def queryBitsEquiv (d : Fin n) (h : Fin g) (x : Fin m → Bool) :
    ParseChoice (Fin g) d x ≃
      {bs : Fin (2*d.val+1) → BitSlot (recordWidth m g n) → Bool // CheckedBits d h x bs} := by
  classical
  let f (a : ParseChoice (Fin g) d x) :
      {bs : Fin (2*d.val+1) → BitSlot (recordWidth m g n) → Bool // CheckedBits d h x bs} :=
    ⟨treeBits d h a.1, encode d h a.1, readBlock_eq_some_iff.mpr (ofFn_treeBits d h a.1),
      (queryEquiv d h x a).property⟩
  apply Equiv.ofBijective f
  constructor
  · intro a b e
    apply (queryEquiv d h x).injective
    apply Subtype.ext
    have he : treeBits d h a.1 = treeBits d h b.1 := congrArg Subtype.val e
    have hl : List.ofFn (treeBits d h a.1) = List.ofFn (treeBits d h b.1) := congrArg _ he
    rw [ofFn_treeBits, ofFn_treeBits] at hl
    exact Option.some.inj ((readBlock_eq_some_iff.mpr rfl).symm.trans (readBlock_eq_some_iff.mpr hl))
  · rintro ⟨bs, rs, hread, hvalid, hmatch⟩
    obtain ⟨a, ha⟩ := (queryEquiv d h x).surjective ⟨rs, hvalid, hmatch⟩
    have he : encode d h a.1 = rs := congrArg Subtype.val ha
    refine ⟨a, Subtype.ext ?_⟩
    apply List.ofFn_injective
    change List.ofFn (treeBits d h a.1) = List.ofFn bs
    rw [ofFn_treeBits, he, readBlock_eq_some_iff.mp hread]

/-- The forward map in the bit-level bijection is the preorder bit array. -/
theorem queryBitsEquiv_apply (d : Fin n) (h : Fin g) (x : Fin m → Bool)
    (p : ParseChoice (Fin g) d x) : (queryBitsEquiv d h x p).val = treeBits d h p.1 := rfl

end ParseRecords

end BorderVNP
end Computability
end OAI
