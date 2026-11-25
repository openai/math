import OAI.Computability.BorderVNP.TransmissionChoiceMemory

/-! # Decoding finite words into locally shared transmission bits -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.Transmission

open VPVNP.BurstRAM

variable {w : ℕ}

/-- Number of actual private choices made by rows strictly before row `k`. -/
def choiceOffset (rows : ℕ → Range w) (self : Word w) (k : ℕ) : ℕ :=
  ∑ i ∈ Finset.range k, if (rows i).selected self = some (some .sharedHere) then (rows i).width.val else 0

/-- Read row `i`, slot `j` from the chronological stream at its absolute bit offset.
Out-of-range accesses have a fixed default and never contribute to the encoded stream
when its length matches the directory. -/
def decodeChoices (rows : ℕ → Range w) (self : Word w) (bs : List Bool) (i j : ℕ) : Bool :=
  (bs[choiceOffset rows self i + j]?).getD false

private theorem decode_prefix (rows : ℕ → Range w) (self : Word w) (bs : List Bool) (k : ℕ) :
    tableChoiceBits rows self (decodeChoices rows self bs) k =
      List.ofFn (fun i : Fin (choiceOffset rows self k) => (bs[i.val]?).getD false) := by
  induction k with
  | zero => simp [tableChoiceBits, choiceOffset]
  | succ k ih =>
    rw [tableChoiceBits, ih]
    have next : choiceOffset rows self (k+1) = choiceOffset rows self k +
        if (rows k).selected self = some (some .sharedHere) then (rows k).width.val else 0 :=
      Finset.sum_range_succ ..
    by_cases h : (rows k).selected self = some (some .sharedHere)
    · simp only [Range.choiceBits,h,ite_true] at next ⊢
      rw [next,List.ofFn_add]
      rfl
    · simp only [h,ite_false,Nat.add_zero] at next
      simp only [Range.choiceBits,h,ite_false,List.append_nil,next,Fin.val_cast]

/-- Every bit string of the physical directory's exact length round-trips through the
canonical offset decoder. This gives one representative assignment per finite word. -/
theorem tableChoiceBits_decodeChoices (rows : ℕ → Range w) (self : Word w) (bs : List Bool)
    {k : ℕ} (h : bs.length = choiceOffset rows self k) :
    tableChoiceBits rows self (decodeChoices rows self bs) k = bs := by
  rw [decode_prefix, ← h]
  calc
    _ = List.ofFn (fun i : Fin bs.length => bs[i.val]) := by
      apply congrArg List.ofFn
      funext i
      rw [List.getElem?_eq_getElem i.isLt]
      rfl
    _ = bs := List.ofFn_getElem

/-- Replacing a raw assignment by the canonical decoding of its chronological stream
preserves each row's address and data checks at the actual intermediate memory. -/
theorem decodeChoices_allowed (rows : ℕ → Range w) (self : Word w) (pub : Arg → Word w)
    (m : Memory w) (a : ℕ → ℕ → Bool) (k i : ℕ) (hi : i < k) :
    let decoded := decodeChoices rows self (tableChoiceBits rows self a k)
    (rows i).allowed self pub (tableMemory rows self pub m decoded i) (decoded i) ↔
      (rows i).allowed self pub (tableMemory rows self pub m a i) (a i) := by
  dsimp only
  have round := tableChoiceBits_decodeChoices rows self _ (tableChoiceBits_length rows self a k)
  rw [tableMemory_eq_of_choices rows self pub m round i hi.le]
  exact (rows i).allowed_congr_choices self pub _ ((tableChoiceBits_eq_iff rows self _ a k).mp round i hi)

end RoutingISA.Transmission

end BorderVNP
end Computability
end OAI
