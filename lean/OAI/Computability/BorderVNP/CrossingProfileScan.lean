import OAI.Computability.BorderVNP.CrossingProfileSize
import Mathlib.Order.Interval.Finset.Fin

/-!
# Reading a selector word in order

The occurrence ordinal used by each terminal is the prefix count for
that letter. One scan of the public alphabet counters produces all
ordinals and the final histogram.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Crossing.Profile

variable {A j : ℕ}

/-- Count occurrences of a given term strictly before the scan position. -/
def prefixCount (w : Fin j → Fin A) (n : ℕ) (a : Fin A) : ℕ :=
  ((positions w a).filter (fun k => k.val < n)).card

/-- The histogram counters start at zero. -/
theorem prefixCount_zero (w : Fin j → Fin A) (a : Fin A) : prefixCount w 0 a = 0 := by
  simp [prefixCount]

/-- Reading one letter increments only its own counter. -/
theorem prefixCount_step (w : Fin j → Fin A) (i : Fin j) (a : Fin A) :
    prefixCount w (i.val + 1) a = prefixCount w i.val a + if w i = a then 1 else 0 := by
  by_cases h : w i = a
  · have hf : ((positions w a).filter (fun k => k.val < i.val + 1)) =
        insert i ((positions w a).filter (fun k => k.val < i.val)) := by
      ext k
      simp only [positions, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
      constructor
      · rintro ⟨hk, hi⟩
        rcases Nat.lt_succ_iff_lt_or_eq.mp hi with ht | heq
        · exact Or.inr ⟨hk, ht⟩
        · exact Or.inl (Fin.ext heq)
      · rintro (rfl | ⟨hk, ht⟩)
        · exact ⟨h, Nat.lt_succ_self _⟩
        · exact ⟨hk, Nat.lt_succ_of_lt ht⟩
    unfold prefixCount
    rw [hf]
    simp [h]
  · have hf : ((positions w a).filter (fun k => k.val < i.val + 1)) =
        ((positions w a).filter (fun k => k.val < i.val)) := by
      ext k
      simp only [positions, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨hk, hi⟩
        exact ⟨hk, lt_of_le_of_ne (Nat.lt_succ_iff.mp hi)
          (fun heq => h ((Fin.ext heq : k = i) ▸ hk))⟩
      · rintro ⟨hk, ht⟩
        exact ⟨hk, Nat.lt_succ_of_lt ht⟩
    unfold prefixCount
    rw [hf]
    simp [h]

/-- The final counters are the exact word histogram. -/
theorem prefixCount_end (w : Fin j → Fin A) (a : Fin A) :
    prefixCount w j a = histogram w a := by
  simp [prefixCount, histogram]

/-- The prefix count at a routed position is the ordinal of that term
copy. A terminal can therefore route the next input directly to its
counter's current position before performing the update. -/
theorem prefixCount_slot (w : Fin j → Fin A) {p : Fin A → ℕ} (hp : histogram w = p)
    (a : Fin A) (l : Fin (p a)) :
    prefixCount w (slots w a hp l).val.val a = l.val := by
  let e := slots w a hp
  let slot (i : Fin (p a)) : Fin j := (e i).val
  have hslot : Function.Injective slot := Subtype.val_injective.comp e.injective
  have himage : (Finset.Iio l).image slot =
      (positions w a).filter (fun i => i.val < (slot l).val) := by
    ext i
    constructor
    · intro hi
      obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hi
      exact Finset.mem_filter.mpr ⟨(e k).property, e.strictMono (Finset.mem_Iio.mp hk)⟩
    · intro hi
      obtain ⟨hmem, hlt⟩ := Finset.mem_filter.mp hi
      let k := e.symm ⟨i, hmem⟩
      have he : e k = ⟨i, hmem⟩ := e.apply_symm_apply _
      refine Finset.mem_image.mpr ⟨k, Finset.mem_Iio.mpr (e.lt_iff_lt.mp ?_), congrArg Subtype.val he⟩
      rw [he]
      exact hlt
  calc
    _ = ((Finset.Iio l).image slot).card := congrArg Finset.card himage.symm
    _ = (Finset.Iio l).card := Finset.card_image_of_injective _ hslot
    _ = l.val := Fin.card_Iio l

end Crossing.Profile

end BorderVNP
end Computability
end OAI
