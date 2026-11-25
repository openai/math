import OAI.Computability.BorderVNP.ParseBatchRecordsCheck

/-! # Executable packed parse-block validation -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace ParseRecords

open VPVNP

variable {m g n : ℕ}

/-- Decode each fixed-width record and reject the entire block on a range or padding failure. -/
def unpackRows (m g n : ℕ) : List Fields → Option (List (GrammarLabel (Fin m × Bool) (Fin g) n))
  | [] => some []
  | a :: as => match unpack m g n a, unpackRows m g n as with
    | some r, some rs => some (r :: rs)
    | _, _ => none

/-- A decoded block recovers exactly the raw records, including every unused field. -/
theorem unpackRows_eq_some_iff {raw : List Fields}
    {rs : List (GrammarLabel (Fin m × Bool) (Fin g) n)} :
    unpackRows m g n raw = some rs ↔ raw = rs.map pack := by
  induction raw generalizing rs with
  | nil => cases rs <;> simp [unpackRows]
  | cons a as ih =>
    cases h : unpack m g n a with
    | none =>
      cases rs with
      | nil => simp [unpackRows, h]
      | cons t ts =>
        have ne : a ≠ pack t := fun he => by rw [he, unpack_pack] at h; contradiction
        simp [unpackRows, h, ne]
    | some t =>
      have ha := (unpack_eq_some_iff.mp h).symm
      cases ht : unpackRows m g n as with
      | none =>
        cases rs with
        | nil => simp [unpackRows, h, ht]
        | cons v vs =>
          have ne : as ≠ vs.map pack := fun he => by rw [ih.mpr he] at ht; contradiction
          simp [unpackRows, h, ht, ne]
      | some ts =>
        have he := (ih.mp ht).symm
        cases rs with
        | nil => simp [unpackRows, h, ht]
        | cons v vs =>
          simp only [unpackRows, h, ht, List.map_cons,
            Option.some.injEq, List.cons.injEq]
          constructor
          · rintro ⟨rfl, rfl⟩
            exact ⟨ha.symm, he.symm⟩
          · rintro ⟨hav, has⟩
            exact ⟨Option.some.inj (h.symm.trans (unpack_eq_some_iff.mpr hav)),
              Option.some.inj (ht.symm.trans (ih.mpr has))⟩

/-- Validate a guessed block, with all field, interval, address and root checks. -/
def checkPacked (m : ℕ) (d : Fin n) (h : Fin g) (raw : List Fields) : Bool :=
  (unpackRows m g n raw).any (check d h)

/-- Acceptance is exactly the existence of a valid parse block with these raw records. -/
theorem checkPacked_iff (m : ℕ) (d : Fin n) (h : Fin g) (raw : List Fields) :
    checkPacked m d h raw = true ↔
      ∃ rs : List (GrammarLabel (Fin m × Bool) (Fin g) n), raw = rs.map pack ∧ Valid d h rs := by
  rw [checkPacked, Option.any_eq_true]
  simp only [unpackRows_eq_some_iff, check_iff_valid]

end ParseRecords

end BorderVNP
end Computability
end OAI
