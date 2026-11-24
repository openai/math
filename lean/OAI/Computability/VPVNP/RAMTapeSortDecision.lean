import OAI.Computability.VPVNP.RAMTapeSortCompareBits

/-! # Order and canonicality decisions from the five scanned word fields -/

namespace OAI
namespace Computability
namespace VPVNP

namespace RAMTape.Sorter

open BurstRAM RAMBoundary RAMSort RAMSerialization SuccessorTags

/-- Information retained about one field after scanning both words, including each decoded tag
category and their unsigned comparison. -/
structure Observation where
  /-- Tag category assigned to the left word, distinguishing zero, one, two, three and larger
  values. -/
  left : Tag
  /-- Tag category assigned to the right word using the same finite decoder. -/
  right : Tag
  /-- Unsigned ordering of the two field words after the scan completes. -/
  ord : Ordering
  deriving DecidableEq

instance : Fintype Observation := derive_fintype% _

/-- One comparison observation for each of the five fields of the paired records. -/
abbrev RecordInfo := Fin 5 → Observation

/-- Finish both tag decoders and retain the word ordering from the completed field scan. -/
def observe (s : WordState) : Observation := ⟨finish s.lhs, finish s.rhs, s.ord⟩

/-- The five field observations computed directly from two raw records' natural word values. -/
def expected {w : ℕ} (a b : RawSlot w) : RecordInfo := fun i ↦
  ⟨Tag.ofNat (a i).val, Tag.ofNat (b i).val, compare (a i).val (b i).val⟩

theorem observe_fold {w : ℕ} (a b : RawSlot w) (i : Fin 5) :
    observe (Boundary.Field.fold WordState.step WordState.start (BurstRAM.wordBits (a i))
      (BurstRAM.wordBits (b i))) = expected a b i := by
  obtain ⟨hl,hr,ho⟩ := wordState_spec (a i) (b i)
  simp only [observe, expected, hl, hr, ho]

/-- Recognize the three occupied record tags, one through three. -/
def used : Tag → Bool
  | .one | .two | .three => true
  | _ => false

private def probe : Tag → Bool
  | .zero | .one => false
  | _ => true

private theorem tags (n : ℕ) :
    used (Tag.ofNat n) = decide (0 < n ∧ n ≤ 3) ∧
    (probe (Tag.ofNat n)).toNat = (if 1 < n then 1 else 0) ∧
    (Tag.ofNat n = .zero ↔ n = 0) := by
  match n with
  | 0 | 1 | 2 | 3 => decide
  | n + 4 =>
    rw [Tag.ofNat_large (by omega)]
    simp [used, probe]

/-- Return the left-first verdict for an unequal comparison and use the supplied secondary
verdict to break equality. -/
def chooseOrder : Ordering → Bool → Bool
  | .lt, _ => true
  | .gt, _ => false
  | .eq, tie => tie

private theorem chooseOrder_compare (a b : ℕ) (tie : Bool) :
    chooseOrder (compare a b) tie = WordCompare.lexBit a b tie := by
  rcases lt_trichotomy a b with hl | he | hg
  · simp [compare, compareOfLessAndEq, WordCompare.lexBit, chooseOrder, hl, hl.ne]
  · subst b; simp [compare, compareOfLessAndEq, WordCompare.lexBit, chooseOrder]
  · simp [compare, compareOfLessAndEq, WordCompare.lexBit, chooseOrder, not_lt_of_gt hg, hg.ne']

/-- The initialized-address flag is between the address and the timestamp.
The value is consulted only after equal timestamp and kind. -/
def leDecision (f : RecordInfo) : Bool :=
  if used (f 0).right then
    if used (f 0).left then
      chooseOrder (f 1).ord (chooseOrder (compare (probe (f 0).left).toNat (probe (f 0).right).toNat)
        (chooseOrder (f 3).ord (chooseOrder (f 4).ord (chooseOrder (f 0).ord (chooseOrder (f 2).ord true)))))
    else false
  else true

/-- On an arbitrary five-word tuple the scan compares the parsed slots,
including the parser's empty value for unknown tags. -/
theorem leDecision_eq {w : ℕ} (hw : 2 ≤ w) (a b : RawSlot w) :
    leDecision (expected a b) = decide (parsedSlot hw a ≤ parsedSlot hw b) := by
  rw [← compareSlots_result, ← compareWords_eq hw a b, WordCompare.compareWords_lex]
  simp only [leDecision, expected, chooseOrder_compare, (tags _).1, (tags _).2.1, decide_eq_true_eq]
  have tail : WordCompare.lexBit (a 2).val (b 2).val true = decide (a 2 ≤ b 2) := by
    by_cases he : (a 2).val = (b 2).val
    · simp [WordCompare.lexBit, he, show a 2 ≤ b 2 from Nat.le_of_eq he]
    · by_cases hl : (a 2).val < (b 2).val
      · simp [WordCompare.lexBit, he, hl, show a 2 ≤ b 2 from hl.le]
      · simp [WordCompare.lexBit, he, hl, show ¬a 2 ≤ b 2 from fun h ↦ by
          change (a 2).val ≤ (b 2).val at h; omega]
  rw [tail]

/-- An occupied tag may carry data fields, while an empty record must have all five fields
zero. -/
def canonical (f : Fin 5 → Tag) : Bool := used (f 0) || decide (∀ j, f j = .zero)

theorem canonical_iff {w : ℕ} (hw : 2 ≤ w) (a : RawSlot w) :
    canonical (fun i ↦ Tag.ofNat (a i).val) = true ↔ ∃ r, (recordFormat hw).words r = a := by
  simp only [canonical, (tags _).1, (tags _).2.2, Bool.or_eq_true, decide_eq_true_eq]
  constructor
  · rintro (h | h)
    · have ht : (a 0).val = 1 ∨ (a 0).val = 2 ∨ (a 0).val = 3 := by omega
      rcases ht with hi | hr | hw'
      · exact ⟨some ⟨.init,a 1,a 2,a 3,a 4⟩, funext fun i ↦ by fin_cases i <;> first | rfl | exact Fin.ext hi.symm⟩
      · exact ⟨some ⟨.read,a 1,a 2,a 3,a 4⟩, funext fun i ↦ by fin_cases i <;> first | rfl | exact Fin.ext hr.symm⟩
      · exact ⟨some ⟨.write,a 1,a 2,a 3,a 4⟩, funext fun i ↦ by fin_cases i <;> first | rfl | exact Fin.ext hw'.symm⟩
    · exact ⟨none, funext fun j ↦ Fin.ext (h j).symm⟩
  · rintro ⟨_ | ⟨kind,a',v,c,j⟩, rfl⟩
    · exact Or.inr (fun _ ↦ rfl)
    · left
      cases kind with
      | init => change 0 < 1 ∧ 1 ≤ 3; decide
      | read => change 0 < 2 ∧ 2 ≤ 3; decide
      | write => change 0 < 3 ∧ 3 ≤ 3; decide

/-- Check equality of all five fields of the compared records. -/
def equalDecision (f : RecordInfo) : Bool := decide (∀ i, (f i).ord = .eq)

theorem equalDecision_eq {w : ℕ} (a b : RawSlot w) :
    equalDecision (expected a b) = decide (a = b) := by
  apply decide_eq_decide.mpr
  change (∀ i, compare (a i).val (b i).val = .eq) ↔ a = b
  simp only [compare_eq_iff_eq]
  exact ⟨fun h ↦ funext fun i ↦ Fin.ext (h i), fun h i ↦ h ▸ rfl⟩

end RAMTape.Sorter

end VPVNP
end Computability
end OAI
