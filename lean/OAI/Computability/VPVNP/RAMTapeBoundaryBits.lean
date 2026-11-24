import OAI.Computability.VPVNP.RAMTapeWord
import OAI.Computability.VPVNP.RAMValidatorBoundaryWord
import Mathlib.Tactic.DeriveFintype
import Mathlib.Data.Fintype.Sigma

/-!
# Bit-by-bit checks of adjacent RAM records

Two equal-width physical records are scanned together, from low to high bit
within each of the five fields. The finite control recognizes the tag, tracks
address and value equality, and tests the current value for zero. The same
scan also tests complete-slot equality for an outgoing message.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RAMTape.Boundary

open BurstRAM RAMMemory RAMSort RAMSerialization RAMBoundary TapeWord

/-- Position in the tag scan, distinguishing the low bit, second bit, and remaining high bits. -/
inductive TagPhase where
  | low | second | high
  deriving DecidableEq

instance : Fintype TagPhase :=
  ⟨{.low, .second, .high}, fun p ↦ by cases p <;> simp⟩

/-- Finite summary of the two tags, field comparisons, and zero test accumulated while scanning
adjacent records. -/
structure Flags where
  /-- Position of the next tag bit in the low, second, or high part of the word. -/
  phase : TagPhase
  /-- Running test that the predecessor tag denotes an occupied slot. -/
  prevUsed : Bool
  /-- Running test that the current tag denotes an occupied slot. -/
  currUsed : Bool
  /-- Running test that the current tag denotes a read. -/
  currRead : Bool
  /-- Whether all address-bit pairs compared so far agree. -/
  addressEq : Bool
  /-- Whether all value-bit pairs compared so far agree. -/
  valueEq : Bool
  /-- Whether every current value bit examined so far is zero. -/
  currZero : Bool
  /-- Whether every pair of record bits examined so far agrees. -/
  allEqual : Bool
  deriving DecidableEq

set_option synthInstance.maxSize 4096 in
deriving instance Fintype for Flags

/-- Start at the low tag bit with empty comparisons and zero tests satisfied. -/
def initial : Flags := ⟨.low, false, false, false, true, true, true, true⟩

private def payload (j : Fin 5) (s : Flags) (eq zero : Bool) : Flags :=
  {s with addressEq := if j = 1 then s.addressEq && eq else s.addressEq
          valueEq := if j = 2 then s.valueEq && eq else s.valueEq
          currZero := if j = 2 then s.currZero && zero else s.currZero
          allEqual := s.allEqual && eq}

private def highTag (s : Flags) (az bz eq : Bool) : Flags :=
  {s with prevUsed := s.prevUsed && az, currUsed := s.currUsed && bz,
          currRead := s.currRead && bz, allEqual := s.allEqual && eq}

/-- One physical bit pair. After the first two tag bits, any set bit makes the
corresponding tag invalid. This requires only three phases for every width. -/
def stepField (j : Fin 5) (s : Flags) (a b : Bool) : Flags :=
  if j = 0 then
    match s.phase with
    | .low => {s with phase := .second, prevUsed := a, currUsed := b, currRead := !b,
                      allEqual := s.allEqual && (a == b)}
    | .second => {s with phase := .high, prevUsed := s.prevUsed || a, currUsed := s.currUsed || b,
                         currRead := s.currRead && b, allEqual := s.allEqual && (a == b)}
    | .high => highTag s (!a) (!b) (a == b)
  else payload j s (a == b) (!b)

/-- Update the boundary flags from one pair of bits at the given field index. -/
abbrev step := stepField

/-- Fold a paired-bit update over two words until either stream ends. -/
def foldWord (next : Flags → Bool → Bool → Flags) : Flags → List Bool → List Bool → Flags
  | s, a :: as, b :: bs => foldWord next (next s a b) as bs
  | s, _, _ => s

/-- Compare the bits of a single field using its field-specific flag update. -/
abbrev foldField (j : Fin 5) := foldWord (stepField j)

@[simp] theorem foldField_nil (j : Fin 5) (s : Flags) (ys : List Bool) :
    foldField j s [] ys = s := rfl

theorem foldField_cons (j : Fin 5) (s : Flags) (a b : Bool) (xs ys : List Bool) :
    foldField j s (a :: xs) (b :: ys) = foldField j (stepField j s a b) xs ys := rfl

/-- Scan the specified field indices in order, passing each comparison’s flags to the next. -/
def foldFields : List (Fin 5) → Flags → (Fin 5 → List Bool) → (Fin 5 → List Bool) → Flags
  | [], s, _, _ => s
  | j :: js, s, a, b => foldFields js (foldField j s (a j) (b j)) a b

variable {w : ℕ}

/-- The five fields of a physical slot, each encoded as a low-bit-first word. -/
def recordWords (a : RawSlot w) : List (List Bool) := List.ofFn fun i ↦ BurstRAM.wordBits (a i)

/-- Compare two complete physical slots from the initial flags in field order. -/
def foldRecord (a b : RawSlot w) : Flags :=
  foldFields (List.finRange 5) initial (fun i ↦ BurstRAM.wordBits (a i)) (fun i ↦ BurstRAM.wordBits (b i))

/-- Accept a read if its value matches an occupied predecessor at the same address, or is zero
when there is no such predecessor. -/
def checked (s : Flags) : Bool :=
  !s.currRead || (if s.prevUsed && s.addressEq then s.valueEq else s.currZero)

/-- For an occupied predecessor require complete record equality. For an unused predecessor
require an unused current slot. -/
def equalChecked (s : Flags) : Bool := if s.prevUsed then s.allEqual else !s.currUsed

private theorem same_cons (a b : Bool) (xs ys : List Bool) :
    decide (a :: xs = b :: ys) = ((a == b) && decide (xs = ys)) := by
  apply Bool.eq_iff_iff.mpr
  simp

private theorem zero_cons (a : Bool) (xs : List Bool) :
    decide (value (a :: xs) = 0) = (!a && decide (value xs = 0)) := by
  cases a <;> simp [value]

private theorem payload_append (j : Fin 5) (s : Flags) (ae az be bz : Bool) :
    payload j (payload j s ae az) be bz = payload j s (ae && be) (az && bz) := by
  by_cases h₁ : j = 1 <;> by_cases h₂ : j = 2 <;> simp [payload, h₁, h₂, Bool.and_assoc]

private theorem highTag_append (s : Flags) (az bz ae cz dz be : Bool) :
    highTag (highTag s az bz ae) cz dz be = highTag s (az && cz) (bz && dz) (ae && be) := by
  simp [highTag, Bool.and_assoc]

private theorem fold_payload (j : Fin 5) (hj : j ≠ 0) (s : Flags) (xs ys : List Bool)
    (hlen : xs.length = ys.length) :
    foldField j s xs ys = payload j s (decide (xs = ys)) (decide (value ys = 0)) := by
  induction xs generalizing ys s with
  | nil =>
    have : ys = [] := by simpa using hlen.symm
    subst ys
    simp [payload, value]
  | cons a xs ih =>
    cases ys with
    | nil => simp at hlen
    | cons b ys =>
      rw [foldField_cons, ih _ _ (Nat.succ.inj hlen), same_cons, zero_cons]
      simp only [stepField, hj, ite_false, payload_append]

private theorem fold_high (s : Flags) (h : s.phase = .high) (xs ys : List Bool)
    (hlen : xs.length = ys.length) : foldField 0 s xs ys =
      highTag s (decide (value xs = 0)) (decide (value ys = 0)) (decide (xs = ys)) := by
  induction xs generalizing ys s with
  | nil =>
    have : ys = [] := by simpa using hlen.symm
    subst ys
    simp [highTag, value]
  | cons a xs ih =>
    cases ys with
    | nil => simp at hlen
    | cons b ys =>
      rw [foldField_cons, ih _ (by simp [stepField, h, highTag]) _ (Nat.succ.inj hlen),
        same_cons, zero_cons, zero_cons]
      simp only [stepField, h, ite_true, highTag_append]

private theorem used_digits (lo hi : Bool) (n : ℕ) :
    ((lo || hi) && decide (n = 0)) =
      decide (0 < lo.toNat + 2 * (hi.toNat + 2 * n) ∧ lo.toNat + 2 * (hi.toNat + 2 * n) ≤ 3) := by
  apply Bool.eq_iff_iff.mpr
  cases lo <;> cases hi <;> simp <;> omega

private theorem read_digits (lo hi : Bool) (n : ℕ) :
    ((!lo && hi) && decide (n = 0)) = decide (lo.toNat + 2 * (hi.toNat + 2 * n) = 2) := by
  apply Bool.eq_iff_iff.mpr
  cases lo <;> cases hi <;> simp <;> omega

private def tagSummary (a b : ℕ) (eq : Bool) : Flags :=
  {initial with phase := .high, prevUsed := decide (0 < a ∧ a ≤ 3), currUsed := decide (0 < b ∧ b ≤ 3),
                currRead := decide (b = 2), allEqual := eq}

private theorem fold_tag (xs ys : List Bool) (hl : xs.length = ys.length) (hw : 2 ≤ xs.length) :
    foldField 0 initial xs ys = tagSummary (value xs) (value ys) (decide (xs = ys)) := by
  obtain ⟨a₀, a₁, xs, rfl⟩ : ∃ a₀ a₁ as, xs = a₀ :: a₁ :: as := by
    cases xs with
    | nil => simp at hw
    | cons a as => cases as <;> simp_all; omega
  obtain ⟨b₀, b₁, ys, rfl⟩ : ∃ b₀ b₁ bs, ys = b₀ :: b₁ :: bs := by
    cases ys with
    | nil => simp at hl
    | cons b bs => cases bs <;> simp_all
  rw [foldField_cons, foldField_cons, fold_high _ rfl _ _ (by simpa using hl)]
  simp only [tagSummary, highTag, stepField, initial, ite_true, Bool.true_and, used_digits, read_digits,
    value, same_cons]
  simp only [Bool.and_assoc]
  rfl

private theorem wordBits_eq {a b : Word w} : BurstRAM.wordBits a = BurstRAM.wordBits b ↔ a = b := by
  constructor
  · intro h
    apply Fin.ext
    simpa only [value_wordBits] using congrArg value h
  · rintro rfl
    rfl

private theorem fold_payload_word (j : Fin 5) (hj : j ≠ 0) (s : Flags) (a b : Word w) :
    foldField j s (BurstRAM.wordBits a) (BurstRAM.wordBits b) =
      payload j s (decide (a = b)) (decide (b.val = 0)) := by
  rw [fold_payload _ hj _ _ _ (by simp), value_wordBits, decide_eq_decide.mpr wordBits_eq]

private theorem fold_tag_word (hw : 2 ≤ w) (a b : Word w) :
    foldField 0 initial (BurstRAM.wordBits a) (BurstRAM.wordBits b) =
      tagSummary a.val b.val (decide (a = b)) := by
  rw [fold_tag _ _ (by simp) (by simpa using hw), value_wordBits, value_wordBits,
    decide_eq_decide.mpr wordBits_eq]

private abbrev Used {w : ℕ} (a : RawSlot w) : Prop := 0 < (a 0).val ∧ (a 0).val ≤ 3

private theorem used_tags {w : ℕ} {a : RawSlot w} (h : Used a) :
    (a 0).val = 1 ∨ (a 0).val = 2 ∨ (a 0).val = 3 := by
  unfold Used at h
  omega

private theorem unused_parse {w : ℕ} (hw : 2 ≤ w) (a : RawSlot w) (h : ¬Used a) :
    (parsedSlot hw a).record = none := by
  unfold Used at h
  have h₁ : (a 0).val ≠ 1 := by omega
  have h₂ : (a 0).val ≠ 2 := by omega
  have h₃ : (a 0).val ≠ 3 := by omega
  simp [parsedSlot, recordFormat]

private theorem parsed_read_iff {w : ℕ} (hw : 2 ≤ w) (a b : RawSlot w) :
    (readOK (parsedSlot hw a).record (parsedSlot hw b).record).1 = true ↔
      ((b 0).val = 2 → (if Used a ∧ a 1 = b 1 then b 2 = a 2 else (b 2).val = 0)) := by
  rw [readOK_spec]
  by_cases hb : Used b
  · rcases used_tags hb with ht | ht | ht
    · simp [parsedSlot, recordFormat, WordRecord.record, ht]
    · by_cases ha : Used a
      · rcases used_tags ha with h | h | h <;> by_cases he : a 1 = b 1 <;>
          simp [parsedSlot, recordFormat, WordRecord.record, ht, h, previousValue, he,
            Fin.val_inj]
      · rw [unused_parse hw a ha]
        simp [parsedSlot, recordFormat, WordRecord.record, ht, previousValue, ha]
    · simp [parsedSlot, recordFormat, WordRecord.record, ht]
  · have ht : (b 0).val ≠ 2 := fun he ↦ hb (by simp [Used, he])
    simp [unused_parse hw b hb, ht]

private theorem fields_iff {w : ℕ} (a b : RawSlot w) (h : (a 0).val = (b 0).val) :
    (a 1 = b 1 ∧ a 2 = b 2 ∧ a 3 = b 3 ∧ a 4 = b 4) ↔ a = b := by
  constructor
  · rintro ⟨h₁, h₂, h₃, h₄⟩
    funext i
    fin_cases i <;> first | exact Fin.ext h | assumption
  · rintro rfl
    simp

private theorem parsed_equal_iff {w : ℕ} (hw : 2 ≤ w) (a b : RawSlot w) :
    (equalSlot (parsedSlot hw a).record (parsedSlot hw b).record).1 = true ↔
      if Used a then a = b else ¬Used b := by
  rw [equalSlot_spec]
  by_cases ha : Used a
  · rw [ite_eq_left ha]
    constructor
    · intro he
      by_cases hb : Used b
      · rcases used_tags ha with ht | ht | ht <;> rcases used_tags hb with ht' | ht' | ht' <;>
          simp [parsedSlot, recordFormat, WordRecord.record, ht, ht', Fin.val_inj] at he
        all_goals exact (fields_iff a b (ht.trans ht'.symm)).1 he
      · rw [unused_parse hw b hb] at he
        rcases used_tags ha with ht | ht | ht <;> simp [parsedSlot, recordFormat, ht] at he
    · rintro rfl
      rfl
  · rw [ite_eq_right ha, unused_parse hw a ha]
    by_cases hb : Used b
    · rcases used_tags hb with ht | ht | ht <;> simp [parsedSlot, recordFormat, ht]
    · simp [unused_parse hw b hb, hb]

private theorem complete_equal (a b : RawSlot w) :
    ((((decide (a 0 = b 0) && decide (a 1 = b 1)) && decide (a 2 = b 2)) &&
      decide (a 3 = b 3)) && decide (a 4 = b 4)) = decide (a = b) := by
  apply Bool.eq_iff_iff.mpr
  simp only [Bool.and_eq_true, decide_eq_true_eq, and_assoc]
  constructor
  · rintro ⟨h₀, hs⟩
    exact (fields_iff a b (congrArg Fin.val h₀)).1 hs
  · rintro rfl
    simp

private theorem foldRecord_summary (hw : 2 ≤ w) (a b : RawSlot w) :
    foldRecord a b = ⟨.high, decide (Used a), decide (Used b), decide ((b 0).val = 2),
      decide (a 1 = b 1), decide (a 2 = b 2), decide ((b 2).val = 0), decide (a = b)⟩ := by
  rw [foldRecord, show List.finRange 5 = [0, 1, 2, 3, 4] from rfl]
  simp only [foldFields, fold_tag_word hw, fold_payload_word 1 (by decide), fold_payload_word 2 (by decide),
    fold_payload_word 3 (by decide), fold_payload_word 4 (by decide)]
  simp [payload, tagSummary, initial, Used, complete_equal]

/-- For arbitrary tuples, the read flag is precisely the word validator's decision. -/
theorem checked_foldRecord (hw : 2 ≤ w) (a b : RawSlot w) :
    checked (foldRecord a b) = (readOK (parsedSlot hw a).record (parsedSlot hw b).record).1 := by
  apply Bool.eq_iff_iff.mpr
  rw [parsed_read_iff, foldRecord_summary hw]
  by_cases hr : (b 0).val = 2 <;> by_cases ha : Used a <;> by_cases he : a 1 = b 1 <;>
    simp [checked, hr, ha, he, eq_comm (a := a 2)]

/-- Complete-slot equality ignores the payload when both tags parse as empty. -/
theorem equalChecked_foldRecord (hw : 2 ≤ w) (a b : RawSlot w) :
    equalChecked (foldRecord a b) = (equalSlot (parsedSlot hw a).record (parsedSlot hw b).record).1 := by
  apply Bool.eq_iff_iff.mpr
  rw [parsed_equal_iff, foldRecord_summary hw]
  change (if decide (Used a) then decide (a = b) else !decide (Used b)) = true ↔ _
  by_cases ha : Used a
  · rw [ite_eq_left (decide_eq_true ha), ite_eq_left ha, decide_eq_true_eq]
  · rw [ite_eq_right (fun h ↦ ha (of_decide_eq_true h)), ite_eq_right ha]
    simp only [Bool.not_eq_true', decide_eq_false_iff_not]

end RAMTape.Boundary

end VPVNP
end Computability
end OAI
