import OAI.Computability.VPVNP.RAMTapeSuccessorTags
import OAI.Computability.VPVNP.RAMSuccessorDecodeCost

/-!
# The finite control test for an eight-word successor field

The bit-stack machine retains the small tags of the eight words and a separate
unsigned cost comparison. These finite data decide exactly the canonical
encoding test, or the all-zero clamp at a missing edge.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RAMTape.Successor

open BurstRAM RAMMemory RAMSerialization SuccessorTags

/-- One small integer tag for each of the eight words in a successor message. -/
abbrev Tags := Fin 8 → Tag

/-- Empty record padding is fixed in all five words. -/
def recordOK (t : Tags) : Bool := decide (
  t 3 = .one ∨ t 3 = .two ∨ t 3 = .three ∨
    t 3 = .zero ∧ t 4 = .zero ∧ t 5 = .zero ∧ t 6 = .zero ∧ t 7 = .zero)

/-- The zero clamp is separate from a regular, present message. -/
def valid (present : Bool) (t : Tags) (costOK : Bool) : Bool :=
  if present then (decide (t 0 = .one ∨ t 0 = .two ∧ t 2 = .zero)) && costOK && recordOK t
  else decide (∀ j, t j = .zero)

private theorem tagSmall (n : ℕ) :
    (Tag.ofNat n = .zero ↔ n = 0) ∧ (Tag.ofNat n = .one ↔ n = 1) ∧
    (Tag.ofNat n = .two ↔ n = 2) ∧ (Tag.ofNat n = .three ↔ n = 3) := by
  by_cases h : 4 ≤ n
  · rw [Tag.ofNat_large h]
    simp; omega
  · have : n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 := by omega
    rcases this with rfl | rfl | rfl | rfl <;> decide

variable {w cap : ℕ}

/-- Classify the unsigned value of each successor word by its small integer tag. -/
def wordTags (a : Fin 8 → Word w) : Tags := fun i ↦ Tag.ofNat (a i).val

private def GoodRecord (a : Fin 8 → Word w) : Prop :=
  (a 3).val = 1 ∨ (a 3).val = 2 ∨ (a 3).val = 3 ∨
    (a 3).val = 0 ∧ (a 4).val = 0 ∧ (a 5).val = 0 ∧ (a 6).val = 0 ∧ (a 7).val = 0

private theorem goodRecord_iff (hw : 2 ≤ w) (a : Fin 8 → Word w) :
    GoodRecord a ↔ ∃ r : Option (WordRecord w),
      ∀ i : Fin 5, (recordFormat hw).words r i = a (Fin.natAdd 3 i) := by
  constructor
  · rintro (hi | hr | hw' | he)
    · refine ⟨some ⟨.init, a 4, a 5, a 6, a 7⟩, fun i ↦ ?_⟩
      fin_cases i <;> first | rfl | exact Fin.ext hi.symm
    · refine ⟨some ⟨.read, a 4, a 5, a 6, a 7⟩, fun i ↦ ?_⟩
      fin_cases i <;> first | rfl | exact Fin.ext hr.symm
    · refine ⟨some ⟨.write, a 4, a 5, a 6, a 7⟩, fun i ↦ ?_⟩
      fin_cases i <;> first | rfl | exact Fin.ext hw'.symm
    · obtain ⟨h3, h4, h5, h6, h7⟩ := he
      refine ⟨none, fun i ↦ ?_⟩
      fin_cases i <;> apply Fin.ext <;> first | exact h3.symm | exact h4.symm | exact h5.symm | exact h6.symm | exact h7.symm
  · rintro ⟨_ | ⟨kind, addr, val, start, ord⟩, he⟩
    · exact .inr (.inr (.inr ⟨(congrArg Fin.val (he 0)).symm, (congrArg Fin.val (he 1)).symm,
        (congrArg Fin.val (he 2)).symm, (congrArg Fin.val (he 3)).symm, (congrArg Fin.val (he 4)).symm⟩))
    · have h := (congrArg Fin.val (he 0)).symm
      cases kind with
      | init => exact .inl h
      | read => exact .inr (.inl h)
      | write => exact .inr (.inr (.inl h))

/-- A present field passes exactly when all eight saved words have the unique
canonical encoding. Acceptance at the cap is allowed and has state word zero. -/
theorem valid_present_iff (hw : 2 ≤ w) (hc : cap < 2 ^ w) (a : Fin 8 → Word w) :
    valid true (wordTags a) (decide ((a 1).val ≤ cap)) = true ↔
      ∃ x : Successor w cap, (successorFormat hw hc).words x = a := by
  simp only [valid, ↓reduceIte, Bool.and_eq_true, decide_eq_true_eq, wordTags, recordOK,
    (tagSmall _).1, (tagSmall _).2.1, (tagSmall _).2.2.1, (tagSmall _).2.2.2]
  change ((_ ∨ _ ∧ _) ∧ _) ∧ GoodRecord a ↔ _
  rw [goodRecord_iff hw]
  constructor
  · rintro ⟨⟨hstatus, hcost⟩, r, hr⟩
    let c : Fin (cap + 1) := ⟨(a 1).val, Nat.lt_succ_of_le hcost⟩
    rcases hstatus with hrun | ⟨hhalt, hz⟩
    · refine ⟨⟨some (a 2), c, r⟩, funext (Fin.addCases (m := 3) (n := 5) (fun i ↦ ?_) (fun i ↦ (Fin.append_right _ _ i).trans (hr i)))⟩
      fin_cases i <;> first | rfl | exact Fin.ext hrun.symm
    · refine ⟨⟨none, c, r⟩, funext (Fin.addCases (m := 3) (n := 5) (fun i ↦ ?_) (fun i ↦ (Fin.append_right _ _ i).trans (hr i)))⟩
      fin_cases i <;> first | rfl | exact Fin.ext hhalt.symm | exact Fin.ext hz.symm
  · rintro ⟨⟨state, cost, last⟩, rfl⟩
    refine ⟨⟨?_, Nat.le_of_lt_succ cost.isLt⟩, last, fun i ↦ (Fin.append_right _ _ i).symm⟩
    cases state with
    | none => exact .inr ⟨rfl, rfl⟩
    | some _ => exact .inl rfl

theorem valid_clamp_iff (a : Fin 8 → Word w) (costOK : Bool) :
    valid false (wordTags a) costOK = true ↔ a = fun _ ↦ 0 := by
  simp only [valid, Bool.false_eq_true, ↓reduceIte, decide_eq_true_eq, wordTags, (tagSmall _).1]
  exact ⟨fun h ↦ funext fun i ↦ Fin.ext (h i), fun h i ↦ congrArg Fin.val (congrFun h i)⟩

/-- Equality with the word-level validator on every bit pattern. -/
theorem valid_present_bits (hw : 2 ≤ w) (hc : cap < 2 ^ w) (b : Fin (8 * w) → Bool) :
    let a := (arrayBits 8 w).symm b
    valid true (wordTags a) (decide ((a 1).val ≤ cap)) = (scanSuccessor hw hc b).1.2 := by
  apply Bool.eq_iff_iff.mpr
  rw [valid_present_iff hw hc, scanSuccessor_valid, Format.encode]
  constructor
  · rintro ⟨x, hx⟩
    rw [← hx, Format.parse_words, hx, Equiv.apply_symm_apply]
  · intro he
    exact ⟨_, (arrayBits 8 w).eq_symm_apply.mpr he.symm⟩

end RAMTape.Successor

end VPVNP
end Computability
end OAI
