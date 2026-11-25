import OAI.Computability.BorderVNP.TransmissionTableChoices
import Mathlib.Data.List.OfFn

/-! # Dependence of physical transmission memory on the chronological choices -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.Transmission

open VPVNP.BurstRAM

variable {w : ℕ}

/-- Only locally shared rows read the private assignment, exactly at their listed offsets. -/
theorem Range.choiceBits_eq_iff (row : Range w) (self : Word w) (a b : ℕ → Bool) :
    row.choiceBits self a = row.choiceBits self b ↔
      (row.selected self = some (some .sharedHere) → ∀ j < row.width.val, a j = b j) := by
  by_cases sel : row.selected self = some (some .sharedHere)
  · simp only [Range.choiceBits, sel, ite_true, true_implies, List.ofFn_inj]
    exact ⟨fun h j hj => congrFun h ⟨j,hj⟩, fun h => funext fun j => h j j.isLt⟩
  · simp [Range.choiceBits, sel]

/-- Equal chronological choices imply identical partial memory scans of the selected
role. The ignored choice tape of a data row can be arbitrary. -/
theorem Range.rangeMemory_congr_choices {row : Range w} {self : Word w} {mode : Role}
    (sel : row.selected self = some (some mode)) (pub : Arg → Word w) (m : Memory w)
    {a b : ℕ → Bool} (h : row.choiceBits self a = row.choiceBits self b) (k : ℕ)
    (hk : k ≤ row.width.val) :
    rangeMemory mode pub (row.bank self) m a k = rangeMemory mode pub (row.bank self) m b k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [rangeMemory, ih (Nat.le_of_succ_le hk)]
    cases mode with
    | sharedHere => rw [(row.choiceBits_eq_iff self a b).mp h sel k hk]
    | dataHere | sendData | receiveA | receiveB => rfl

/-- The row memory transformation factors through its finite list of actual choices. -/
theorem Range.apply_congr_choices (row : Range w) (self : Word w) (pub : Arg → Word w)
    (m : Memory w) {a b : ℕ → Bool} (h : row.choiceBits self a = row.choiceBits self b) :
    row.apply self pub m a = row.apply self pub m b := by
  unfold Range.apply
  cases sel : row.selected self with
  | none => rfl
  | some role =>
    cases role with
    | none => rfl
    | some mode => exact row.rangeMemory_congr_choices sel pub m h _ le_rfl

/-- The address and data-delivery checks also factor through the finite choice list. -/
theorem Range.allowed_congr_choices (row : Range w) (self : Word w) (pub : Arg → Word w)
    (m : Memory w) {a b : ℕ → Bool} (h : row.choiceBits self a = row.choiceBits self b) :
    row.allowed self pub m a ↔ row.allowed self pub m b := by
  suffices forward : ∀ x y : ℕ → Bool, row.choiceBits self x = row.choiceBits self y →
      row.allowed self pub m x → row.allowed self pub m y from ⟨forward a b h, forward b a h.symm⟩
  rintro x y eq ⟨role,sel,ok⟩
  refine ⟨role,sel,?_⟩
  intro mode hm j hj t hr ht h1 h0 hj'
  rw [← row.rangeMemory_congr_choices (hm ▸ sel) pub m eq j hj.le]
  exact ok mode hm j hj t hr ht h1 h0 hj'

/-- The fixed row lengths permit the chronological stream to be split uniquely, even
when it contains adjacent rows of length zero. -/
theorem tableChoiceBits_eq_iff (rows : ℕ → Range w) (self : Word w) (a b : ℕ → ℕ → Bool) (k : ℕ) :
    tableChoiceBits rows self a k = tableChoiceBits rows self b k ↔
      ∀ i < k, (rows i).choiceBits self (a i) = (rows i).choiceBits self (b i) := by
  induction k with
  | zero => simp [tableChoiceBits]
  | succ k ih =>
    have len : (tableChoiceBits rows self a k).length = (tableChoiceBits rows self b k).length := by
      rw [tableChoiceBits_length,tableChoiceBits_length]
    constructor
    · intro h i hi
      obtain ⟨earlier,last⟩ := List.append_inj (show
        tableChoiceBits rows self a k ++ (rows k).choiceBits self (a k) =
        tableChoiceBits rows self b k ++ (rows k).choiceBits self (b k) from h) len
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
      · exact ih.mp earlier i hi
      · exact last
    · intro h
      rw [tableChoiceBits, tableChoiceBits, ih.mpr (fun i hi => h i (hi.trans k.lt_succ_self)),
        h k k.lt_succ_self]

/-- Equal chronological streams of the entire directory determine every earlier memory
state, with no hypothesis on unused offsets in the two assignments. -/
theorem tableMemory_eq_of_choices (rows : ℕ → Range w) (self : Word w) (pub : Arg → Word w)
    (m : Memory w) {a b : ℕ → ℕ → Bool} {k : ℕ}
    (h : tableChoiceBits rows self a k = tableChoiceBits rows self b k) (i : ℕ) (hi : i ≤ k) :
    tableMemory rows self pub m a i = tableMemory rows self pub m b i := by
  have agree := (tableChoiceBits_eq_iff rows self a b k).mp h
  induction i with
  | zero => rfl
  | succ i ih =>
    rw [tableMemory,tableMemory,ih (Nat.le_of_succ_le hi)]
    exact (rows i).apply_congr_choices self pub _ (agree i hi)

end RoutingISA.Transmission

end BorderVNP
end Computability
end OAI
