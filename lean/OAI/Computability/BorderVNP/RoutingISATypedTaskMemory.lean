import OAI.Computability.BorderVNP.RoutingISATypedTaskBuilder

/-! # Memory image and ownership of the native task builder -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.TypedTaskBuilder

/-- Natural-word image of a run of consecutive scalar stores. -/
def putNat (mem : ℕ → ℕ) (base : ℕ) : List ℕ → ℕ → ℕ
  | [] => mem
  | v::vs => putNat (Function.update mem base v) (base+1) vs

/-- Stores preserve addresses on either side of their half-open interval. -/
theorem putNat_outside (mem : ℕ → ℕ) (base a : ℕ) (values : List ℕ)
    (h : a < base ∨ base+values.length ≤ a) : putNat mem base values a = mem a := by
  induction values generalizing mem base with
  | nil => rfl
  | cons v vs ih =>
    simp only [List.length_cons] at h
    rw [putNat,ih (Function.update mem base v) (base+1) (by omega),Function.update_of_ne (by omega : a ≠ base)]

/-- Read back a word of the exact emitted row. -/
theorem putNat_read (mem : ℕ → ℕ) (base : ℕ) (values : List ℕ) (i : Fin values.length) :
    putNat mem base values (base+i.val) = values[i] := by
  induction values generalizing mem base with
  | nil => exact i.elim0
  | cons v vs ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · simp only [Fin.val_zero,Nat.add_zero,putNat]
      rw [putNat_outside _ _ _ _ (Or.inl (by omega)),Function.update_self]
      rfl
    · simpa [putNat,Nat.add_assoc,Nat.add_comm 1] using ih (Function.update mem base v) (base+1) j

/-- Chronological shared-memory image through all cells before the given cursor. -/
def Layout.image (l : Layout) (original : ℕ → ℕ) : ℕ → ℕ → ℕ
  | 0 => original
  | c+1 =>
    let m := Function.update (l.image original c) (l.call c) (l.owner original c)
    if l.owner original c = l.team then putNat m (l.tasks+7*l.before original c) (l.row original c) else m

/-- Exact native image after publishing the populated task count. -/
def Layout.published (l : Layout) (mem : ℕ → ℕ) : ℕ → ℕ :=
  Function.update (l.image mem l.cells) (l.frame+90) (l.before mem l.cells)

private theorem row_len (l : Layout) (mem : ℕ → ℕ) (c : ℕ) : (l.row mem c).length = 7 := rfl

/-- Any address not reserved for this stage is still present at every iteration. -/
theorem Layout.image_outside (l : Layout) (mem : ℕ → ℕ) (i : ℕ) (hi : i ≤ l.cells)
    (a : ℕ) (h : ¬l.outputAt a) : l.image mem i a = mem a := by
  induction i with
  | zero => rfl
  | succ c ih =>
    have hc : c < l.cells := by omega
    have old : a ≠ l.call c := fun hh => h (Or.inr (Or.inl ⟨c,hc,hh⟩))
    have region : a < l.tasks ∨ l.tasks+7*l.cells ≤ a := by
      by_contra! hn
      exact h (Or.inl hn)
    have hj := l.before_le mem c
    rw [image]
    split
    · rw [putNat_outside _ _ _ _ (by rw [row_len]; omega),Function.update_of_ne old,ih (by omega)]
    · rw [Function.update_of_ne old,ih (by omega)]

/-- The actual addresses consulted by a cell gather still have their original values. -/
theorem Layout.image_input {w : ℕ} (l : Layout) (mem : ℕ → ℕ) (room : l.Room mem w)
    {i c a : ℕ} (hi : i ≤ l.cells) (hc : c < l.cells) (ha : l.inputAt c a) :
    l.image mem i a = mem a := l.image_outside mem i hi a (room.input c hc a ha)

/-- A previously emitted task remains strictly before all subsequent task starts. -/
theorem Layout.before_strict (l : Layout) (mem : ℕ → ℕ) {i j : ℕ} (h : i < j) (ho : l.owner mem i = l.team) :
    l.before mem i < l.before mem j := by
  induction j with
  | zero => omega
  | succ j ih =>
    by_cases eq : i = j
    · subst j; simp [before,ho]
    · exact (ih (by omega)).trans_le (by rw [before]; omega)

private theorem ownerOutside {w : ℕ} (l : Layout) {mem : ℕ → ℕ} (room : l.Room mem w)
    {c i : ℕ} (hc : c < l.cells) (hi : i < l.cells) :
    l.call c < l.tasks+7*l.before mem i ∨ l.tasks+7*l.before mem i+7 ≤ l.call c := by
  have := l.before_le mem i
  rcases room.ownerTasks with h|h <;> unfold Layout.call <;> omega

/-- All global call rows receive the actual owner, including rows owned by another team. -/
theorem Layout.image_owner {w : ℕ} (l : Layout) (mem : ℕ → ℕ) (room : l.Room mem w)
    {c i : ℕ} (hc : c < i) (hi : i ≤ l.cells) : l.image mem i (l.call c) = l.owner mem c := by
  induction i with
  | zero => omega
  | succ i ih =>
    have stable := ownerOutside l room (c := c) (i := i) (by omega) (by omega)
    rw [image]
    split
    · rw [putNat_outside _ _ _ _ (by rwa [row_len])]
      by_cases eq : c=i
      · subst c; exact Function.update_self ..
      · rw [Function.update_of_ne (by unfold Layout.call; omega : l.call c ≠ l.call i),ih (by omega) (by omega)]
    · by_cases eq : c=i
      · subst c; exact Function.update_self ..
      · rw [Function.update_of_ne (by unfold Layout.call; omega : l.call c ≠ l.call i),ih (by omega) (by omega)]

/-- Read any word of a previously emitted seven-word row in the compact local table. -/
theorem Layout.image_word {w : ℕ} (l : Layout) (mem : ℕ → ℕ) (room : l.Room mem w)
    {c i : ℕ} (hc : c < i) (hi : i ≤ l.cells) (ho : l.owner mem c=l.team) (b : Fin 7) :
    l.image mem i (l.tasks+7*l.before mem c+b.val) = (l.row mem c)[b.val]'(by rw [row_len]; exact b.isLt) := by
  induction i with
  | zero => omega
  | succ i ih =>
    have size := l.before_le mem c
    have idx := b.isLt
    have apart : l.tasks+7*l.before mem c+b.val ≠ l.call i := by
      rcases room.ownerTasks with ha|ha <;> unfold Layout.call <;> omega
    by_cases eq : c = i
    · subst i
      rw [image,ite_eq_left ho]
      exact putNat_read _ _ (l.row mem c) ⟨b.val,by rw [row_len]; exact b.isLt⟩
    · have lt := l.before_strict mem (show c < i by omega) ho
      rw [image]
      split
      · rw [putNat_outside _ _ _ _ (Or.inl (by omega)),Function.update_of_ne apart,ih (by omega) (by omega)]
      · rw [Function.update_of_ne apart,ih (by omega) (by omega)]

/-- Every populated local task index is produced by an owned global cell. -/
theorem Layout.before_surjective (l : Layout) (mem : ℕ → ℕ) {i j : ℕ} (hj : j < l.before mem i) :
    ∃ c < i, l.owner mem c=l.team ∧ l.before mem c=j := by
  induction i with
  | zero => exact (Nat.not_lt_zero _ hj).elim
  | succ i ih =>
    by_cases prev : j < l.before mem i
    · obtain ⟨c,hc,hh⟩ := ih prev
      exact ⟨c,by omega,hh⟩
    · have own : l.owner mem i=l.team := by by_contra hn; simp [before,hn,prev] at hj
      have := by simpa [before,own] using hj
      exact ⟨i,by omega,own,by omega⟩

/-- Unique owned global cell at every emitted task ordinal. -/
theorem Layout.before_unique (l : Layout) (mem : ℕ → ℕ) {i j : ℕ} (hj : j < l.before mem i) :
    ∃! c, c < i ∧ l.owner mem c=l.team ∧ l.before mem c=j := by
  obtain ⟨c,hc,ho,he⟩ := l.before_surjective mem hj
  refine ⟨c,⟨hc,ho,he⟩,?_⟩
  rintro d ⟨_,hd,hj'⟩
  rcases lt_trichotomy d c with h|h|h
  · have := l.before_strict mem h hd; omega
  · exact h
  · have := l.before_strict mem h ho; omega

end RoutingISA.TypedTaskBuilder

end BorderVNP
end Computability
end OAI
