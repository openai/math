import OAI.Hierarchy.ProbeStageMask
import Mathlib.Combinatorics.Colex

namespace OAI
/-! # The mutable availability masks and their fixed occurrence lists -/

namespace Hierarchy.ProbeStage.PackedMask

open Finset

/-- One availability word for a color string and one consecutive chunk of its positions.
The last chunk is padded by zeros. -/
def bits {B ℓ : ℕ} (row : Fin ℓ → Fin B) (full : Finset (Fin B)) (width chunk : ℕ) : Finset ℕ :=
  (range width).filter fun t => ∃ i : Fin ℓ, i.val=chunk*width+t ∧ row i ∉ full

def word {B ℓ : ℕ} (row : Fin ℓ → Fin B) (full : Finset (Fin B)) (width chunk : ℕ) : ℕ :=
  Finset.equivBitIndices.symm (bits row full width chunk)

theorem word_test {B ℓ : ℕ} (row : Fin ℓ → Fin B) (full : Finset (Fin B)) (width chunk t : ℕ) :
    (word row full width chunk).testBit t = true ↔
      t<width ∧ ∃ i : Fin ℓ, i.val=chunk*width+t ∧ row i ∉ full := by
  have h := Finset.equivBitIndices.apply_symm_apply (bits row full width chunk)
  change (word row full width chunk).bitIndices.toFinset = _ at h
  simpa [bits, ← Nat.mem_bitIndices] using Finset.ext_iff.mp h t

theorem word_lt {B ℓ : ℕ} (row : Fin ℓ → Fin B) (full : Finset (Fin B)) (width chunk : ℕ) :
    word row full width chunk < 2^width := by
  by_contra! h
  obtain ⟨i,hi,hset⟩ := Nat.exists_ge_and_testBit_of_ge_two_pow h
  exact (word_test row full width chunk i |>.1 hset).1.not_ge hi

/-- The literal stored next to one occurrence zeros just that bit of its target word. -/
def keep (width offset : ℕ) : ℕ := (2^width-1) ^^^ (2^offset)

theorem keep_test {width offset i : ℕ} (ho : offset<width) :
    (keep width offset).testBit i = decide (i<width ∧ i≠offset) := by
  simp only [keep,Nat.testBit_xor,Nat.testBit_two_pow_sub_one,Nat.testBit_two_pow]
  by_cases h : offset=i
  · subst i
    simp [ho]
  · by_cases hi : i<width <;> simp [h,Ne.symm h,hi]

abbrev Pos (B ℓ : ℕ) := MaskIndex B × Fin ℓ

noncomputable def occurrences {B ℓ : ℕ} (strings : MaskIndex B → Fin ℓ → Fin B) (c : Fin B) : List (Pos B ℓ) :=
  (univ.filter fun p : Pos B ℓ => strings p.1 p.2 = c).toList

@[simp] theorem mem_occurrences {B ℓ : ℕ} (strings : MaskIndex B → Fin ℓ → Fin B) (c : Fin B) (p : Pos B ℓ) :
    p ∈ occurrences strings c ↔ strings p.1 p.2=c := by simp [occurrences]

/-- The update of one row's one queried chunk by an occurrence descriptor. -/
def scatterBit {B ℓ : ℕ} (width : ℕ) (row : MaskIndex B) (chunk : ℕ) (x : ℕ) (p : Pos B ℓ) :=
  if p.1=row ∧ p.2.val/width=chunk then x &&& keep width (p.2.val%width) else x

theorem scatter_list {B ℓ : ℕ} (width : ℕ) (pos : 0<width) (row : MaskIndex B) (chunk t x : ℕ)
    (ht : t<width) (L : List (Pos B ℓ)) :
    (L.foldl (scatterBit width row chunk) x).testBit t = true ↔
    x.testBit t = true ∧ ∀ p ∈ L, p.1≠row ∨ p.2.val≠chunk*width+t := by
  induction L generalizing x with
  | nil => simp
  | cons p rest ih =>
    rw [List.foldl_cons,ih]
    have div := Nat.mod_add_div p.2.val width
    have rem := Nat.mod_lt p.2.val pos
    have code : p.2.val=chunk*width+t ↔ p.2.val/width=chunk ∧ p.2.val%width=t := by
      constructor
      · intro hp
        rw [hp,Nat.mul_comm chunk width]
        simp [Nat.mul_add_div pos,Nat.div_eq_of_lt ht,Nat.mod_eq_of_lt ht]
      · rintro ⟨h1,h2⟩
        rw [h1,h2,Nat.mul_comm width chunk] at div
        omega
    by_cases h : p.1=row ∧ p.2.val/width=chunk
    · simp only [scatterBit,ite_eq_left h,Nat.testBit_and,Bool.and_eq_true,keep_test rem,decide_eq_true_eq,ht,true_and,List.mem_cons,forall_eq_or_imp,ne_eq]
      rw [code]
      tauto
    · simp only [scatterBit,ite_eq_right h,List.mem_cons,forall_eq_or_imp,ne_eq]
      rw [code]
      tauto

/-- Scattering the advice list on its first saturation produces precisely the new packed words,
including in the presence of repeated colors at different positions of the same string. -/
theorem scatter_saturation {B ℓ : ℕ} (width : ℕ) (pos : 0<width)
    (strings : MaskIndex B → Fin ℓ → Fin B) (full : Finset (Fin B)) (c : Fin B)
    (r : MaskIndex B) (chunk : ℕ) :
    ((occurrences strings c).foldl (scatterBit width r chunk) (word (strings r) full width chunk)) =
      word (strings r) (insert c full) width chunk := by
  apply Nat.eq_of_testBit_eq
  intro t
  apply Bool.eq_iff_iff.mpr
  by_cases ht : t<width
  · rw [scatter_list _ pos _ _ _ _ ht,word_test,word_test]
    simp only [ht,true_and,mem_insert,not_or,mem_occurrences]
    constructor
    · rintro ⟨⟨i,hi,hgood⟩,h⟩
      refine ⟨i,hi,?_,hgood⟩
      intro he
      exact (h (r,i) he).elim (fun e => e rfl) (fun e => e hi)
    · rintro ⟨i,hi,hne,hgood⟩
      refine ⟨⟨i,hi,hgood⟩,?_⟩
      rintro ⟨s,j⟩ hcolor
      by_contra! bad
      obtain ⟨rfl,hj⟩ := bad
      exact hne (by have e : j=i := Fin.ext (hj.trans hi.symm); subst j; exact hcolor)
  · have no : (word (strings r) (insert c full) width chunk).testBit t ≠ true :=
      fun h => ht ((word_test ..).1 h).1
    have initial : (word (strings r) full width chunk).testBit t ≠ true :=
      fun h => ht ((word_test ..).1 h).1
    suffices ∀ (L : List (Pos B ℓ)) (x : ℕ), x.testBit t ≠ true →
        (L.foldl (scatterBit width r chunk) x).testBit t ≠ true from iff_of_false (this _ _ initial) no
    intro L
    induction L with
    | nil => simp
    | cons p rest ih =>
      intro x hx
      apply ih
      simp only [scatterBit]
      split <;> simp [hx]

end Hierarchy.ProbeStage.PackedMask

end OAI
