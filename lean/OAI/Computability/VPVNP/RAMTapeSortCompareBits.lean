import OAI.Computability.VPVNP.RAMTapeBoundaryRecord
import OAI.Computability.VPVNP.RAMSortCompareCost
import OAI.Computability.VPVNP.RAMTapeSuccessorTags

/-!
# Finite bit summaries for physical record comparison

The sorter scans each five-word record from its tag through its probe
ordinal. Within a word, the most recent unequal pair of bits decides the
unsigned order. Only the low two bits and the presence of a higher set bit
matter for tag validation. The summaries therefore use a fixed finite state
space independent of the word width.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RAMTape.Sorter

open BurstRAM RAMSort RAMBoundary TapeWord

/-- A low-order result is retained only while all remaining high bits agree. -/
def orderStep (o : Ordering) (a b : Bool) : Ordering :=
  if a = b then o else if a then .gt else .lt

private def orderWith (a b : ℕ) (tie : Ordering) : Ordering :=
  if a < b then .lt else if b < a then .gt else tie

private theorem order_fold (o : Ordering) (xs ys : List Bool) (h : xs.length = ys.length) :
    Boundary.Field.fold orderStep o xs ys = orderWith (value xs) (value ys) o := by
  induction xs generalizing ys o with
  | nil => cases ys <;> simp_all [Boundary.Field.fold, orderWith, value]
  | cons x xs ih =>
    cases ys with
    | nil => simp at h
    | cons y ys =>
      rw [Boundary.Field.fold, ih _ ys (Nat.succ.inj h)]
      rcases lt_trichotomy (value xs) (value ys) with hlt | he | hgt <;> cases x <;> cases y <;>
        simp [value, orderStep, orderWith] <;> grind

/-- Finite state of one word scan. The bounded tag observations also detect
an all-zero payload word without storing its numerical value. -/
structure WordState where
  /-- Finite tag-decoder state summarizing the bits scanned so far in the left word. -/
  lhs : SuccessorTags.State
  /-- Finite tag-decoder state summarizing the bits scanned so far in the right word. -/
  rhs : SuccessorTags.State
  /-- Unsigned order of the two little-endian prefixes. A later unequal pair of bits supersedes
  the earlier order. -/
  ord : Ordering
  deriving DecidableEq

instance sorterOrderingFintype : Fintype Ordering := ⟨{.lt,.eq,.gt}, fun q ↦ by cases q <;> simp⟩

instance : Fintype WordState := derive_fintype% _

/-- Start a field comparison with both tag decoders empty and the operand words provisionally
equal. -/
def WordState.start : WordState := ⟨.first,.first,.eq⟩

/-- Feed one bit from each operand to its tag decoder and update the unsigned order at this bit
position. -/
def WordState.step (s : WordState) (x y : Bool) : WordState :=
  ⟨SuccessorTags.advance s.lhs x, SuccessorTags.advance s.rhs y, orderStep s.ord x y⟩

private theorem word_fold (s : WordState) (xs ys : List Bool) (h : xs.length = ys.length) :
    Boundary.Field.fold WordState.step s xs ys =
      ⟨xs.foldl SuccessorTags.advance s.lhs, ys.foldl SuccessorTags.advance s.rhs,
        Boundary.Field.fold orderStep s.ord xs ys⟩ := by
  induction xs generalizing ys s with
  | nil => cases ys <;> simp_all [Boundary.Field.fold]
  | cons x xs ih =>
    cases ys with
    | nil => simp at h
    | cons y ys =>
      rw [Boundary.Field.fold, ih _ ys (Nat.succ.inj h)]
      rfl

theorem wordState_spec {w : ℕ} (a b : Word w) :
    let s := Boundary.Field.fold WordState.step WordState.start (wordBits a) (wordBits b)
    SuccessorTags.finish s.lhs = SuccessorTags.Tag.ofNat a.val ∧
      SuccessorTags.finish s.rhs = SuccessorTags.Tag.ofNat b.val ∧
      s.ord = compare a.val b.val := by
  have h : (wordBits a).length = (wordBits b).length := by simp
  simp only [word_fold _ _ _ h, WordState.start, SuccessorTags.finish_fold, order_fold _ _ _ h, value_wordBits, true_and]
  simp only [orderWith, compareOfLessAndEq, compare]
  split_ifs <;> grind

end RAMTape.Sorter

end VPVNP
end Computability
end OAI
