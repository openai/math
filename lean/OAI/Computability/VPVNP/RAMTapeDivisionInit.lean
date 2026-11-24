import OAI.Computability.VPVNP.RAMTapeDivisionCore

/-!
# Initialization and division by zero on bit stacks

Reversing the input exposes the dividend in most-significant-bit order.
While saving the divisor the machine records whether any bit is set and
allocates a zero remainder cell for each divisor bit. Restoring the saved
divisor then branches on the computed nonzero flag.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace TapeWord.DivisionStack

open RAMTape

private theorem reverseInputRun (x feed d : List Bool) :
    Run (2 * x.length + 1) .reverseInput ⟨x, feed, d, [], [], [], [], []⟩
      (.init false) ⟨[], x.reverse ++ feed, d, [], [], [], [], []⟩ := by
  induction x generalizing feed with
  | nil =>
    apply prepend (by rfl)
    exact .nil ..
  | cons b xs ih =>
    rw [List.length_cons, Nat.mul_succ,
      show 2 * xs.length + 2 + 1 = (2 * xs.length + 1 + 1) + 1 by omega]
    apply prepend (by rfl)
    apply prepend (by rfl)
    simpa [Data.set, Data.stacks, List.append_assoc] using ih (b :: feed)

private theorem saveInitRun (flag : Bool) (feed d rem saved : List Bool) :
    Run (3 * d.length + 1) (.init flag) ⟨[], feed, d, rem, [], saved, [], []⟩
      (.restoreInit (flag || d.any id))
      ⟨[], feed, [], List.replicate d.length false ++ rem, [], d.reverse ++ saved, [], []⟩ := by
  induction d generalizing flag rem saved with
  | nil =>
    simp only [List.length_nil, Nat.mul_zero, Nat.zero_add, List.any_nil,
      Bool.or_false, List.replicate_zero, List.nil_append, List.reverse_nil]
    apply prepend (by rfl)
    exact .nil ..
  | cons b ds ih =>
    rw [List.length_cons, Nat.mul_succ,
      show 3 * ds.length + 3 + 1 = ((3 * ds.length + 1 + 1) + 1) + 1 by omega]
    apply prepend (by rfl)
    apply prepend (by rfl)
    apply prepend (by rfl)
    simpa [Data.set, Data.stacks, List.any_cons, Bool.or_assoc, List.append_assoc, List.replicate_succ']
      using ih (flag || b) (false :: rem) (b :: saved)

private theorem restoreInitRun (flag : Bool) (feed d rem saved : List Bool) :
    Run (2 * saved.length + 1) (.restoreInit flag) ⟨[], feed, d, rem, [], saved, [], []⟩
      (if flag then .outer else .clearRemainder) ⟨[], feed, saved.reverse ++ d, rem, [], [], [], []⟩ := by
  induction saved generalizing d with
  | nil =>
    apply prepend (by rfl)
    exact .nil ..
  | cons b ds ih =>
    rw [List.length_cons, Nat.mul_succ,
      show 2 * ds.length + 2 + 1 = (2 * ds.length + 1 + 1) + 1 by omega]
    apply prepend (by rfl)
    apply prepend (by rfl)
    simpa [Data.set, Data.stacks, List.append_assoc] using ih (b :: d)

/-- The initial scans detect a zero divisor at every width, including zero.
They consume the dividend stack, restore the divisor, and prepare a zero
remainder of exactly the divisor's width. -/
theorem initRun (x d : List Bool) :
    Run (2 * x.length + 5 * d.length + 3) .reverseInput ⟨x, [], d, [], [], [], [], []⟩
      (if d.any id then .outer else .clearRemainder)
      ⟨[], x.reverse, d, List.replicate d.length false, [], [], [], []⟩ := by
  have h₁ := reverseInputRun x [] d
  have h₂ := saveInitRun false x.reverse d [] []
  have h₃ := restoreInitRun (d.any id) x.reverse [] (List.replicate d.length false) d.reverse
  simp only [List.append_nil, List.length_reverse, List.reverse_reverse, Bool.false_or] at h₁ h₂ h₃
  convert (h₁.trans h₂).trans h₃ using 1
  omega

private theorem clearRemainderRun (feed d rem : List Bool) :
    Run (rem.length + 1) .clearRemainder ⟨[], feed, d, rem, [], [], [], []⟩
      .zeroLoop ⟨[], feed, d, [], [], [], [], []⟩ := by
  induction rem with
  | nil =>
    apply prepend (by rfl)
    exact .nil ..
  | cons b rs ih =>
    apply prepend (by rfl)
    exact ih

private theorem zeroLoopRun (feed d rem quot : List Bool) :
    Run (3 * feed.length + 1) .zeroLoop ⟨[], feed, d, rem, quot, [], [], []⟩
      .done ⟨[], [], d, feed.reverse ++ rem, List.replicate feed.length false ++ quot, [], [], []⟩ := by
  induction feed generalizing rem quot with
  | nil =>
    apply prepend (by rfl)
    exact .nil ..
  | cons b bs ih =>
    rw [List.length_cons, Nat.mul_succ,
      show 3 * bs.length + 3 + 1 = ((3 * bs.length + 1 + 1) + 1) + 1 by omega]
    apply prepend (by rfl)
    apply prepend (by rfl)
    apply prepend (by rfl)
    simpa [Data.set, Data.stacks, List.append_assoc, List.replicate_succ'] using ih (b :: rem) (false :: quot)

/-- After zero-divisor detection the machine returns an all-zero quotient
and the original dividend as remainder, both at the dividend's width. -/
theorem zeroRun (x d : List Bool) :
    Run (d.length + 3 * x.length + 2) .clearRemainder
      ⟨[], x.reverse, d, List.replicate d.length false, [], [], [], []⟩
      .done ⟨[], [], d, x, List.replicate x.length false, [], [], []⟩ := by
  have h₁ := clearRemainderRun x.reverse d (List.replicate d.length false)
  have h₂ := zeroLoopRun x.reverse d [] []
  simp only [List.length_replicate, List.length_reverse, List.reverse_reverse,
    List.append_nil] at h₁ h₂
  convert h₁.trans h₂ using 1
  omega

end TapeWord.DivisionStack

end VPVNP
end Computability
end OAI
