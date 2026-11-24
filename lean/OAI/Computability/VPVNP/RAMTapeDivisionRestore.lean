import OAI.Computability.VPVNP.RAMTapeDivisionCore

/-!
# Restore scan for binary division

Each iteration restores one divisor bit and consumes the corresponding bits
of both possible remainders. The borrow from the forward scan determines
which bit is written. Reversing the three scratch stacks in this way puts
the resulting words back in least-significant-bit-first order.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace TapeWord.DivisionStack

private theorem restoreAux (feed q ds os ts d r : List Bool) (borrow : Bool)
    (ho : os.length = ds.length) (ht : ts.length = ds.length) :
    Run (5 * ds.length + 1) (.restore borrow) ⟨[], feed, d, r, q, ds, os, ts⟩
      (.digit borrow) ⟨[], feed, ds.reverse ++ d,
        (if borrow then os else ts).reverse ++ r, q, [], [], []⟩ := by
  induction ds generalizing os ts d r with
  | nil =>
    have hos : os = [] := List.length_eq_zero_iff.mp ho
    have hts : ts = [] := List.length_eq_zero_iff.mp ht
    subst os ts
    simp only [ite_self, List.reverse_nil, List.nil_append]
    exact prepend rfl (.nil ..)
  | cons b bs ih =>
    cases os with
    | nil => simp at ho
    | cons a as =>
      cases ts with
      | nil => simp at ht
      | cons c cs =>
        have tail := ih as cs (b :: d) ((if borrow then a else c) :: r)
          (Nat.succ.inj ho) (Nat.succ.inj ht)
        have selected : (if borrow then a :: as else c :: cs) =
            (if borrow then a else c) :: (if borrow then as else cs) := by cases borrow <;> rfl
        simp only [selected, List.reverse_cons, List.append_assoc, List.singleton_append,
          List.length_cons, Nat.mul_succ]
        exact prepend rfl (prepend rfl (prepend rfl (prepend rfl (prepend rfl tail))))

/-- Restore the divisor and select the low word of the old or trial
remainder. The final empty pop transfers control to the quotient digit. -/
theorem restoreRun (feed q d original diff : List Bool) (borrow : Bool)
    (h₁ : original.length = d.length) (h₂ : diff.length = d.length) :
    Run (5 * d.length + 1) (.restore borrow)
      ⟨[], feed, [], [], q, d.reverse, original.reverse, diff.reverse⟩
      (.digit borrow) ⟨[], feed, d, if borrow then original else diff, q, [], [], []⟩ := by
  have h := restoreAux feed q d.reverse original.reverse diff.reverse [] [] borrow
    (by simpa using h₁) (by simpa using h₂)
  cases borrow <;> simpa using h

end TapeWord.DivisionStack

end VPVNP
end Computability
end OAI
