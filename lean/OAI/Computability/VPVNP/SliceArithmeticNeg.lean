import OAI.Computability.VPVNP.SliceArithmeticAddCall

/-!
# Destructive negation of a packed field scalar

The caller holds the input scalar in the accumulator and an empty query stack.
A copy of the scalar supplies the second input stream of the coefficientwise
scan. Each row computes the modular negation of the first input. The scan
consumes the copy and returns the negated scalar on the accumulator stack.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace SliceArithmetic.NegCall

open RAMTape BurstRAM
open SliceArithmeticRound (packed)
open MultiplyCall (External external)
open AddCall (clean)

private def scratch : AddCall.Port := .inl (.inr .scratch)

/-- Negate the packed accumulator coefficientwise using a private copy on the query port. -/
def machine : FiniteRoutine AddCall.Port :=
  (SuccessorFields.prependCopy (.inr .acc) (.inr .query) scratch).followedBy (AddCall.operation .neg)

theorem machine_runs {p e w : ℕ} [NeZero p] (hw : Word.workingWidth p ≤ w)
    (a : Vector p e) (coeff : List Bool) :
    ∃ t ≤ 5 * (e * w) + 2 + AddCall.callCap e w, machine.Runs t
      (clean (external p e w coeff [] (packed w (List.ofFn a))))
      (clean (external p e w coeff [] (packed w (List.ofFn fun i => -a i)))) := by
  let x := packed w (List.ofFn a)
  let entry := clean (external p e w coeff [] x)
  let staged := clean (external p e w coeff x x)
  have copy := SuccessorFields.prependCopy_runs (Sum.inr External.acc : AddCall.Port)
    (.inr .query) scratch (by decide) (by decide) (by decide) entry rfl
  have hstage : Function.update entry (.inr .query) (entry (.inr .acc) ++ entry (.inr .query)) = staged := by
    funext i
    cases i with
    | inl i => rfl
    | inr i => cases i <;> simp [entry, staged, AddCall.clean, external]
  have hlen : (entry (.inr .acc)).length = e * w := by simp [entry, x, AddCall.clean, external]
  rw [hstage, hlen] at copy
  obtain ⟨u, hu, run⟩ := AddCall.operation_runs .neg hw a a coeff
  exact ⟨_, Nat.add_le_add_left hu _, copy.followedBy run⟩

/-- The destructive operation realizes the additive inverse in the quotient ring. -/
theorem value_neg {p e : ℕ} [NeZero p] (f : Polynomial (ZMod p)) (v : Vector p e) :
    value f (fun i => -v i) = -value f v := by
  simp only [value, cast_val_eq_finEquiv, map_neg, neg_mul, Finset.sum_neg_distrib]

end SliceArithmetic.NegCall

end VPVNP
end Computability
end OAI
