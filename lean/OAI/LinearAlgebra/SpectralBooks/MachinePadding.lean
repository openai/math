import OAI.LinearAlgebra.SpectralBooks.SignedMachine
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# Fixed-length guesses for the signed witness

The deterministic verifier reads a guess only when a step requests a fresh bit. At a valid
halt it accepts the signed output only if all unread guesses are zero. Thus each computation
path has a unique padded guess string, even when different paths reach the same configuration.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

namespace SignedMachine

variable {C : Type*}

/-- Execute the branch addressed by the guess string. Report zero on timeout, failure,
exhaustion of the guesses at a branch, or a nonzero unused suffix. -/
def paddedOutput (next : C → Outcome C) : ℕ → C → {g : ℕ} → (Fin g → Bool) → Output
  | 0, _, _, _ => .zero
  | fuel + 1, cfg, g, bits =>
    match next cfg with
    | .fail => .zero
    | .halt out => if bits = (fun _ ↦ false) then out else .zero
    | .step c => paddedOutput next fuel c bits
    | .branch a b =>
      match g, bits with
      | 0, _ => .zero
      | _ + 1, bs => paddedOutput next fuel (if bs 0 then b else a) (Fin.tail bs)

/-- Integer value of the deterministic verifier's signed output. -/
def paddedRun (next : C → Outcome C) (fuel : ℕ) (cfg : C) {g : ℕ} (bits : Fin g → Bool) : ℤ :=
  (paddedOutput next fuel cfg bits).value

private theorem sum_cons {g : ℕ} (f : (Fin (g + 1) → Bool) → ℤ) :
    ∑ bits, f bits =
      (∑ tail, f (Fin.cons false tail)) + ∑ tail, f (Fin.cons true tail) := by
  let e := Fin.consEquiv fun _ : Fin (g + 1) ↦ Bool
  rw [← e.sum_comp f, Fintype.sum_prod_type, Fintype.sum_bool, add_comm]
  rfl

/-- Summing over all fixed-length guesses recovers the signed path sum. Any guess length
at least the clock bound gives the same sum. -/
theorem sum_paddedRun (next : C → Outcome C) (fuel : ℕ) (cfg : C) {g : ℕ}
    (h : fuel ≤ g) : ∑ bits : Fin g → Bool, paddedRun next fuel cfg bits = run next fuel cfg := by
  induction fuel generalizing g cfg with
  | zero => simp [run, paddedRun, paddedOutput, Output.value]
  | succ fuel ih =>
    cases g with
    | zero => omega
    | succ g =>
      cases e : next cfg with
      | fail => simp [run, paddedRun, paddedOutput, e, Output.value]
      | halt out =>
        have hz : Output.zero.value = 0 := rfl
        simp [run, paddedRun, paddedOutput, e, apply_ite Output.value, hz]
      | step c =>
        simpa [run, paddedRun, paddedOutput, e] using ih c (g := g + 1) (by omega)
      | branch a b =>
        rw [sum_cons]
        simpa [run, paddedRun, paddedOutput, e] using
          congrArg₂ (· + ·) (ih a (g := g) (by omega)) (ih b (g := g) (by omega))

/-- The signed count is the difference between two ordinary counts of padded guesses. -/
theorem run_eq_card_pos_sub_card_neg (next : C → Outcome C) (fuel : ℕ) (cfg : C)
    {g : ℕ} (h : fuel ≤ g) :
    run next fuel cfg =
      ((Finset.univ.filter fun bits : Fin g → Bool ↦ paddedOutput next fuel cfg bits = .pos).card : ℤ) -
      (Finset.univ.filter fun bits : Fin g → Bool ↦ paddedOutput next fuel cfg bits = .neg).card := by
  have score (o : Output) : o.value = (if o = .pos then 1 else 0) - (if o = .neg then 1 else 0) := by
    cases o <;> decide
  rw [← sum_paddedRun next fuel cfg h]
  simp_rw [paddedRun, score, Finset.sum_sub_distrib]
  simp

end SignedMachine

end SpectralBooks
end LinearAlgebra
end OAI
