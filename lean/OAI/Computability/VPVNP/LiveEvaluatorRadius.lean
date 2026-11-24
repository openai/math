import OAI.Computability.VPVNP.LiveEvaluatorTail
import OAI.Computability.VPVNP.PolynomialBounds

/-!
# One length-dependent window for all middle-cut inputs

The raw input length and reachable stack storage are polynomially bounded
independently of the particular accumulated exponents. A fixed power of the
input length thus provides the radius the live RAM computes. The exponent
is chosen before the later group-width and processor constants.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace LiveEvaluatorRadius

open LiveEvaluatorEncoding LiveEvaluatorTail UniversalMachine RAMTape RAMTape.StackCompiler

/-- Enlarging a head-relative window retains all the data of a bounded state. -/
theorem fits_mono {extra A B : ℕ} (h : A ≤ B) (s : EvaluatorTail.State extra)
    (hs : StateFits A s) : StateFits B s := by
  cases s with
  | accepted | rejected => trivial
  | running c =>
    have enlarge (t : Turing.Tape Symbol) (ht : TapeFits A t) : TapeFits B t :=
      fun j hj => ht j (by omega)
    exact ⟨hs.1, enlarge _ hs.2.1, enlarge _ hs.2.2⟩

/-- A single exponent and threshold bound the relative tape radius for every
admissible middle input and stack bound at each length. -/
theorem exists_length_radius {inputLength stackSpace : ℕ → ℕ}
    (hl : PolynomiallyBounded inputLength) (hs : PolynomiallyBounded stackSpace) :
    ∃ m N : ℕ, ∀ n ≥ N, ∀ l ≤ inputLength n, ∀ b ≤ stackSpace n,
      l + (7 * b + 4) + (7 * b + 4) ≤ n ^ m := by
  have hr := ((PolynomiallyBounded.const 7).mul hs).add (.const 4)
  obtain ⟨A, k, N, hN⟩ := (hl.add hr).add hr
  refine ⟨k + 1, max A N, fun n hn l hL b hB => ?_⟩
  have hle := hN n ((le_max_right ..).trans hn)
  have hr' : 7 * b + 4 ≤ 7 * stackSpace n + 4 := by omega
  exact (Nat.add_le_add (Nat.add_le_add hL hr') hr').trans <| hle.trans <| by
    rw [pow_succ, mul_comm]
    exact Nat.mul_le_mul_left _ ((le_max_left ..).trans hn)

/-- Apply the literal tail count at the common, length-only radius.
Each input may use strictly less stack storage and fewer input bits. -/
theorem card_labeled_of_le {K Q : Type*} [DecidableEq K] [Fintype K] [Fintype Q]
    (input : K) (code : StackCode K Q) (start : Q) (raw : Word) {B M : ℕ}
    (bounded : ∀ ⦃q s⦄, Reach code start (labeledInput input raw) q s →
      Fintype.card K + 1 + ∑ a, (s a).length ≤ B)
    (fits : raw.length + (7 * B + 4) + (7 * B + 4) ≤ M)
    {h w Δ : ℕ} (layout : Layout (labeledProgram input code start).extra M w Δ) :
    let p := labeledProgram input code start
    Nat.card (Runs (h := h) layout (initialCode M (initial p raw))) = paths p (2 ^ h) (initial p raw) := by
  let p := labeledProgram input code start
  have hf (t : ℕ) (bits : Fin t → Bool) (i : Fin (t+1)) :
      StateFits M (EvaluatorTail.history p t (initial p raw) bits i) :=
    fits_mono fits _ (LiveEvaluatorSpace.history_fits_labeled input code start raw bounded t bits i)
  exact card_runs layout (initial p raw) (initialCode M (initial p raw))
    (initialCode_toState _ (hf 0 Fin.elim0 0)) (fun bits _ i => hf _ bits i)

end LiveEvaluatorRadius

end VPVNP
end Computability
end OAI
