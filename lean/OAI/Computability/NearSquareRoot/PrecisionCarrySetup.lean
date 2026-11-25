import OAI.Computability.IntegerMultiplication.Code.Dup
import OAI.Computability.NearSquareRoot.PrecisionCarryCost
import Mathlib.Tactic.Ring

/-! # Preparing the carry packet on the stacks

Starting with one radix ruler and one length ruler, the stream pass obtains the
number of coefficient words from the stream, duplicates the radix ruler once
per word, and doubles the length ruler for the output. All traversals are
charged in the P192 command language.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

open IntegerMultiplication Code Bits

private abbrev CarrySource := Tally × Tally × List Word

private def rulers (p : CarrySource) : (Tally × Tally) × CarrySource :=
  ((ruler p.2.2, p.2.1), p)

private def orderCarry (p : List Tally × CarrySource) : Tally × List Word × List Tally × Tally :=
  (p.2.1 ++ p.2.1, p.2.2.2, p.1, p.2.2.1)

/-- Setup of the full P192 carry-packet representation from two shared rulers
and a compact list of little-endian coefficient words. -/
theorem prepareCarry {I : Type*} (n b m N k : I → ℕ) (words : (i : I) → Fin (m i) → Word)
    (hw : ∀ i j, (words i j).length ≤ 3*b i) (hm : ∀ i, m i ≤ N i)
    (hb : ∀ i, b i ≤ 2*k i) (hn : ∀ i, n i ≤ N i*k i)
    (hN : ∀ i, 1 ≤ N i) (hk : ∀ i, 1 ≤ k i) :
    Task (fun i => N i*k i)
      (fun i => send (tally (n i), tally (b i), List.ofFn (words i)))
      (fun i => send (tally (2*n i), List.ofFn (words i), List.replicate (m i) (tally (b i)),
        tally (b i))) := by
  let input (i : I) : CarrySource := (tally (n i), tally (b i), List.ofFn (words i))
  let args (i : I) := (rulers (input i)).1
  let repeated (i : I) := List.replicate (args i).1.length (args i).2
  have before : Easy rulers := by unfold rulers; fun_prop
  have after : Easy orderCarry := by unfold orderCarry; fun_prop
  have dup := ((Code.generate (X := Tally)).on args).left (fun i => send (input i))
  have first := before.on input
  have join : Task (fun i => size (input i) + ((args i).1.length+1)*size (args i).2)
      (fun i => send (input i)) (fun i => send (repeated i, input i)) := first.compose dup
  have all := join.compose (after.on fun i => (repeated i, input i))
  have len (i) : (args i).1.length = m i := by simp [args,rulers,input]
  have expansion (i) : repeated i = List.replicate (m i) (tally (b i)) := by
    dsimp only [repeated]
    rw [len]
    rfl
  refine (all.conform (fun _ => rfl) (fun _ => rfl) (fun i => ?_)).bound 120 ?_
  · change send (tally (n i) ++ tally (n i), List.ofFn (words i), repeated i, tally (b i)) = _
    rw [expansion]
    simp only [tally, ← List.replicate_add, two_mul]
  · intro i
    have S := carryInputSize_le_volume (words i) (hw i) (hm i) (hb i) (hn i) (hN i) (hk i)
    have count : m i ≤ N i*k i := (hm i).trans (Nat.le_mul_of_pos_right _ (hk i))
    have w : k i ≤ N i*k i := Nat.le_mul_of_pos_left _ (hN i)
    have mb : m i*b i ≤ 2*(N i*k i) := by
      calc
        m i*b i ≤ N i*(2*k i) := Nat.mul_le_mul (hm i) (hb i)
        _ = _ := by ring
    dsimp only [input]
    rw [len, expansion]
    simp only [args, rulers, input, size_prod, size_tally, tally_length] at S ⊢
    have B := hb i
    nlinarith

end NearSquareRoot
end Computability
end OAI
