import OAI.Computability.IntegerMultiplication.Bits.Word
import OAI.Computability.NearSquareRoot.ShortWordError

/-! # Signed fixed-point record products

A record contains two sign-magnitude words in most-significant-bit-first order
and a unary ruler recording their common number of fractional bits. The
unsigned integer product is computed at full precision. We discard its low
fractional bits and attach the product sign. All copying, splitting, and
reversing of records is included in the stack program's time bound.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace ShortWord.FixedPoint
open IntegerMultiplication IntegerMultiplication.Code

abbrev SignedWord := Bool × List Bool
abbrev ProductInput := (SignedWord × SignedWord) × Tally

private def prepare (i : ProductInput) :
    (List Bool × List Bool) × (Bool × Tally) :=
  ((i.1.1.2, i.1.2.2), (i.1.1.1 ^^ i.1.2.1, i.2))

private theorem prepare_easy : Easy prepare := by
  have hx : Easy (fun i : ProductInput => (i.1.1.1, i.1.2.1)) := by fun_prop
  have hs := hx.compose (Easy.finite (fun s : Bool × Bool => s.1 ^^ s.2))
  exact (show Easy (fun i : ProductInput => (i.1.1.2, i.1.2.2)) by fun_prop).pair
    (hs.pair (by fun_prop))

/-- Truncate a full product to the common input grid, rounding towards zero.
The record can represent signed zero, which has the usual value zero. -/
def truncate (w : List Bool) (s : Bool) (p : ℕ) : SignedWord :=
  (s, (w.reverse.drop p).reverse)

private def finish (i : List Bool × (Bool × Tally)) : SignedWord :=
  truncate i.1 i.2.1 i.2.2.length

private theorem finish_easy : Easy finish := by
  change Easy (fun i : List Bool × (Bool × Tally) =>
    (i.2.1, (cutLists (i.2.2, i.1.reverse)).2.reverse))
  have h : Easy (fun i : List Bool × (Bool × Tally) => (i.2.2, i.1.reverse)) := by fun_prop
  exact (show Easy (fun i : List Bool × (Bool × Tally) => i.2.1) by fun_prop).pair
    ((easy_cut h).sndCompose.compose Easy.reverse)

/-- Frame a word multiplier with the signed fixed-point input and output
adapters. The unary precision ruler is ordinary input read by this one
program, so its value may vary between invocations. -/
theorem task {I : Type*} (i : I → ProductInput) (w : I → List Bool) (b : I → ℕ)
    (mul : Task b (fun a => send ((i a).1.1.2, (i a).1.2.2)) (fun a => send (w a))) :
    Task (fun a => b a + (i a).1.1.2.length + (i a).1.2.2.length +
        (w a).length + (i a).2.length)
      (fun a => send (i a))
      (fun a => send (truncate (w a) ((i a).1.1.1 ^^ (i a).1.2.1) (i a).2.length)) := by
  let ctx (a : I) := ((i a).1.1.1 ^^ (i a).1.2.1, (i a).2)
  have load := Task.on prepare_easy i
  have call := mul.left (fun a => send (ctx a))
  have save := Task.on finish_easy (fun a => (w a, ctx a))
  apply ((load.compose call).compose save).bound 20
  intro a
  dsimp only [ctx]
  simp only [size_prod, size_bit, Bits.size_word, size_tally]
  omega

/-- Width and real error of the returned signed word, given correctness of the
full-precision unsigned multiplier. -/
theorem truncate_spec (x y : SignedWord) (w : List Bool) (p : ℕ)
    (hw : bitValue w = bitValue x.2 * bitValue y.2) :
    let z := truncate w (x.1 ^^ y.1) p
    z.2.length = w.length - p ∧
      |signedDyadic z.1 (bitValue z.2) p -
        signedDyadic x.1 (bitValue x.2) p * signedDyadic y.1 (bitValue y.2) p| <
          1 / (2 : ℝ)^p := by
  dsimp only [truncate]
  constructor
  · simp
  · rw [bitValue_drop_low, hw]
    exact signedDyadic_mul_error _ _ _ _ _

end ShortWord.FixedPoint

end NearSquareRoot
end Computability
end OAI
