import OAI.Computability.NearSquareRoot.InterchangeTable
import OAI.Computability.NearSquareRoot.KernelSwapRepair
import OAI.Computability.IntegerMultiplication.Bits.Word

/-!
# A fixed bit encoding for the repair alphabet

For fixed repair parameters there is one codeword length for each coefficient.
The same encoding is used on both sides of a recursive interchange. The
pointwise Hermite correction is a P192 stack program operating on finite
records, with its local work linear in the number of addresses.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace InterchangeAlphabet

open IntegerMultiplication.Code IntegerMultiplication.Strip NearSquareRoot.SwapRepair

noncomputable section

/-- Width of a fixed-length code for a finite alphabet. -/
def width (A : Type) [Finite A] := Nat.clog 2 (Nat.card A)

private def codeBits (A : Type) [Finite A] : A ↪ (Fin (width A) → Bool) := by
  classical
  letI := Fintype.ofFinite A
  apply Classical.choice
  apply Function.Embedding.nonempty_of_card_le
  simpa only [width, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin, Nat.card_eq_fintype_card] using
    Nat.le_pow_clog (by decide : 1 < 2) (Nat.card A)

/-- One coefficient occupies exactly one fixed-length Boolean word. -/
def word {A : Type} [Finite A] (a : A) : List Bool := List.ofFn (codeBits A a)

theorem word_length {A : Type} [Finite A] (a : A) : (word a).length = width A := by
  simp [word]

theorem word_injective {A : Type} [Finite A] : Function.Injective (word (A := A)) :=
  List.ofFn_injective.comp (codeBits A).injective

private theorem send_bits_injective : Function.Injective (send (X := List Bool)) := by
  intro a
  induction a with
  | nil =>
    intro b h
    cases b with
    | nil => rfl
    | cons => simp only [send_nil, send_cons] at h; contradiction
  | cons a l ih =>
    intro b h
    cases b with
    | nil => simp only [send_nil, send_cons] at h; contradiction
    | cons b k =>
      simp only [send_cons, Tree.fork.injEq] at h
      exact congrArg₂ List.cons (Tree.atom.inj h.1) (ih h.2)

/-- Prefix-tree representation in the P192 stream interpreter. -/
def symbol {A : Type} [Finite A] (a : A) := send (word a)

theorem symbol_injective {A : Type} [Finite A] : Function.Injective (symbol (A := A)) :=
  send_bits_injective.comp word_injective

theorem symbol_cells {A : Type} [Finite A] (a : A) : (symbol a).count = 2 * width A + 1 := by
  change size (word a) = _
  rw [IntegerMultiplication.Bits.size_word, word_length]

/-- Lift a bit stream to the two distinct elements zero and one of the data ring. -/
def bitValue (A : Type) [Zero A] [One A] (b : Bool) : A := if b then 1 else 0

theorem bitValue_injective (A : Type) [MulZeroOneClass A] [Nontrivial A] :
    Function.Injective (bitValue A) := by
  intro b c h
  cases b <;> cases c <;> simp_all [bitValue]

/-- Both the initial conversion from input bits and the final extraction
of permuted bits have linear P192 run certificates. -/
theorem bit_conversions (A : Type) [Finite A] [MulZeroOneClass A] [Nontrivial A]
    {I : Type} {P : I → Type} (points : (i : I) → Series (P i))
    (v : (i : I) → P i → Bool) :
    let plain := stackRun points (fun i j => send (v i j))
    let packed := stackRun points (fun i j => symbol (bitValue A (v i j)))
    let cost := fun i => ((points i).count : ℝ) + 1
    Carries cost plain packed ∧ Carries cost packed plain :=
  ⟨interchange_record_table points v send (symbol ∘ bitValue A) FiniteState.identify,
   interchange_record_table points v (symbol ∘ bitValue A) send
     (symbol_injective.comp (bitValue_injective A))⟩

/-- Finite check data passed to and returned by the Hermite table. -/
abbrev CheckData (R : Type) [CommRing R] (m : ℕ) :=
  (Fin (checks m) → Coeff R m) × (Fin (checks m) → Coeff R m)

local instance {R : Type} [CommRing R] [Nontrivial R] [Finite R] (m : ℕ) :
    Finite (Coeff R m) := finite_coeff R m

/-- Each record contains the sign bits and the two blocks of check values
already in spectral order. Evaluate the fixed Hermite solver across the
entire stream with a single charged stack program. -/
theorem hermite_table {R : Type} [CommRing R] [Nontrivial R] [Finite R] {m : ℕ}
    (T : Table R m) {I : Type} {P : I → Type} (points : (i : I) → Series (P i))
    (pattern : (i : I) → P i → Pattern m) (checksIn : (i : I) → P i → CheckData R m) :
    Carries (fun i => ((points i).count : ℝ) + 1)
      (stackRun points fun i j => .fork (symbol (pattern i j)) (symbol (checksIn i j)))
      (stackRun points fun i j => symbol ((T (pattern i j)) (checksIn i j))) := by
  let pairCode (x : Pattern m × CheckData R m) := Tree.fork (symbol x.1) (symbol x.2)
  have hi : Function.Injective pairCode := by
    intro a b h
    exact Prod.ext (symbol_injective (Tree.fork.inj h).1) (symbol_injective (Tree.fork.inj h).2)
  exact interchange_record_table points (fun i j => (pattern i j, checksIn i j))
    pairCode (fun x => symbol (T x.1 x.2)) hi

end
end InterchangeAlphabet

end NearSquareRoot
end Computability
end OAI
