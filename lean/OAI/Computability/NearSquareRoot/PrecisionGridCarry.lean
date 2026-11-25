import OAI.Computability.NearSquareRoot.PrecisionGridRecover
import OAI.Computability.NearSquareRoot.PrecisionCarry

/-! # Passing a recovered coefficient stream to the carry program

The shared natural input length, radix and fractional precision are given as
unary rulers. The scan recovers and resizes each coefficient to three radix
blocks before the carry pass. Its two carried parameters are preserved.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace FixedPoint

open IntegerMultiplication IntegerMultiplication.Code IntegerMultiplication.Bits

/-- Working packet from the end of the inverse CRT permutation: input width,
radix width, fractional precision and the marked grid records in natural order. -/
def decodePacket {m w : ℕ} (n b p : ℕ) (x : Fin m → Dusk.Grain w) :
    Tally × Tally × Tally × List Dusk.Pair :=
  (tally n, tally b, tally p, List.ofFn (fun j => Dusk.mark (x j)))

private def setWidths (i : Tally × Tally × Tally × List Dusk.Pair) :
    Tally × Tally × (Tally × Tally) × List Dusk.Pair :=
  (i.1, i.2.1, (i.2.2.1, i.2.1 ++ i.2.1 ++ i.2.1), i.2.2.2)

private theorem setWidths_easy : Easy setWidths := by
  unfold setWidths
  fun_prop

private theorem setWidths_decodePacket {m w : ℕ} (n b p : ℕ) (x : Fin m → Dusk.Grain w) :
    setWidths (decodePacket n b p x) =
      (tally n, tally b, (tally p, tally (3*b)), List.ofFn (fun j => Dusk.mark (x j))) := by
  have hb : tally b ++ tally b ++ tally b = tally (3*b) := by
    rw [← recover_tally (tally b ++ tally b ++ tally b)]
    congr 1
    simp
    omega
  simp only [decodePacket, setWidths, hb]

theorem decodePacketSize {m w : ℕ} (n b p : ℕ) (x : Fin m → Dusk.Grain w) :
    size (decodePacket n b p x) = 2*n + 2*b + 2*p + m*(4*(w+1)+4) + 7 := by
  have hs := markedListSize (List.ofFn x)
  rw [List.map_ofFn, List.length_ofFn] at hs
  simp only [Function.comp_def] at hs
  simp only [decodePacket, size_prod, size_tally, tally_length]
  rw [hs]
  omega

/-- The words passed to the carry program, each in exactly three radix blocks. -/
def coefficientWords {m w : ℕ} (b p : ℕ) (x : Fin m → Dusk.Grain w) (j : Fin m) : Word :=
  readCoefficientWord (Dusk.mark (x j), tally p, tally (3*b))

@[simp] theorem coefficientWords_length {m w : ℕ} (b p : ℕ) (x : Fin m → Dusk.Grain w)
    (j : Fin m) : (coefficientWords b p x j).length = 3*b := sized_length _ _

/-- One command performs the coefficient scan and leaves the input and radix
widths beside its output. Every ruler and every grid record is read from the
input packet. -/
theorem decodeToCarryInput {I : Type} (m w n b p : I → ℕ)
    (x : (i : I) → Fin (m i) → Dusk.Grain (w i)) :
    Task (fun i => n i + (m i + 1) * (w i + p i + b i + 1))
      (fun i => send (decodePacket (n i) (b i) (p i) (x i)))
      (fun i => send (tally (n i), tally (b i), List.ofFn (coefficientWords (b i) (p i) (x i)))) := by
  let pkt i := decodePacket (n i) (b i) (p i) (x i)
  have prep := setWidths_easy.on pkt
  have read := readCoefficientList m w p (fun i => 3*b i) x
  have read' := (read.right (fun i => send (tally (b i)))).right (fun i => send (tally (n i)))
  have run := prep.compose (e := read'.conform (fun _ => rfl)
    (fun i => by rw [show pkt i = decodePacket (n i) (b i) (p i) (x i) from rfl, setWidths_decodePacket]; rfl)
    (fun _ => rfl))
  apply run.bound 20
  intro i
  change size (decodePacket (n i) (b i) (p i) (x i)) +
    (size (tally (n i)) + (size (tally (b i)) +
      (m i + 1)*(w i + p i + 3*b i + 1))) + 1 ≤ _
  rw [decodePacketSize, size_tally, size_tally, tally_length, tally_length]
  nlinarith


theorem decodeBudget {m w n b p N k D : ℕ} (hm : m ≤ N) (hb : b ≤ 2*k)
    (hn : n ≤ N*k) (hword : w+p ≤ D*k) (hN : 1 ≤ N) (hk : 1 ≤ k) :
    n + (m+1) * (w+p+b+1) + 1 ≤ (2*D+8) * (N*k + 1) := by
  have h₁ : m+1 ≤ 2*N := by omega
  have h₂ : w+p+b+1 ≤ (D+3)*k := by rw [Nat.add_mul]; omega
  have h := Nat.mul_le_mul h₁ h₂
  calc
    n + (m+1) * (w+p+b+1) + 1 ≤ N*k + 2*N*((D+3)*k) + 1 := by omega
    _ ≤ (2*D+8) * (N*k + 1) := by nlinarith


/-- Compose rounding, narrowing, carry propagation, reversal and exact-width
output padding into one stack task. No numerical correctness hypothesis is
needed to bound the cost of this code. -/
theorem decodeAndFinish {I : Type} (m w n b p N k : I → ℕ) (D : ℕ)
    (x : (i : I) → Fin (m i) → Dusk.Grain (w i)) (hm : ∀ i, m i ≤ N i)
    (hb : ∀ i, b i ≤ 2*k i) (hn : ∀ i, n i ≤ N i*k i)
    (hword : ∀ i, w i+p i ≤ D*k i) (hN : ∀ i, 1 ≤ N i) (hk : ∀ i, 1 ≤ k i) :
    Task (fun i => N i*k i)
      (fun i => send (decodePacket (n i) (b i) (p i) (x i)))
      (fun i => send (finishCarry (carryPacket (n i) (b i)
        (coefficientWords (b i) (p i) (x i))))) := by
  let words i := coefficientWords (b i) (p i) (x i)
  have decode := (decodeToCarryInput m w n b p x).bound (b' := fun i => N i*k i)
    (2*D+8) fun i => decodeBudget (hm i) (hb i) (hn i) (hword i) (hN i) (hk i)
  have finish := finishCarry_compact n b m N k words
    (fun i j => (coefficientWords_length (b i) (p i) (x i) j).le) hm hb hn hN hk
  exact (decode.compose finish).bound 2 (fun i => by omega)

/-- Accuracy of the final numerical grid implies correctness of the rounded,
carried and padded word. -/
theorem finishGrid_product {n b h m w p : ℕ} (a c : Word) (x : Fin m → Dusk.Grain w)
    (ha : a.length = n) (hc : c.length = n) (hcap : n ≤ b*h) (hslots : 2*h ≤ m)
    (hh : 0 < h) (hd : h ≤ 2^b)
    (herr : ∀ j, ‖Grid.meaning p w (x j) -
      (ordinaryCoefficient (unpackDigits b m a) (unpackDigits b m c) j : ℂ)‖ < 1/2) :
    let z := finishCarry (carryPacket n b (coefficientWords b p x))
    z.length = 2*n ∧ bitValue z = bitValue a * bitValue c := by
  apply finishCarry_product a c ha hc hcap hslots (coefficientWords b p x)
  · exact fun j => (coefficientWords_length b p x j).le
  · intro j
    exact (readCoefficientWord_of_norm (x j) _
      (unpackedCoefficient_lt a c ha hc hcap hslots hh hd j) (herr j)).2

/-- A single fixed deterministic tape machine, reading the marked transformed
coefficients in natural order, recovers the exact plain most-significant-first
product. The bound covers the serialized packet, the final write and visited
cells on every tape. -/
theorem gridToProduct {I : Type} (m w n b p N k h : I → ℕ) (D : ℕ)
    (a c : I → Word) (x : (i : I) → Fin (m i) → Dusk.Grain (w i))
    (hm : ∀ i, m i ≤ N i) (hb : ∀ i, b i ≤ 2*k i) (hn : ∀ i, n i ≤ N i*k i)
    (hword : ∀ i, w i+p i ≤ D*k i) (hN : ∀ i, 1 ≤ N i) (hk : ∀ i, 1 ≤ k i)
    (ha : ∀ i, (a i).length = n i) (hc : ∀ i, (c i).length = n i)
    (hcap : ∀ i, n i ≤ b i*h i) (hslots : ∀ i, 2*h i ≤ m i)
    (hh : ∀ i, 0 < h i) (hd : ∀ i, h i ≤ 2^(b i))
    (herr : ∀ i j, ‖Grid.meaning (p i) (w i) (x i j) -
      (ordinaryCoefficient (unpackDigits (b i) (m i) (a i))
        (unpackDigits (b i) (m i) (c i)) j : ℂ)‖ < 1/2) :
    ∃ z : I → Word, (∀ i, (z i).length = 2*n i ∧ bitValue (z i) = bitValue (a i)*bitValue (c i)) ∧
      TreeToPlainBits (fun i => send (decodePacket (n i) (b i) (p i) (x i))) z
        (fun i => N i*k i + 2*n i) := by
  let words i := coefficientWords (b i) (p i) (x i)
  let z i := finishCarry (carryPacket (n i) (b i) (words i))
  have hz i : (z i).length = 2*n i ∧ bitValue (z i) = bitValue (a i)*bitValue (c i) :=
    finishGrid_product (a i) (c i) (x i) (ha i) (hc i) (hcap i) (hslots i) (hh i) (hd i) (herr i)
  refine ⟨z, hz, ?_⟩
  have run := treeToPlainBits_of_task (reply := z) (decodeAndFinish m w n b p N k D x
    hm hb hn hword hN hk)
  simpa only [fun i => (hz i).1] using run

end FixedPoint

end NearSquareRoot
end Computability
end OAI
