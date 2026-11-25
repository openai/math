import OAI.Computability.NearSquareRoot.KernelSelectorAlign

/-! # Decoding a flat binary address into the columns of a Fourier template

For `n + 1` slots of width `f`, the address consists of `n + 1` consecutive
runs of `f` bits in slot order. Both round trips preserve every bit, including
leading zeroes.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace KernelSelectorAlign

/-- Decode successive `f`-bit slots into columns of an address. -/
def decode : (n f : ℕ) → List Bool → List (Column n)
  | 0, f, bits => bits.take f
  | n+1, f, bits => (bits.take f).zip (decode n f (bits.drop f))

theorem decode_spec : ∀ (n f : ℕ) (bits : List Bool),
    bits.length = (n+1)*f →
    (decode n f bits).length = f ∧ flatBits n (decode n f bits) = bits
  | 0, f, bits, h => by
    have len : bits.length = f := by simpa using h
    simp [decode, ← len, flatBits, bitStreams]
  | n+1, f, bits, h => by
    have total : bits.length = (n+1)*f + f := by simpa only [Nat.succ_mul] using h
    have headLen : (bits.take f).length = f := by simp [List.length_take]; omega
    have tailLen : (bits.drop f).length = (n+1)*f := by rw [List.length_drop]; omega
    obtain ⟨len, eqn⟩ := decode_spec n f (bits.drop f) tailLen
    have same : (bits.take f).length = (decode n f (bits.drop f)).length := headLen.trans len.symm
    constructor
    · simp [decode, headLen, len]
    · let cols := (bits.take f).zip (decode n f (bits.drop f))
      change cols.map Prod.fst ++ flatBits n (cols.map Prod.snd) = bits
      dsimp only [cols]
      rw [List.map_fst_zip same.le, List.map_snd_zip same.ge, eqn, List.take_append_drop]

theorem decode_length (n f : ℕ) (bits : List Bool) (h : bits.length = (n+1)*f) :
    (decode n f bits).length = f :=
  (decode_spec n f bits h).1

theorem flatBits_decode (n f : ℕ) (bits : List Bool) (h : bits.length = (n+1)*f) :
    flatBits n (decode n f bits) = bits :=
  (decode_spec n f bits h).2

@[simp] theorem decode_flatBits : ∀ (n : ℕ) (xs : List (Column n)),
    decode n xs.length (flatBits n xs) = xs
  | 0, xs => by simp [decode, flatBits, bitStreams]
  | n+1, xs => by
    change (((xs.map Prod.fst) ++ flatBits n (xs.map Prod.snd)).take xs.length).zip
      (decode n xs.length (((xs.map Prod.fst) ++ flatBits n (xs.map Prod.snd)).drop xs.length)) = xs
    have len : (xs.map Prod.fst).length = xs.length := List.length_map _
    rw [← len, List.take_left, List.drop_left, len, ← List.length_map (as := xs) Prod.snd,
      decode_flatBits, List.zip_map']
    simp

end KernelSelectorAlign

end NearSquareRoot
end Computability
end OAI
