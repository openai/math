import OAI.LinearAlgebra.FiniteFourier.WorkingGroup
import OAI.LinearAlgebra.FiniteFourier.RadixButterfly
import OAI.LinearAlgebra.FiniteFourier.GridFactorWord

/-! # Fourier words on the short coprime factors

Pad each factor of length at most `3 * t ^ 2` to the common radix. The
intermediate FFT uses its own coordinates, and the reduction to geometric
evaluation restores the borrowed registers.
-/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

/-- Uniform number of layers for all short Fourier transforms of the working group. -/
def shortWordDepth (t : ℕ) : ℕ := 24000 * (1 + Nat.clog 2 (1+t))

namespace WorkingGroup

variable {K : Type*} [Field K] {ι : Type*} [Fintype ι] {a : ι → ℕ} {t : ℕ}
  (w : WorkingGroup K a t)

omit [Fintype ι] in
theorem shortExponent_le (i : ι) {d : ℕ} (hd : d ∈ (w.axes i).factors) :
    w.shortExponent d ≤ 5 + 2 * Nat.clog 2 (1+t) := by
  have h₁ := (w.axes i).factor_le d hd
  have h₂ := w.short_upper i d hd
  have hbase := (fourierRadix_prime K).two_le
  let l := Nat.clog 2 (1+t)
  have ht : t ≤ 2 ^ l := (Nat.le_add_left t 1).trans (Nat.le_pow_clog (by decide) _)
  have hs : 2 ^ w.shortExponent d ≤ 2 ^ (5 + 2*l) := by
    calc
      _ ≤ fourierRadix K ^ w.shortExponent d := Nat.pow_le_pow_left hbase _
      _ ≤ 18 * t ^ 2 := by omega
      _ ≤ 32 * (2 ^ l) ^ 2 := Nat.mul_le_mul (by decide) (Nat.pow_le_pow_left ht _)
      _ = _ := by rw [pow_add, Nat.mul_comm 2 l, pow_mul]; norm_num
  exact (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp hs

/-- Every primitive root at a short coprime working length admits the
same depth and workspace bound throughout the group. -/
theorem short_fourier_word (i : ι) {d : ℕ} (hd : d ∈ (w.axes i).factors)
    {z : CyclotomicField w.order K} (hz : IsPrimitiveRoot z d) :
    OccupiedWord (Fin (13*d)) (shortWordDepth t) (geometricMatrix d z) := by
  have hs := w.short_upper i d hd
  have hd₂ := (w.axes i).factor_ge d hd
  have hdpos : 0 < d := by omega
  obtain ⟨ζ, _, _, hζ⟩ := w.exists_roots
  have hroot := hζ i d hd
  have hr : fourierRadix K = 2 ∨ fourierRadix K = 3 := by
    unfold fourierRadix
    split <;> simp
  have hF := layerWord_smallRadixPow hr (w.shortExponent d) hroot
  have hV : GridFactor (geometricMatrix d z) :=
    .geometric z (hz.ne_zero hdpos.ne') (fun i j e => Fin.ext (hz.pow_inj i.isLt j.isLt e))
  have h := gridFactor_word_of_fourier hdpos (w.short_lower i d hd) hroot
    (hF.occupied (W := Fin 0)) hV
  apply LayerWord.pad _ (h.enlargeWorkspace (V := Fin (13*d)) (by
    simp only [Fintype.card_sum, Fintype.card_fin]
    omega))
  have := w.shortExponent_le i hd
  unfold shortWordDepth
  omega

end WorkingGroup

end FiniteFourier
end LinearAlgebra
end OAI
