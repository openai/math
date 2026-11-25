import OAI.Computability.IntegerMultiplication.Axon.Factor
import OAI.Computability.NearSquareRoot.SynchronizedCirculant
import OAI.Computability.NearSquareRoot.SynchronizedMatching

/-! # Normalized radix-two stage word

Each dyadic Fourier transform in the chirp dilation uses the radix-two
identity from the fixed-tape multiplier. Normalization is absorbed in the
individual Walsh butterflies. The only change of output layout is bit
reversal.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace ShortFourier.Radix

open IntegerMultiplication IntegerMultiplication.Axon IntegerMultiplication.Net
open IntegerMultiplication.Net.Walsh SynchronizedPair Matrix

noncomputable section

variable {k : ℕ}

/-- Expose a distinguished bit and collect the spectator address bits. -/
abbrev splitBit (i : Fin k) : Face k ≃ Fin 2 × ({j : Fin k // j ≠ i} → Fin 2) :=
  Equiv.funSplitAt i (Fin 2)

private theorem walsh_entry (a b : Walsh.B) :
    (w : ℂ) * (Walsh.F a b : ℂ) = walsh a b := by
  rcases bit_value a with rfl | rfl <;> rcases bit_value b with rfl | rfl <;>
    norm_num [Walsh.F, walsh, Matrix.of_apply] <;> rfl

/-- The bit operation in P192, after normalization, is a whole matching of
Walsh pairs routed to one designated bit. -/
theorem normalized_butterfly (i : Fin k) :
    (w : ℂ) • headH i =
      (blockDiagonal (fun _ : {j : Fin k // j ≠ i} → Fin 2 => walsh)).submatrix
        (splitBit i) (splitBit i) := by
  ext x y
  rw [submatrix_apply, blockDiagonal_apply]
  change (w : ℂ) * (if E i x y then Walsh.F (x i) (y i) else 0) =
    if ((splitBit i x).2 = (splitBit i y).2) then walsh (x i) (y i) else 0
  have he : E i x y = true ↔ (splitBit i x).2 = (splitBit i y).2 := by
    simp only [E, decide_eq_true_eq]
    exact ⟨fun h => funext fun j => h j.val j.property,
      fun h j hj => congrFun h ⟨j, hj⟩⟩
  by_cases h : E i x y = true
  · simp only [ite_eq_left h, ite_eq_left (he.mp h)]
    exact walsh_entry _ _
  · simp only [ite_eq_right h, ite_eq_right (mt he.mpr h), mul_zero]

inductive Gate (k : ℕ) where
  | twiddle (i : Fin k)
  | butterfly (i : Fin k)

/-- Twiddle values are exactly unit phases for arbitrary frequency factor q. -/
theorem frequency_unit (q : ℤ) (i : Fin k) (x : Face k) : ‖frequency q i x‖ = 1 :=
  Fourier.phase_norm ..

def eval (q : ℤ) : Gate k → Mb k
  | .twiddle i => diagonal (frequency q i)
  | .butterfly i => (w : ℂ) • headH i

/-- The word is in matrix-product order. -/
def word : List (Fin k) → List (Gate k)
  | [] => []
  | i :: is => word is ++ [.twiddle i, .butterfly i]

theorem word_length (l : List (Fin k)) : (word l).length = 2 * l.length := by
  induction l with
  | nil => rfl
  | cons i l ih => simp [word, ih, Nat.mul_succ]

theorem word_semantics (q : ℤ) (l : List (Fin k)) :
    ((word l).map (eval q)).prod = ((w : ℂ) ^ l.length) • play q l := by
  induction l with
  | nil => simp [word, play]
  | cons i l ih =>
    simp only [word, List.map_append, List.prod_append, List.map_cons, List.map_nil,
      List.prod_cons, List.prod_nil, mul_one, ih, eval, List.length_cons, pow_succ]
    simp only [play, List.foldr_cons, layer, Matrix.mul_smul, Matrix.smul_mul, smul_smul]
    rw [mul_comm (w : ℂ)]

private theorem normalize_pow (k : ℕ) :
    (w : ℂ) ^ k = (Real.sqrt (2 ^ k : ℕ) : ℂ)⁻¹ := by
  have h : Real.sqrt ((2 : ℝ) ^ k) = (Real.sqrt 2) ^ k := by
    induction k with
    | zero => simp
    | succ k ih => rw [pow_succ, pow_succ, Real.sqrt_mul (by positivity), ih]
  push_cast
  rw [h]
  simp [w]

/-- Entries after the radix word and the bit reversal are precisely the
positive-sign normalized dyadic Fourier entries. -/
theorem matrix_entry (x y : Face k) :
    (((word (layers k)).map (eval 1)).prod) (refl_ x) y =
      normalizedFourier (2 ^ k) (localE k x) (localE k y) := by
  rw [word_semantics, persist 1 (by decide)]
  simp only [layers, List.length_ofFn, normalize_pow, Matrix.smul_apply, smul_eq_mul,
    lineF, Matrix.of_apply, shine]
  unfold normalizedFourier Axon.R Fourier.phase Fourier.cis phase
  congr 2
  change _ = (↑((bold x : ℝ) * bold y / ↑(2 ^ k : ℕ)) : ℂ) * (2 * Real.pi * Complex.I)
  push_cast
  ring

/-- The exact axis on finite cyclic residue coordinates, with the bit order
used by the multitape radix code. -/
theorem axis_entry (x y : Face k) :
    (((word (layers k)).map (eval 1)).prod) (refl_ x) y =
      ResidueFourier.axisMatrix (2^k) (ZMod.finEquiv _ (localE k x))
        (ZMod.finEquiv _ (localE k y)) := by
  rw [matrix_entry, normalizedFourier_axisMatrix]
  rfl

end

end ShortFourier.Radix

end NearSquareRoot
end Computability
end OAI
