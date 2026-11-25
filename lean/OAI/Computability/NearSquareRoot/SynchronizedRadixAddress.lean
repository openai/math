import OAI.Computability.NearSquareRoot.SynchronizedRadixLayers

/-! # Physical binary addresses of the normalized radix program

The stage index counts address bits from the most significant end.
The twiddle numerator is either zero or the low suffix of the rank.
The two inputs to an aligned butterfly have ranks differing by one XOR mask.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace ShortFourier

open IntegerMultiplication Axon Net.Walsh SynchronizedPair

variable {k : ℕ}

/-- Executable most-significant-first unpacking of a position in a radix work array. -/
def rankBits (r : Fin (2 ^ k)) (i : Fin k) : B :=
  if r.val.testBit i.rev.val then 1 else 0

private theorem testBit_bold (x : Face k) (i : Fin k) :
    (bold x).testBit i.rev.val = decide (x i = 1) := by
  induction k with
  | zero => exact Fin.elim0 i
  | succ k ih =>
    refine Fin.cases ?_ (fun j ↦ ?_) i
    · rw [born, Fin.rev_zero, Fin.val_last, Nat.testBit_two_pow_mul_add _ (vellum _) _]
      rcases bit_value (crest x) with he | he <;> change _ = decide (crest x = 1) <;>
        simp [he, pin]
      decide
    · rw [born, Fin.rev_succ, Fin.val_castSucc, Nat.testBit_two_pow_mul_add _ (vellum _) _,
        ite_eq_left j.rev.isLt]
      exact ih (stem x) j

theorem rankBits_localV (x : Face k) : rankBits (localV x) = x := by
  funext i
  change (if (bold x).testBit i.rev.val then _ else _) = _
  rw [testBit_bold]
  rcases bit_value (x i) with h | h <;> simp [h]

theorem rankBits_eq (r : Fin (2 ^ k)) : rankBits r = (localE k).symm r := by
  obtain ⟨x, rfl⟩ := (localE k).surjective r
  rw [Equiv.symm_apply_apply]
  exact rankBits_localV x

@[simp] theorem localV_rankBits (r : Fin (2 ^ k)) : localV (rankBits r) = r := by
  change localE k (rankBits r) = r
  rw [rankBits_eq, Equiv.apply_symm_apply]

/-- Pack the input address in reverse bit order, retaining all width-`k` zeros. -/
def reverseRank (r : Fin (2 ^ k)) : Fin (2 ^ k) := localV (refl_ (rankBits r))

theorem reverseRank_eq (r : Fin (2 ^ k)) : reverseRank r = reversalPerm k r := by
  unfold reverseRank
  rw [rankBits_eq]
  rfl

/-- Cyclic phase numerator at this specific physical address. -/
def twiddleNumerator (i : Fin k) (r : Fin (2 ^ k)) : ℕ :=
  if r.val.testBit i.rev.val then r.val % 2 ^ i.rev.val else 0

theorem frequency_rank (i : Fin k) (r : Fin (2 ^ k)) :
    frequency 1 i ((localE k).symm r) =
      Fourier.phase (2 ^ (k - i.val)) (twiddleNumerator i r : ℤ) := by
  rw [← rankBits_eq]
  have he : bold (rankBits r) = r.val := congrArg Fin.val (localV_rankBits r)
  have hi : k - (i.val + 1) = i.rev.val := by simp [Fin.rev]
  simp only [frequency, R, beyond, he, hi, twiddleNumerator, rankBits]
  split <;> simp only [show pin (1 : B) = 1 from rfl, show pin (0 : B) = 0 from rfl,
    Nat.cast_one, Nat.cast_zero, one_mul, zero_mul]

theorem twiddleNumerator_lt (i : Fin k) (r : Fin (2 ^ k)) :
    twiddleNumerator i r < 2 ^ i.rev.val := by
  unfold twiddleNumerator
  split
  · exact Nat.mod_lt _ (Nat.two_pow_pos _)
  · exact Nat.two_pow_pos _

/-- Toggle the distinguished bit of a physical address. -/
def partnerRank (i : Fin k) (r : Fin (2 ^ k)) : Fin (2 ^ k) :=
  ⟨r.val ^^^ 2 ^ i.rev.val,
    Nat.xor_lt_two_pow r.isLt (Nat.pow_lt_pow_right (by decide) i.rev.isLt)⟩

theorem rankBits_partner (i : Fin k) (r : Fin (2 ^ k)) (j : Fin k) :
    rankBits (partnerRank i r) j =
      if j = i then 1 - rankBits r j else rankBits r j := by
  simp only [rankBits, partnerRank, Nat.testBit_xor, Nat.testBit_two_pow]
  by_cases h : i = j
  · subst j
    cases r.val.testBit i.rev.val <;> simp
  · have hn : i.rev.val ≠ j.rev.val := fun he ↦ h (Fin.rev_injective (Fin.ext he))
    simp only [decide_eq_false hn, Bool.xor_false, ite_eq_right (Ne.symm h)]

theorem splitBit_partner (i : Fin k) (r : Fin (2 ^ k)) :
    Radix.splitBit i ((localE k).symm (partnerRank i r)) =
      (1 - (rankBits r i : B), (Radix.splitBit i (rankBits r)).2) := by
  rw [← rankBits_eq]
  apply Prod.ext
  · change rankBits (partnerRank i r) i = 1 - rankBits r i
    simp [rankBits_partner]
  · funext j
    change rankBits (partnerRank i r) j.val = rankBits r j.val
    simp [rankBits_partner, j.property]

/-- Copy a supplied bit into one position of the physical rank. -/
def withBit (i : Fin k) (r : Fin (2 ^ k)) (b : B) : Fin (2 ^ k) :=
  if rankBits r i = b then r else partnerRank i r

theorem rankBits_withBit (i : Fin k) (r : Fin (2 ^ k)) (b : B) (j : Fin k) :
    rankBits (withBit i r b) j = if j = i then b else rankBits r j := by
  by_cases hi : j = i
  · subst j
    simp only [↓reduceIte]
    by_cases he : rankBits r i = b
    · simp [withBit, he]
    rw [withBit, ite_eq_right he, rankBits_partner, ite_eq_left rfl]
    rcases bit_value (rankBits r i) with hx | hx <;> rcases bit_value b with hb | hb <;> simp_all
  · by_cases he : rankBits r i = b <;> simp [withBit, he, rankBits_partner, hi]

theorem splitBit_withBit (i : Fin k) (r : Fin (2 ^ k)) (b : B) :
    Radix.splitBit i ((localE k).symm (withBit i r b)) =
      (b, (Radix.splitBit i (rankBits r)).2) := by
  rw [← rankBits_eq]
  apply Prod.ext
  · change rankBits (withBit i r b) i = b
    simp [rankBits_withBit]
  · funext j
    change rankBits (withBit i r b) j.val = rankBits r j.val
    simp [rankBits_withBit, j.property]

/-- Exchange the outer half selector with the physical rank's stage bit.
This is its own inverse and uses one bit test and at most one XOR. -/
def swapHalf (i : Fin k) : Equiv.Perm (B × Fin (2 ^ k)) :=
  Function.Involutive.toPerm (fun x ↦ (rankBits x.2 i, withBit i x.2 x.1)) (by
    intro x
    apply Prod.ext
    · exact (rankBits_withBit i x.2 x.1 i).trans (ite_eq_left rfl)
    · apply ((Function.LeftInverse.injective (fun r ↦ localV_rankBits (k := k) r)) :
        Function.Injective (rankBits (k := k)))
      funext j
      change rankBits (withBit i (withBit i x.2 x.1) (rankBits x.2 i)) j = rankBits x.2 j
      by_cases h : j = i <;> simp [rankBits_withBit, h])

@[simp] theorem swapHalf_apply (i : Fin k) (b : B) (r : Fin (2 ^ k)) :
    swapHalf i (b, r) = (rankBits r i, withBit i r b) := rfl

/-- A reversal-table entry at two physical ranks can be tested directly. -/
theorem radixReverseMatrix_apply (r t : Fin (2 ^ k)) :
    radixReverseMatrix k r t = (if reverseRank r = t then 1 else 0) := by
  simp [radixReverseMatrix, PEquiv.toMatrix_apply, reverseRank_eq]

/-- The two ranks in a butterfly fiber are the current rank and its XOR partner. -/
theorem sameSpectators_iff (i : Fin k) (r t : Fin (2 ^ k)) :
    (∀ j, j ≠ i → rankBits r j = rankBits t j) ↔ r = t ∨ partnerRank i r = t := by
  constructor
  · intro h
    have he : withBit i r (rankBits t i) = t := by
      apply ((Function.LeftInverse.injective (fun u ↦ localV_rankBits (k := k) u)) :
        Function.Injective (rankBits (k := k)))
      funext j
      rw [rankBits_withBit]
      by_cases hj : j = i
      · simp [hj]
      · simp [hj, h j hj]
    by_cases hbit : rankBits r i = rankBits t i
    · exact Or.inl (by simpa [withBit, hbit] using he)
    · exact Or.inr (by simpa [withBit, hbit] using he)
  · rintro (rfl | rfl) j hj
    · rfl
    · simp [rankBits_partner, hj]

/-- On the physical tape array a butterfly picks its second operand by a
single-bit XOR. Its signs are exactly the two-by-two normalized Walsh signs. -/
theorem radixGateMatrix_butterfly_apply (i : Fin k) (r t : Fin (2 ^ k)) :
    radixGateMatrix k (.butterfly i) r t =
      if r = t ∨ partnerRank i r = t then walsh (rankBits r i) (rankBits t i) else 0 := by
  change (((w : ℂ) • headH i) ((localE k).symm r) ((localE k).symm t)) = _
  rw [Radix.normalized_butterfly, Matrix.submatrix_apply, Matrix.blockDiagonal_apply,
    ← rankBits_eq, ← rankBits_eq]
  change (if (Radix.splitBit i (rankBits r)).2 = (Radix.splitBit i (rankBits t)).2 then
    walsh (rankBits r i) (rankBits t i) else 0) = _
  congr 1
  apply propext
  rw [← sameSpectators_iff]
  exact ⟨fun h j hj ↦ congrFun h ⟨j, hj⟩, fun h ↦ funext (fun j ↦ h j j.property)⟩

/-- Actual twiddle gate as a phase table queried by the physical rank. -/
theorem radixGateMatrix_twiddle (i : Fin k) :
    radixGateMatrix k (.twiddle i) = Matrix.diagonal (fun r ↦
      Fourier.phase (2 ^ (k - i.val)) (twiddleNumerator i r : ℤ)) := by
  ext x y
  change Matrix.diagonal (frequency 1 i) ((localE k).symm x) ((localE k).symm y) = _
  simp [Matrix.diagonal_apply, frequency_rank]

end ShortFourier

end NearSquareRoot
end Computability
end OAI
