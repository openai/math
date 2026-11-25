import OAI.Computability.NearSquareRoot.SynchronizedPlacedPermutation
import OAI.Computability.NearSquareRoot.SynchronizedFixedSemantics
import OAI.Computability.NearSquareRoot.SynchronizedHalfAddressTape

/-! # Numerical source queries for the two routed permutation opcodes -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace ShortFourier.AxisWord

open Matrix IntegerMultiplication Code Bits RadixAddressTape
variable {k a b c : ℕ}

/-- Action of the permutation opcodes on the flat index of the two Fourier
halves. The adjoint has the same query because both operations are involutions. -/
def permutationTarget (k tag arg t : ℕ) : ℕ :=
  if tag = 0 then
    if t < 2^k then value (phrase k t).reverse else t
  else if tag = 18 ∧ arg < k then
    let z := halfReply (decide (2^k ≤ t), tally arg, (phrase k (t % 2^k)).reverse)
    (if z.1 then 2^k else 0) + value z.2.reverse
  else t

@[simp] theorem reverseLeft_inv (k : ℕ) : (reverseLeft k).symm = reverseLeft k := by
  ext x
  cases x <;> rfl

@[simp] theorem routeAt_inv (k arg : ℕ) : (routeAt k arg).symm = routeAt k arg := by
  unfold routeAt
  split <;> simp

private theorem word_reverseRank (x : Fin (2^k)) :
    value (phrase k x.val).reverse = (reversalPerm k x).val := by
  rw [← address_eq_phrase]
  have h := address_value (reverseRank x)
  rw [← address_reverse, List.reverse_reverse, reverseRank_eq] at h
  exact h

theorem permutationTarget_reverse (arg : ℕ) (x : Ambient k) :
    permutationTarget k 0 arg (finSumFinEquiv x).val = (finSumFinEquiv (reverseLeft k x)).val := by
  cases x with
  | inl x => simp [permutationTarget, x.isLt, reverseLeft, word_reverseRank]
  | inr x => simp [permutationTarget, reverseLeft]

private theorem halfRank (x : Ambient k) :
    (finSumFinEquiv x).val =
      (if (dilationAddress x).1 = 1 then 2^k else 0) + (dilationAddress x).2.val := by
  cases x <;> simp [dilationAddress, Nat.add_comm]

private theorem queryBit (x : Ambient k) :
    decide (2^k ≤ (finSumFinEquiv x).val) = decide ((dilationAddress x).1 = 1) := by
  cases x with
  | inl x => simp [dilationAddress, Nat.not_le_of_gt x.isLt]
  | inr x => simp [dilationAddress]

private theorem queryBits (x : Ambient k) :
    (phrase k ((finSumFinEquiv x).val % 2^k)).reverse = address (dilationAddress x).2 := by
  cases x <;> rename_i x <;>
    simp [dilationAddress, address_eq_phrase, Nat.mod_eq_of_lt x.isLt]

theorem permutationTarget_route (arg : ℕ) (x : Ambient k) :
    permutationTarget k 18 arg (finSumFinEquiv x).val = (finSumFinEquiv (routeAt k arg x)).val := by
  by_cases h : arg < k
  · let i : Fin k := ⟨arg,h⟩
    simp only [permutationTarget, show (18 : ℕ) ≠ 0 by decide, ↓reduceIte, h, and_self, routeAt, dite_eq_left]
    rw [queryBit, queryBits, halfRank, internalRoute_address]
    generalize dilationAddress x = d
    rcases d with ⟨bit, idx⟩
    have desc := halfReply_rank i bit idx
    change halfReply (_, tally arg, address idx) = _ at desc
    erw [desc]
    simp [address_value, i]
    rfl
  · simp [permutationTarget, routeAt, h]

/-- A typed permutation decoded from a valid permutation tag, independent of
its direction flag. The default covers unused tags in numerical queries. -/
noncomputable def opcodePermutation (k tag arg : ℕ) : Equiv.Perm (Ambient k) :=
  if tag = 0 then reverseLeft k else if tag = 18 then routeAt k arg else Equiv.refl _

theorem opcodePermutation_rank (tag arg : ℕ) (x : Ambient k) :
    permutationTarget k tag arg (finSumFinEquiv x).val =
      (finSumFinEquiv (opcodePermutation k tag arg x)).val := by
  by_cases h : tag = 0
  · subst tag
    simpa [opcodePermutation] using permutationTarget_reverse arg x
  by_cases h' : tag = 18
  · subst tag
    simpa [opcodePermutation] using permutationTarget_route arg x
  simp [opcodePermutation, permutationTarget, h, h']

theorem fixedSlot_permutation (a k : ℕ) [NeZero a] (x : Inst)
    (ht : x.1.length = 0 ∨ x.1.length = 18) :
    fixedSlot a k x = Slot.permutation (opcodePermutation k x.1.length x.2.1.length) := by
  rcases x with ⟨tag,arg,dir⟩
  change tag.length = 0 ∨ tag.length = 18 at ht
  rcases ht with h | h
  · cases dir <;> simp only [fixedSlot, fixedBase, opcodePermutation, h, ↓reduceIte]
    · rfl
    · change Slot.permutation (reverseLeft k).symm = _
      rw [reverseLeft_inv]
  · cases dir <;> simp only [fixedSlot, fixedBase, opcodePermutation, h, ↓reduceIte]
    · rfl
    · change Slot.permutation (routeAt k arg.length).symm = _
      rw [routeAt_inv]
      rfl

theorem placedOpcode_matrix [NeZero a] (har : a ≤ 2^k) (hr : 2*2^k ≤ 8*a)
    (j : Fin 15) (x : Inst) (ht : x.1.length = 0 ∨ x.1.length = 18) :
    batchMatrix (b := b) (c := c) hr j
        (((fixedSlot a k x).matrix dilationAddress).submatrix (auxiliaryLayout har).symm (auxiliaryLayout har).symm) =
      (placedPermutation hr j (borrowedPermutation har (opcodePermutation k x.1.length x.2.1.length))).toPEquiv.toMatrix := by
  rw [fixedSlot_permutation a k x ht]
  exact placedHalfPermutation_matrix har hr j _

theorem placedOpcode_coordinates (ha : 0 < a) (har : a ≤ 2^k) (hr : 2*2^k ≤ 8*a)
    (j : Fin 15) (tag arg : ℕ) (p : Fin b × (Fin a ⊕ Fin c)) :
    cellCoordinates (placedPermutation hr j (borrowedPermutation har (opcodePermutation k tag arg)) p) =
      placedPermTarget (SynchronizedBorrowing.first b j) (SynchronizedBorrowing.size b j) a (2^k)
        (permutationTarget k tag arg) (cellCoordinates p).1 (cellCoordinates p).2 :=
  placedPermutation_coordinates ha har hr j _ _ (borrowedPermutation_rank har _ _ (opcodePermutation_rank tag arg)) p

end ShortFourier.AxisWord

end NearSquareRoot
end Computability
end OAI
