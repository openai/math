import OAI.Computability.BorderVNP.ParseBatchVerifierHistogram
import OAI.Computability.BorderVNP.ParseBatchBitCounts
import Mathlib.Data.Fin.Rev

/-!
# Wiring the sparse counter to literal grammar records

The complete bit string is a parameter key. Only canonical grammar-label keys
are weighted, even though the counter accepts every binary word as a possible
key. Sorting lanes consist of the actual records, the end markers and enough
dummy rows to reach a power of two. Count bits are emitted at the fixed
parameter addresses in least-significant-bit order.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace ParseBatchVerifier

open VPVNP ParseRecords ParseBatchCounts ParseBatchSort ParseBatch

/-- Number of bits in a raw fixed-width parse record. -/
abbrev labelWidth (m g n : ℕ) := 2 + 6 * recordWidth m g n

/-- The fixed ordering of the fields used as sort-key bits. -/
noncomputable def labelPins (m g n : ℕ) : Fin (labelWidth m g n) ≃ BitSlot (recordWidth m g n) :=
  (Fintype.equivFinOfCardEq (card_bitSlot _)).symm

/-- The unsigned numerical key of an entire binary record. -/
noncomputable def recordKey {m g n : ℕ} (v : BitSlot (recordWidth m g n) → Bool) :
    Fin (2 ^ labelWidth m g n) :=
  numberWords _ (v ∘ labelPins m g n)

/-- Distinct binary records have distinct complete keys. -/
theorem recordKey_injective (m g n : ℕ) : Function.Injective (@recordKey m g n) := by
  intro v w e
  have h := (numberWords _).injective e
  funext i
  simpa [Function.comp_apply] using congrFun h ((labelPins m g n).symm i)

/-- Flat occurrences retain the tree index and the position within its preorder block. -/
abbrev Use {n : ℕ} (r : ℕ) (d : Fin n) := Fin r × Fin (2*d.val+1)

/-- Width of a marker-position or count word in the padded histogram sort. -/
abbrev histogramWidth {n : ℕ} (m g r : ℕ) (d : Fin n) :=
  Nat.clog 2 (r * (2*d.val+1) + 2 ^ labelWidth m g n)

/-- The padded sorting array contains every use row and exactly one marker per
possible binary key; every remaining row is an explicitly prescribed dummy. -/
noncomputable def histogramLayout {n : ℕ} (m g r : ℕ) (d : Fin n) :
    Fin (2 ^ histogramWidth m g r d) ≃
      Rows (Use r d) (2 ^ labelWidth m g n)
        (Fin (2 ^ histogramWidth m g r d - (r*(2*d.val+1) + 2^labelWidth m g n))) := by
  apply (Fintype.equivFinOfCardEq _).symm
  have h := Nat.le_pow_clog (by decide : 1 < 2) (r*(2*d.val+1) + 2 ^ labelWidth m g n)
  simp only [Rows, Use, Fintype.card_sum, Fintype.card_prod, Fintype.card_fin, histogramWidth]
  omega

/-- All occurrence bits in their sorting positions. -/
noncomputable def occurrenceBits {m g n r : ℕ} {d : Fin n} (bs : Guess m g n r d) :
    Use r d × Fin (labelWidth m g n) → Bool :=
  fun p => bs p.1.1 p.1.2 (labelPins m g n p.2)

private theorem count_ofFn {α : Type*} [DecidableEq α] {k : ℕ} (v : Fin k → α) (a : α) :
    (List.ofFn v).count a = ∑ i, if v i = a then 1 else 0 := by
  induction k with
  | zero => simp
  | succ k ih =>
    simp only [List.ofFn_succ, List.count_cons, Fin.sum_univ_succ, ih, beq_iff_eq]
    omega

/-- The marker keyed by a grammar label reads exactly its total number of uses,
including all repetitions in the same tree or in different batch queries. -/
theorem label_uses {m g n r : ℕ} (d : Fin n) (bs : Guess m g n r d)
    (t : GrammarLabel (Fin m × Bool) (Fin g) n) :
    useCount (useLabel (occurrenceBits bs)) (recordKey (packBits t)) = uses d bs t := by
  classical
  simp only [useCount, Finset.card_filter, Use, Fintype.sum_prod_type, uses, count_ofFn]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  change (if recordKey (bs i j) = recordKey (packBits t) then 1 else 0) = _
  simp only [(recordKey_injective m g n).eq_iff]

/-- Position `j` in little-endian order reads position `rev j` of a big-endian word. -/
theorem value_testBit {b : ℕ} (v : Fin b → Bool) (j : Fin b) :
    (value v).testBit j.val = v j.rev := by
  induction b with
  | zero => exact j.elim0
  | succ b ih =>
    have hv := value_lt (fun i : Fin b => v i.succ)
    simp only [value, Nat.mul_comm (v 0).toNat, Nat.testBit_two_pow_mul_add _ hv]
    refine Fin.lastCases ?_ (fun i => ?_) j
    · cases hx : v 0 <;> simp [hx]
    · simp only [Fin.val_castSucc, Fin.is_lt, ite_true, Fin.rev_castSucc]
      exact ih _ i

/-- Every bit of an occurrence multiplicity fits into the histogram word. -/
theorem countWidth_le {n : ℕ} (m g r : ℕ) (d : Fin n) :
    Nat.clog 2 (r*(2*d.val+1)+1) ≤ histogramWidth m g r d :=
  Nat.clog_mono_right 2 (Nat.add_le_add_left Nat.one_le_two_pow _)

/-- The guessed count wire carrying the factor `X_t ^ (2^j)`. -/
noncomputable def weightPin {m g n r : ℕ} (d : Fin n)
    (t : GrammarLabel (Fin m × Bool) (Fin g) n) (j : Fin (Nat.clog 2 (r*(2*d.val+1)+1))) :
    ArithmeticPin (2 ^ labelWidth m g n) (histogramWidth m g r d) :=
  (recordKey (packBits t), true, (j.castLE (countWidth_le m g r d)).rev)

/-- A canonical histogram guess fixes the bit of every unary parameter weight. -/
theorem canonical_weightPin {m g n r : ℕ} (d : Fin n) (bs : Guess m g n r d)
    (t : GrammarLabel (Fin m × Bool) (Fin g) n) (j : Fin (Nat.clog 2 (r*(2*d.val+1)+1))) :
    canonicalGuess (histogramLayout m g r d) (occurrenceBits bs) (weightPin d t j) =
      (uses d bs t).testBit j.val := by
  let g' := canonicalGuess (histogramLayout m g r d) (occurrenceBits bs)
  let k := recordKey (packBits t)
  have h : pinValue g' k true = uses d bs t := by
    rw [canonicalGuess_value, ite_eq_left rfl, label_uses]
  exact (value_testBit (fun i => g' (k,true,i)) (j.castLE (countWidth_le m g r d))).symm.trans
    (congrArg (fun q : ℕ => q.testBit j.val) h)

end ParseBatchVerifier

end BorderVNP
end Computability
end OAI
