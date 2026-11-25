import OAI.Computability.BorderVNP.ParseBatchBitsQuery
import OAI.Computability.BorderVNP.ParseBatchWeights

/-! # Lemma 2.3's weighted contraction over the actual guessed record bits -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace ParseBatch

open MvPolynomial VPVNP VPVNP.ParseGrammar BorderVNP.ParseRecords
open scoped Classical

variable {m g n r : ℕ}

/-- The bit-guess domain for `r` fixed-size blocks, before imposing any range, child,
or leaf constraints. -/
abbrev Guess (m g n r : ℕ) (d : Fin n) :=
  Fin r → Fin (2*d.val+1) → BitSlot (recordWidth m g n) → Bool

/-- All the range, structure, and leaf conditions at once. -/
def Accepted (d : Fin n) (h : Fin g) (x : Fin r → Fin m → Bool) (bs : Guess m g n r d) : Prop :=
  ∀ i, CheckedBits d h (x i) (bs i)

/-- Count uses of one parameter by comparing its canonical record bits with the guessed
record at every slot. Sorting the same keys and counting each run yields this count. -/
noncomputable def uses (d : Fin n) (bs : Guess m g n r d)
    (t : GrammarLabel (Fin m × Bool) (Fin g) n) : ℕ :=
  ∑ i, (List.ofFn (bs i)).count (packBits t)

private theorem count_packed (rs : List (GrammarLabel (Fin m × Bool) (Fin g) n))
    (t : GrammarLabel (Fin m × Bool) (Fin g) n) :
    (rs.map packBits).count (packBits t) = (rs.map (fun z => Finsupp.single z (1 : ℕ))).sum t := by
  induction rs with
  | nil => simp
  | cons a rs ih =>
    simp only [List.map_cons, List.sum_cons, Finsupp.add_apply, Finsupp.single_apply, ih,
      List.count_cons, beq_iff_eq, packBits_injective.eq_iff]
    omega

/-- The count obtained from the raw record bits agrees with the grammar's occurrence
histogram for every tuple of accepted parses. -/
theorem uses_treeBits (d : Fin n) (h : Fin g) (x : Fin r → Fin m → Bool)
    (p : ∀ i, ParseChoice (Fin g) d (x i)) (t : GrammarLabel (Fin m × Bool) (Fin g) n) :
    uses d (fun i => treeBits d h (p i).1) t = counts d h x p t := by
  rw [uses, counts, Finsupp.finsetSum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [ofFn_treeBits, count_packed, encode_histogram]

/-- A guessed batch is weighted by at most one unary polynomial factor for every
parameter and bit position in its total occurrence count. -/
noncomputable def bitWeight (d : Fin n) (bs : Guess m g n r d) :
    MvPolynomial (GrammarLabel (Fin m × Bool) (Fin g) n) ℤ :=
  ∏ t, ∏ j : Fin (Nat.clog 2 (r*(2*d.val+1)+1)),
    if (uses d bs t).testBit j.val then X t ^ (2^j.val) else 1

/-- Contracting all raw record bits, rejecting malformed guesses and applying the unary
count-bit factors, gives exactly the product of the queried coefficients over the integers. -/
theorem product_eq_bit_sum (d : Fin n) (h : Fin g) (x : Fin r → Fin m → Bool) :
    (∏ i, labelQuery d h (x i)) =
      ∑ bs : Guess m g n r d, if Accepted d h x bs then bitWeight d bs else 0 := by
  let e : (∀ i, ParseChoice (Fin g) d (x i)) ≃ {bs // Accepted d h x bs} :=
    (Equiv.piCongrRight fun i => queryBitsEquiv d h (x i)).trans Equiv.subtypePiEquivPi.symm
  rw [product_eq_binary_weights]
  calc
    _ = ∑ p, bitWeight d (e p).val := by
      refine Finset.sum_congr rfl fun p _ => ?_
      change _ = bitWeight d (fun i => treeBits d h (p i).1)
      simp only [bitWeight, uses_treeBits d h x p]
    _ = ∑ bs : {bs // Accepted d h x bs}, bitWeight d bs.val :=
      e.sum_comp (fun bs => bitWeight d bs.val)
    _ = ∑ bs : Guess m g n r d, if Accepted d h x bs then bitWeight d bs else 0 := by
      rw [← Finset.sum_filter, ← Finset.sum_subtype_eq_sum_filter]
      simp

end ParseBatch

end BorderVNP
end Computability
end OAI
