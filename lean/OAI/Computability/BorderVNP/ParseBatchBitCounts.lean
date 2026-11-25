import OAI.Computability.BorderVNP.ParseBatchBitSum
import OAI.Computability.BorderVNP.ParseBatchVerifierCountRanks

/-! # Identifying the sorted-key counts with the raw bit contraction -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace ParseBatch

open VPVNP BorderVNP.ParseRecords BorderVNP.ParseBatchCounts
open scoped Classical

variable {m g n r k : ℕ}

private theorem count_ofFn_sum {A : Type*} [DecidableEq A] {N : ℕ} (v : Fin N → A) (a : A) :
    (List.ofFn v).count a = ∑ i, if v i = a then 1 else 0 := by
  induction N with
  | zero => simp
  | succ N ih =>
    simp only [List.ofFn_succ, List.count_cons, Fin.sum_univ_succ, ih, beq_iff_eq]
    omega

/-- Flattening all the block and slot addresses gives precisely the multiplicity used
by the end-marker count. The sort key may use any injective numbering of the table labels. -/
theorem uses_eq_useCount (d : Fin n) (bs : Guess m g n r d)
    (records : Fin r × Fin (2*d.val+1) → GrammarLabel (Fin m × Bool) (Fin g) n)
    (hbits : ∀ i j, bs i j = packBits (records (i,j)))
    (key : GrammarLabel (Fin m × Bool) (Fin g) n ↪ Fin k)
    (t : GrammarLabel (Fin m × Bool) (Fin g) n) :
    uses d bs t = useCount (key ∘ records) (key t) := by
  simp only [uses, useCount, Finset.card_filter, Fintype.sum_prod_type, count_ofFn_sum,
    hbits, packBits_injective.eq_iff, Function.comp_apply, key.injective.eq_iff]

end ParseBatch

end BorderVNP
end Computability
end OAI
