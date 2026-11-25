import OAI.Computability.BorderVNP.ParseBatchVerifierTrees
import OAI.Computability.BorderVNP.ParseBatchVerifierNetwork

/-! # Lemma 2.3 of the border-circuit paper -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace ParseBatchVerifier

open VPVNP VPVNP.ParseGrammar VPVNP.VerifierNetwork
open ParseBatch ParseBatchTrees
open scoped Classical

/-- Lemma 2.3. One shared degree-three bit network over the integer parameter
polynomial ring computes a batch of coefficient queries. Its only weighted
sites are the fixed `WeightSites`, one per grammar parameter and count bit.
The bound counts vertices, edges, and even the external ports. -/
theorem batched_queries {m g s r : ℕ} (d : Fin m) (h : Fin g) (hm : m = d.val+1)
    (hg : g ≤ 2*m+s+1) (hr : (m+s+2)^24 ≤ r) :
    ∃ trees : Frame (BatchPins m g m r d) Unit,
      (∀ x : Fin r → Fin m → Bool, let L := queryLayout d trees
        L.network.value (L.tables (BooleanLayout.factor (verifier d trees) unaryWeight))
          (fun ij _ => x ij.1 ij.2) = ∏ i, labelQuery d h (x i)) ∧
      (let L := queryLayout d trees
       Fintype.card L.Site + Fintype.card L.Edge + Fintype.card (Fin r × Fin m) ≤
         180000000 * (m*r) * (Nat.clog 2 (2*m*r)+3)^3) ∧
      (∀ v : (queryLayout d trees).Site,
        (Finset.univ.filter (fun e : (queryLayout d trees).Endpoint =>
          (queryLayout d trees).incident e = v)).card ≤ 3) := by
  have hb := histogramBudget_of_replication d hg hr
  have hpos : 0 < r := (Nat.pow_pos (by omega : 0 < m+s+2)).trans_le hr
  obtain ⟨trees, ht, he⟩ := exists_acceptFrame d h hm hpos hb.fieldRange
  refine ⟨trees, queryLayout_value d h trees he, queryLayout_volume d trees hb hpos ht, ?_⟩
  exact BooleanLayout.degree_bound (verifier d trees) (weightedPin (d := d))

/-- In the universal table for size `s`, the tensor entry at a bit address is
precisely the coefficient of the monomial selecting one variable from each pair. -/
theorem universal_table_query (k s : ℕ) (x : Fin (k+1) → Bool) :
    ParseTable.table (Fin (k+1) × Bool) k s
      ⟨pairedExponent x, by simp [pairedExponent, Finsupp.degree_single]⟩ =
        labelQuery (Fin.last k) (0 : ParseTable.State (Fin (k+1) × Bool) s) x := rfl

end ParseBatchVerifier

end BorderVNP
end Computability
end OAI
