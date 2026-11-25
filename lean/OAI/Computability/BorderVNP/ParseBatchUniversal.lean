import OAI.Computability.BorderVNP.ParseBatchQueries
import OAI.Computability.BorderVNP.ParseBatchVertexCodes
import OAI.Computability.BorderVNP.ParseBooleanPhysical

/-!
# The canonical simultaneous batch realization of the universal coefficient map

Here the gate-slot count, root slot, positive degree, paired coefficient address
and scalar parameters are those of Lemma 2.2. The unique unary sites and their
bits are the concrete sites and edges in `BooleanLayout.weightSite` and
`BooleanLayout.weightEdge`. All other physical tables have only zero-one entries.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace ParseBatchVerifier

open VPVNP ParseBatchTrees ParseBatch
open scoped Classical

/-- Full degree-`m` paired-monomial coefficient address in the ambient space. -/
noncomputable def pairedAddress {m : ℕ} (x : Fin m → Bool) : DegreeMonomial (Fin m × Bool) m :=
  ⟨pairedExponent x, by simp [pairedExponent, Finsupp.degree_single]⟩

/-- Lemma 2.3 for the actual universal map of Lemma 2.2. One network serves
every external batch of addresses. Even a complete truth-table row, including
its incident bits, has a logarithmic-size identifier. -/
theorem universal_query_network (k s r : ℕ) (hr : ((k+1)+s+2)^24 ≤ r) :
    let m := k+1
    let g := Fintype.card (Fin m × Bool) + s + 1
    let d := Fin.last k
    ∃ trees : VPVNP.VerifierNetwork.Frame (BatchPins m g m r d) Unit,
      let L := queryLayout d trees
      (∀ x : Fin r → Fin m → Bool,
        L.network.value (L.tables (BooleanLayout.factor (verifier d trees) unaryWeight))
          (fun ij _ => x ij.1 ij.2) =
        ∏ i, ParseTable.table (Fin m × Bool) k s (pairedAddress (x i))) ∧
      L.network.Trivalent ∧
      L.network.bitVolume ≤ 180000000*(m*r)*(Nat.clog 2 (2*m*r)+3)^3 ∧
      Nonempty (Entry L ↪ (Fin (38 + 4*Nat.clog 2 (2*m*r)) → Bool)) := by
  dsimp only
  have hg : Fintype.card (Fin (k+1) × Bool) + s + 1 ≤ 2*(k+1)+s+1 := by simp [Nat.mul_comm]
  obtain ⟨trees, hv, hvol, hdeg⟩ := batched_queries (m := k+1) (s := s)
    (g := Fintype.card (Fin (k+1) × Bool) + s + 1) (Fin.last k) 0 rfl hg hr
  refine ⟨trees, ?_, BooleanLayout.trivalent (verifier (Fin.last k) trees) weightedPin, ?_, ?_⟩
  · intro x
    refine (hv x).trans ?_
    apply Finset.prod_congr (Finset.ext fun _ => by simp)
    intro i _
    exact (universal_table_query k s (x i)).symm
  · exact hvol
  · apply entry_encoding (queryLayout (Fin.last k) trees) (k+1) r
      ((Nat.le_add_right _ _).trans ((Nat.le_add_right _ _).trans hvol))
    intro v
    convert hdeg v using 2
    ext e
    simp

end ParseBatchVerifier

end BorderVNP
end Computability
end OAI
