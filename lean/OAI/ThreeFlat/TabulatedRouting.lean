import OAI.ThreeFlat.ExpanderTabulation
import OAI.ThreeFlat.ExpanderTablePower

namespace OAI
/-! # A uniformly tabulated scalar expander at each dyadic order -/

namespace ThreeFlat.RouteUnits

open BinPackingGames.Foundations.PCP ExpanderTables SpectralReturn
open scoped BigOperators

/-- One finite seed collection handles every order and power. The first term
counts rows of the seed and square-zigzag stages; the sum counts the rows
of the subsequent repeated squares. -/
theorem exists_tabulated_routing_graphs :
    ∃ seed : (i : Fin 448) → Table (2 ^ i.val) dyadicPortDegree,
    ∃ cloud : Table (dyadicPortDegree * dyadicPortDegree) Expanders.baseDegree,
      ∀ k j : ℕ,
        let T := dyadicTable seed cloud k
        SpectralCertificate (graph (poweredTable T j)) ((1 / 2 : ℝ) ^ (2 ^ j)) ∧
        seededRowCount (2 ^ (seedIndex k).val) dyadicPortDegree (k / 448) +
          (∑ i ∈ Finset.range (j + 1), (poweredTable T i).rows.toList.length) ≤
          (j + 3) * (poweredTable T j).rows.toList.length := by
  obtain ⟨seed, cloud, hs, hc⟩ := exists_dyadicTable_seeds
  refine ⟨seed, cloud, fun k j => ?_⟩
  let T := dyadicTable seed cloud k
  let : NeZero dyadicPortDegree := ⟨by decide⟩
  refine ⟨poweredTable_certificate T (dyadicTable_certificate seed cloud hs hc k) j, ?_⟩
  have hdeg : dyadicPortDegree ≤ powerDegree dyadicPortDegree j := by
    rw [powerDegree_eq]
    exact Nat.le_self_pow (by positivity) _
  have hsize : 2 ^ k * dyadicPortDegree ≤ (poweredTable T j).rows.toList.length := by
    rw [row_count]
    exact Nat.mul_le_mul_left _ hdeg
  have h := (dyadicTable_row_bound k).trans (Nat.mul_le_mul_left 2 hsize)
  calc
    _ ≤ 2 * (poweredTable T j).rows.toList.length +
        (j + 1) * (poweredTable T j).rows.toList.length := add_le_add h (poweredTable_rows_le T j)
    _ = _ := by ring

/-- Reindexing the final port count uses only equality of naturals and
keeps each numbered vertex fixed. -/
theorem powered_routing_graphs_of_tables (j : ℕ) :
    ∃ h : ℕ, 2 ^ j ≤ h ∧ ∀ k : ℕ,
      ∃ G : PoweringWalks.PortGraph (Fin (2 ^ k)) (Fin (2 * h)),
        SpectralCertificate G ((1 / 2 : ℝ) ^ (2 ^ j)) := by
  obtain ⟨seed, cloud, cert⟩ := exists_tabulated_routing_graphs
  let h := 2 ^ (224 * 2 ^ j - 1)
  have he : 0 < (2 : ℕ) ^ j := by positivity
  have covers : 2 ^ j ≤ h := Nat.pow_le_pow_right (by decide : 0 < 2)
    (by have := j.lt_two_pow_self; omega : j ≤ 224 * 2 ^ j - 1)
  have pbase : dyadicPortDegree = 2 ^ 224 := by
    change ((2 : ℕ) ^ 16) ^ 7 * ((2 : ℕ) ^ 16) ^ 7 = _
    rw [← sq, ← pow_mul, ← pow_mul]
  have degree : powerDegree dyadicPortDegree j = 2 * h := by
    rw [powerDegree_eq, pbase, ← pow_mul]
    dsimp [h]
    rw [Nat.mul_comm 2, ← pow_succ]
    congr 1
    omega
  refine ⟨h, covers, fun k => ?_⟩
  let G := graph (poweredTable (dyadicTable seed cloud k) j)
  exact ⟨GraphTransport.reindex G (Equiv.refl _) (finCongr degree),
    GraphTransport.reindex_spectralCertificate _ _ _ _ (cert k j).1⟩

end ThreeFlat.RouteUnits

end OAI
