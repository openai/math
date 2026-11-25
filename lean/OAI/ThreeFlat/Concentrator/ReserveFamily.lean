import OAI.ThreeFlat.Concentrator.Budgets
import OAI.ThreeFlat.Concentrator.ExpanderSize
import OAI.ThreeFlat.Concentrator.ReservePorts

namespace OAI
/-! # The fixed-degree family for the reserve pass -/

namespace ThreeFlat.Concentrator

open BinPackingGames.Foundations.PCP PoweringWalks SpectralReturn

/-- One degree works for all large work sizes. Every request receives a directed port,
so both its reserve endpoints are fixed before the mask is chosen. -/
theorem exists_reserve_family_with_size {C q : ℕ} (hC : 0 < C) (hq : 0 < q) :
    ∃ d : ℕ, 0 < d ∧ ∀ R : ℕ, d ≤ C * R → ∃ m : ℕ, 0 < m ∧ m ≤ 2 * (C * R) ∧
      q * (m * reserveSlots C q d + reserveThreshold C q R) ≤ R ∧
      ∃ G : ReserveGraph (Fin (C * R)) (Fin m),
        (∀ v, (G.incident Finset.univ v).card ≤ 2 * d) ∧
        ∀ H : Finset (Fin m), (reserveSlots C q d + 1) * H.card ≤ 2 * reserveThreshold C q R →
          4 * (G.internalEdges Finset.univ H).card ≤ (reserveSlots C q d + 1) * H.card := by
  have hK : 0 < budgetDenom C q := by unfold budgetDenom; positivity
  obtain ⟨d, hd, _, lam, _, spectral, _, graphs⟩ :=
    exists_concentrator_expanders (budgetDenom C q)
      (show 0 < 1 / (8 * (budgetDenom C q : ℝ)) by positivity)
  refine ⟨d, hd, fun R large => ?_⟩
  obtain ⟨k, hlow, hhigh, G, cert⟩ := graphs _ large
  let m := 2 ^ k
  have hm : 0 < m := pow_pos (by decide) _
  let : NeZero m := ⟨hm.ne'⟩
  let : NeZero d := ⟨hd.ne'⟩
  let port : Fin (C * R) ↪ Fin m × Fin d := reservePortEmbedding hlow
  have capacity := reserve_capacity hC hq (m := m) (D := d) (R := R) (by simpa [Nat.mul_assoc] using hhigh)
  have budget := reserve_sparse_budget hC hq hm hd hlow spectral
  refine ⟨m, hm, (Nat.le_mul_of_pos_right m hd).trans hhigh, capacity, portReserveGraph G port, ?_, ?_⟩
  · intro v
    simpa using incident_card_le_two_mul_degree G port Finset.univ v
  · intro H hH
    apply internalEdges_sparse_of_budget G cert port Finset.univ _ _ _ H hH
    simpa only [Fintype.card_fin] using budget

/-- The reserve family with the degree and sparse-mixing bounds. -/
theorem exists_reserve_family {C q : ℕ} (hC : 0 < C) (hq : 0 < q) :
    ∃ d : ℕ, 0 < d ∧ ∀ R : ℕ, d ≤ C * R → ∃ m : ℕ, 0 < m ∧
      q * (m * reserveSlots C q d + reserveThreshold C q R) ≤ R ∧
      ∃ G : ReserveGraph (Fin (C * R)) (Fin m),
        (∀ v, (G.incident Finset.univ v).card ≤ 2 * d) ∧
        ∀ H : Finset (Fin m), (reserveSlots C q d + 1) * H.card ≤ 2 * reserveThreshold C q R →
          4 * (G.internalEdges Finset.univ H).card ≤ (reserveSlots C q d + 1) * H.card := by
  obtain ⟨d, hd, family⟩ := exists_reserve_family_with_size hC hq
  refine ⟨d, hd, fun R large => ?_⟩
  obtain ⟨m, hm, _, capacity, G, rev, sparse⟩ := family R large
  exact ⟨m, hm, capacity, G, rev, sparse⟩

end ThreeFlat.Concentrator

end OAI
