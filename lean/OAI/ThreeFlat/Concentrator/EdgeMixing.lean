import OAI.Computability.BinPacking.Expanders.SpectralCut
import OAI.ThreeFlat.Concentrator.Halving

namespace OAI
/-! # Induced port edges and the reserve matching -/

namespace ThreeFlat.Concentrator

open BinPackingGames.Foundations.PCP PoweringWalks SpectralReturn SpectralCut

variable {V D E : Type*} [Fintype V] [Fintype D] [Nonempty V] [Nonempty D] [DecidableEq V]

/-- A request occupies a distinct directed port and can be assigned to either endpoint. -/
def portReserveGraph (G : PortGraph V D) (port : E ↪ V × D) : ReserveGraph E V where
  src e := (port e).1
  dst e := (G.rot (port e)).1

private theorem induced_port_density (G : PortGraph V D) {lam : ℝ}
    (cert : SpectralCertificate G lam) (H : Finset V) :
    ((Finset.univ.filter (fun e : V × D => e.1 ∈ H ∧ (G.rot e).1 ∈ H)).card : ℝ) /
        Fintype.card (V × D) ≤ mean (indicator H) * (mean (indicator H) + lam) := by
  classical
  let f := indicator H
  let edges := Finset.univ.filter (fun e : V × D => e.1 ∈ H ∧ (G.rot e).1 ∈ H)
  have edgeMean : (edges.card : ℝ) / Fintype.card (V × D) =
      correlation f (averagingOperator G f) := by
    rw [← mean_indicator edges]
    have hi : indicator edges = fun e : V × D => f e.1 * f (G.rot e).1 := by
      funext e
      by_cases hl : e.1 ∈ H <;> by_cases hr : (G.rot e).1 ∈ H <;>
        simp [f, indicator, edges, hl, hr]
    rw [hi, mean_prod]
    apply congrArg mean
    funext v
    change mean (fun d : D => f v * f (G.rot (v,d)).1) = _
    rw [mean_mul_left]
    rfl
  have hz : mean (fun x => f x - mean f) = 0 := by rw [mean_sub, mean_const, sub_self]
  have hE : energy (fun x => f x - mean f) ≤ mean f := by
    rw [energy_sub_const, energy_indicator]
    nlinarith [sq_nonneg (mean f)]
  have bound := zero_mean_correlation_bound G lam cert _ hz 1
  have centered := correlation_centered G f 1
  simp only [iterateOperator, pow_one] at bound centered
  change (edges.card : ℝ) / Fintype.card (V × D) ≤ mean f * (mean f + lam)
  rw [edgeMean, centered]
  nlinarith only [bound, mul_le_mul_of_nonneg_left hE cert.nonnegative]

/-- The number of directed requests with both endpoints in `H`. Parallel edges and loops
retain their indexed port multiplicities. -/
theorem internalEdges_card_le (G : PortGraph V D) {lam : ℝ} (cert : SpectralCertificate G lam)
    (port : E ↪ V × D) (all : Finset E) (H : Finset V) :
    (((portReserveGraph G port).internalEdges all H).card : ℝ) ≤
      Fintype.card D * (H.card : ℝ) * ((H.card : ℝ) / Fintype.card V + lam) := by
  classical
  let edges := Finset.univ.filter (fun e : V × D => e.1 ∈ H ∧ (G.rot e).1 ∈ H)
  have sub : ((portReserveGraph G port).internalEdges all H).map port ⊆ edges := by
    intro e he
    obtain ⟨a, ha, rfl⟩ := Finset.mem_map.mp he
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp ha).2⟩
  have rest : ((portReserveGraph G port).internalEdges all H).card ≤ edges.card := by
    simpa using Finset.card_le_card sub
  have h := induced_port_density G cert H
  rw [mean_indicator, Fintype.card_prod, Nat.cast_mul] at h
  have hV : (0 : ℝ) < Fintype.card V := by exact_mod_cast Fintype.card_pos
  have hD : (0 : ℝ) < Fintype.card D := by exact_mod_cast Fintype.card_pos
  apply le_trans (by exact_mod_cast rest : _ ≤ (edges.card : ℝ))
  apply ((div_le_iff₀ (mul_pos hV hD)).mp h).trans_eq
  field_simp

/-- The sparse-induced-edge condition used by the reserve pass, for every active set
with at most `threshold` requests. -/
theorem internalEdges_sparse_of_budget (G : PortGraph V D) {lam : ℝ}
    (cert : SpectralCertificate G lam) (port : E ↪ V × D) (all : Finset E)
    (slots threshold : ℕ) (budget : 4 * (Fintype.card D : ℝ) *
      (2 * (threshold : ℝ) / ((slots + 1 : ℝ) * Fintype.card V) + lam) ≤ slots + 1)
    (H : Finset V) (heavy : (slots + 1) * H.card ≤ 2 * threshold) :
    4 * ((portReserveGraph G port).internalEdges all H).card ≤ (slots + 1) * H.card := by
  have hn : (0 : ℝ) < Fintype.card V := by exact_mod_cast Fintype.card_pos
  have hs : 0 < (slots + 1 : ℝ) := by positivity
  have hH : (slots + 1 : ℝ) * H.card ≤ 2 * threshold := by exact_mod_cast heavy
  have hden : (H.card : ℝ) / Fintype.card V ≤
      2 * threshold / ((slots + 1 : ℝ) * Fintype.card V) := by
    rw [div_le_div_iff₀ hn (mul_pos hs hn)]
    nlinarith only [mul_le_mul_of_nonneg_right hH hn.le]
  have rate : (H.card : ℝ) / Fintype.card V + lam ≤
      2 * threshold / ((slots + 1 : ℝ) * Fintype.card V) + lam := by linarith only [hden]
  have coeff : 4 * (Fintype.card D : ℝ) * ((H.card : ℝ) / Fintype.card V + lam) ≤ slots + 1 :=
    (mul_le_mul_of_nonneg_left rate (by positivity)).trans budget
  have cardBound := internalEdges_card_le G cert port all H
  have target : 4 * (((portReserveGraph G port).internalEdges all H).card : ℝ) ≤
      (slots + 1 : ℝ) * H.card := by
    nlinarith only [cardBound, mul_le_mul_of_nonneg_right coeff (Nat.cast_nonneg H.card)]
  exact_mod_cast target

end ThreeFlat.Concentrator

end OAI
