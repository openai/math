import OAI.Computability.BorderVNP.PackedSeedLiteralReportRoom
import OAI.Computability.BorderVNP.DiagonalCanonicalReportDirectory

/-! # Actual parameter and exponent indices on every original report sidecar -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.DeckGrid.WiredWitness

open Crossing CellSparse Cover TeamContraction Diagonal.ExternalSew Diagonal.ExternalSew.RowTrace
open Shortening.PublicCapacity
open ParseBatch ParseBatchVerifier Prewire VPVNP VPVNP.ParseGrammar TeamScales
open scoped Classical

variable {R r t pins link inner n g : ℕ} {Edge : Type} [Fintype Edge] {G : Wiring R r t pins link inner n Edge}
    {len : Fin n} {D axes d : ℕ} {ord : Fin (GridHosts.tileCount axes d) ≃ (Fin axes → Deck (d+2))}
    {state : Fin g} (W : WiredWitness G len D axes d ord state)
    (pos : (Fin axes → Deck (d+2)) → {v : EuclideanSpace ℝ (Fin D) // ‖v‖ ≤ 1})
    (code : GrammarLabel (Fin n × Bool) (Fin g) n ↪ ℕ) {ns ne np : ℕ}
    (sites : (W.routedFine pos).Site ↪ Fin ns) (edges : (W.routedFine pos).Edge ↪ Fin ne)
    (ports : Fin r × Fin (publicWidth G) ↪ Fin np) (copies : ℕ)


/-- Genuine original sidecars name finite exponent places. A place fits in the
bit *index* of a machine word, as required for the dynamic decoder shift. -/
theorem seedReport_marks {w : ℕ} (c : Fin axes → Deck (d+2))
    (hr : 0<r) (word : logWidth r n ≤ w) (label : ∀ s, code s<2^w) :
    ∀ p∈W.seedPositions pos code sites edges ports c, p.parameter<2^w ∧ p.place<w := by
  intro p hp
  obtain ⟨i,rfl⟩ := List.mem_iff_get.mp hp
  let start := 3*seedSiteCapacity n r axes d+Inherited.incoming (W.seedGrouped pos) c
  let j := W.sidecarEquiv pos code sites edges ports c start i
  obtain ⟨param,place,_⟩ := W.sidecarEquiv_fields pos code sites edges ports c start i
  have room : r*(2*len.val+1)+1 ≤ 2*n*r := by
    have slots : 2*len.val+2 ≤ 2*n := by have := len.isLt; omega
    nlinarith [Nat.mul_le_mul_left r slots]
  have limited : Nat.clog 2 (r*(2*len.val+1)+1) ≤ logWidth r n := by
    rw [public_logWidth]
    exact Nat.clog_mono_right _ room
  exact ⟨param.symm ▸ label j.val.1,place.symm ▸ j.val.2.isLt.trans_le (limited.trans word)⟩

end Packing.DeckGrid.WiredWitness

namespace DiagonalTallyCellReports.ReportDirectory

/-- The native filtering and stable grouping preserve the concrete bounds on
all parameter names and shift amounts, including empty source and cell rows. -/
theorem sourceCells_marks {J C w : ℕ} (l : ReportLayout) (home : Fin J → Fin C) (payload : Fin J → ReportBundle)
    (team : ℕ) (owner bank supplied wire : ℕ → ℕ) (digits : ℕ → Fin l.gadgets → Fin l.countWidth → Bool)
    (fields : ∀ j, ∀ p∈(payload j).positions, p.parameter<2^w ∧ p.place<w) :
    ∀ c∈sourceCells l home payload team owner bank supplied wire digits,
    ∀ b∈c.bundles, ∀ p∈b.positions, p.parameter<2^w ∧ p.place<w := by
  intro c hc b hb
  obtain ⟨i,_,rfl⟩ := List.mem_map.mp hc
  change b ∈ (Packing.BundleDirectory.sourceRows home i).map payload at hb
  obtain ⟨j,_,rfl⟩ := List.mem_map.mp hb
  exact fields j

end DiagonalTallyCellReports.ReportDirectory

end BorderVNP
end Computability
end OAI
