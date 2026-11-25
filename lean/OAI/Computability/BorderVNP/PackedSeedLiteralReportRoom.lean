import OAI.Computability.BorderVNP.PackedSeedLiteralMatrix
import OAI.Computability.BorderVNP.DiagonalTallyAllocatedInputsBundle

/-! # Native report arithmetic on a delivered original signed descriptor -/

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

local notation "tiles" => GridHosts.tileCount axes d
local notation "cap" => seedBoxCapacity n r axes d (Fintype.card (Direction axes))
local notation "body" => BottomGridBank.bodyBudget cap
local notation3 (prettyPrint := false) "channels" => (groupedGridRows G axes d ord pos copies).edge
local notation3 (prettyPrint := false) "groups" => (Equiv.refl (Fin tiles)).toEmbedding

open DiagonalTallyCellReports Inherited
local notation "oneCopy" => seedSiteCapacity n r axes d

/-- All original body bytes, report fields and staged lanes fit at their
physical origin. Only the assigned header and its retained absolute end
address are needed from placement. The choice of report uses is arbitrary. -/
theorem seedLiteralReport_siteRoom {bundles factor hw : ℕ} (j : Fin (bundles*tiles))
    (b : ReportBundle) (layout : ReportLayout)
    (hr : 1 ≤ r) (hg : g ≤ r) (hf : 8 ≤ factor) (small : cap ≤ n)
    (bounded : ∀ z, code z < Fintype.card (GrammarLabel (Fin n × Bool) (Fin g) n))
    (fieldWidth : layout.fieldWidth=factor*logWidth r n) (bodyWidth : layout.bodyCap=body)
    (bodyEq : b.factors=W.seedLiteralFactors pos code sites edges ports copies bundles j)
    (sidecar : b.positions=W.seedPositions pos code sites edges ports (ord (finProdFinEquiv.symm j).2))
    (capRoom : oneCopy ≤ b.header.cap)
    (origin : b.header.orig = 3*oneCopy+incoming (W.seedGrouped pos) (ord (finProdFinEquiv.symm j).2))
    (endAddr : b.header.boxBase+(b.header.orig+b.header.cap)<2^hw) :
    b.SiteRoom layout hw (seedDescriptionWidth n r axes d (factor*logWidth r n) body) := by
  let c := ord (finProdFinEquiv.symm j).2
  let start := 3*oneCopy+incoming (W.seedGrouped pos) c
  let ps := W.seedPositions pos code sites edges ports c
  have length : ps.length ≤ oneCopy := W.seedPositions_length pos code sites edges ports c
  have marked : b.positions.length ≤ b.header.cap := sidecar ▸ length.trans capRoom
  refine ⟨?_,?_,?_,marked,?_,?_⟩
  · rw [bodyEq,bodyWidth]
    exact W.seedBody_room pos code sites edges ports channels groups c
  · rw [fieldWidth,bodyWidth,sidecar]
    exact sidecar_room _ _ ps length
  · rw [fieldWidth,sidecar]
    exact W.seedPositions_fit pos code sites edges ports c hr hg hf small bounded
  · omega
  · intro i hi
    have hj : i < ps.length := by
      simpa only [sidecar] using hi
    have rel : (ps[i]).stagedReportRel=start+i :=
      (W.sidecarEquiv_fields pos code sites edges ports c start ⟨i,hj⟩).2.2
    have val : b.relative i=start+i := by
      unfold ReportBundle.relative
      rw [sidecar]
      change ((ps[i]?).map TallySidecar.Position.stagedReportRel).getD 0 = _
      rw [List.getElem?_eq_getElem hj]
      exact rel
    rw [val,← show b.header.orig = start from origin]
    omega

end Packing.DeckGrid.WiredWitness

end BorderVNP
end Computability
end OAI
