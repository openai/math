import OAI.Computability.BorderVNP.PackedGridSeedWordsFit
import OAI.Computability.BorderVNP.DiagonalExternalSewNumericName
import OAI.Computability.BorderVNP.ResidueParseReindex

/-! # Original private descriptions on the row-major signed directory -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace ParseTable

open VPVNP

/-- The label printed on a real private sidecar is its coordinate in the
numbered coefficient table of the live reader. -/
noncomputable def signedLiteralCode {k s : ℕ} (ord : Fin (k+1) × Bool ≃ Fin (2*(k+1))) :
    GrammarLabel (Fin (k+1) × Bool) (State (Fin (k+1) × Bool) s) (k+1) ↪ ℕ :=
  (numberedLabelEquiv ord k s).toEmbedding.trans Fin.valEmbedding

theorem signedLiteralCode_bound {k s : ℕ} (ord : Fin (k+1) × Bool ≃ Fin (2*(k+1)))
    (p : GrammarLabel (Fin (k+1) × Bool) (State (Fin (k+1) × Bool) s) (k+1)) :
    signedLiteralCode ord p < Fintype.card (GrammarLabel (Fin (k+1) × Bool) (State (Fin (k+1) × Bool) s) (k+1)) := by
  rw [Fintype.card_congr (numberedLabelEquiv ord k s),Fintype.card_fin]
  exact (numberedLabelEquiv ord k s p).isLt

end ParseTable

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

/-- A private entry is indexed by the original outer batch and tile, each of
which contains a bundle of copies of the same immutable factor description. -/
noncomputable def seedLiteralMatrix (bundles H : ℕ) :
    Fin (bundles*tiles) → Fin (seedDescriptionWidth n r axes d H body) → Bool :=
  fun j => W.seedTape pos code sites edges ports channels groups (ord (finProdFinEquiv.symm j).2) H

/-- The live private factor list addressed by each original directory entry. -/
noncomputable def seedLiteralFactors (bundles : ℕ) (j : Fin (bundles*tiles)) :=
  W.seedStored pos code sites edges ports channels groups (ord (finProdFinEquiv.symm j).2)

variable {bundles factor hw : ℕ} (j : Fin (bundles*GridHosts.tileCount axes d)) (mem : BurstRAM.Memory hw) (slot : ℕ)

/-- Reading the reserved slot of this matrix returns the true factor body
and the exact ordered report labels, bit places and local addresses of the
original tile. The proof applies to every copy of the tile and every reader. -/
theorem seedLiteralMatrix_decoded (hr : 1 ≤ r) (hg : g ≤ r) (hf : 8 ≤ factor) (small : cap ≤ n)
    (lengthRoom : seedDescriptionWidth n r axes d (factor*logWidth r n) body ≤ n)
    (bounded : ∀ z, code z < Fintype.card (GrammarLabel (Fin n × Bool) (Fin g) n))
    (received : ∀ u : Fin (seedDescriptionWidth n r axes d (factor*logWidth r n) body),
      (mem (slot+u.val)).val = (W.seedLiteralMatrix pos code sites edges ports copies bundles (factor*logWidth r n) j u).toNat) :
    let H := factor*logWidth r n
    let c := ord (finProdFinEquiv.symm j).2
    let fs := W.seedLiteralFactors pos code sites edges ports copies bundles j
    let ps := W.seedPositions pos code sites edges ports c
    (RoutingISA.CellPacket.Chunk.box slot H (Packet.Source.boxBody fs)).Stored (fun a => (mem a).val) ∧
      DiagonalTallyBits.WordsAt mem (slot+H+body) (TallySidecar.words H ps) ∧
      (TallySidecar.words H ps).map TapeWord.value = TallySidecar.fields ps :=
  W.seedTape_decoded pos code sites edges ports channels groups _ mem slot hr hg hf small lengthRoom bounded received

end Packing.DeckGrid.WiredWitness

end BorderVNP
end Computability
end OAI
