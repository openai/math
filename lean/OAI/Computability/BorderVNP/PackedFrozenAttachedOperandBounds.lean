import OAI.Computability.BorderVNP.PackedFrozenSignedOperandBounds
import OAI.Computability.BorderVNP.PackedTerminalSignedHosts
import OAI.Computability.BorderVNP.DiagonalSignedCountWordRoom

/-! # Address and record bounds on the attached hosts of the signed terminal emitter -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace PackedHistoryCircuit.Normalized.SelectedSchedule.SeedPlan

open Crossing Cover BorderVNP.Epoch BorderVNP.Epoch.Round Shortening Shortening.Adaptive Shortening.PublicCapacity
open Packing Packing.DeckGrid Packing.Inherited Packing.PhysicalEpochs Diagonal Diagonal.ExternalSew Diagonal.ExternalSew.RowTrace
open TeamContraction ParseBatch ParseBatchVerifier Prewire VPVNP VPVNP.ParseGrammar EnrichedOuter TeamScales
open Inherited InheritedBank CellAddresses ExternalSew.FieldExport ExternalSew.GridHosts
open scoped Classical BorderVNP.Epoch.Cube
attribute [local instance] portFintype
set_option maxHeartbeats 1800000
set_option maxRecDepth 6500
set_option backward.isDefEq.respectTransparency false

variable {D m : ℕ} [NeZero D] {K : Type} [Field K] {e : PaidIdentity K D m} {S : SiteSchedule e}
    {n r d T copies header Q : ℕ} (plan : SeedPlan S n r d T copies header Q)
    {teams time pins link inner : ℕ} {Edge : Type} [Fintype Edge] (G : Wiring teams r time pins link inner n Edge)
    (order : Fin (GridHosts.tileCount (Fintype.card (Cube D)) d) ≃ (Fin (Fintype.card (Cube D)) → Deck (d+2)))
    (position : (Fin (Fintype.card (Cube D)) → Deck (d+2)) → {v : EuclideanSpace ℝ (Fin D) // ‖v‖ ≤ 1})
    {σ : Type} [Fintype σ] {g : ℕ} {len : Fin n} {key : Fin g}
    (W : WiredWitness G len D (Fintype.card (Cube D)) d order key)
    (tag : GrammarLabel (Fin n × Bool) (Fin g) n ↪ ℕ) {ns ne np : ℕ}
    (sites : (W.routedFine position).Site ↪ Fin ns) (edges : (W.routedFine position).Edge ↪ Fin ne)
    (ports : Fin r × Fin (publicWidth G) ↪ Fin np)
    (table : (seedBundle G (Fintype.card (Cube D)) d order position copies).Tables K) (x : σ → Bool)
local notation "axes" => Fintype.card (Cube D)
local notation "tiles" => GridHosts.tileCount axes d
local notation3 (prettyPrint := false) "leaf" => plan.frozenLeaf G order position W tag sites edges ports table x
local notation3 (prettyPrint := false) "geometry" => (plan.execute G order position σ).choose.eval x
local notation3 (prettyPrint := false) "seed" => Boundary.seedBirthPrograms S order position W tag sites edges ports table geometry

local notation3 (prettyPrint := false) "M" => plan.compiled.machine
local notation "K₀" => seedBoxCapacity n r axes d (Fintype.card (Direction axes))
local notation "B₀" => initialMass (D:=D) n r d copies header
local notation "key₀" => Equiv.toEmbedding (finCongr (seedPortCount (D:=D) d))
local notation "scale₀" => S.publicProgramFactor^T * B₀
local notation "coeff" => (birthWordCoefficient e+8)*(BankCharges.bound e+1)*(S.populationFactor+2)
local notation "cap₀" => 15*scale₀
local notation "scalar₀" => max (max (max 2 (max copies K₀)) (coeff*(scale₀+1))) (max 1 cap₀)
local notation "B" => boundaryShape S (d+1) T

variable (seeds : ∀ h, ∀ i : Fin S.rounds,
    ((Cube D → Deck (S.level (offset S (d+1) h) (i.val+1)+1)) × (S.source.pattern i).bins.Bin) → ℕ)
    (number : e.Entry → ℕ) {C : ℕ}
    {R t₁ pins₁ ell inner₁ : ℕ} {Wire : Type}
    (G₁ : Wiring R r t₁ pins₁ ell inner₁ n Wire)
    (count : (fan S)^T*copies=R+1)
    (hp : (fieldSewParams G₁ (Fintype.card (Cube D)) d).Valid)
    (code : (Cube D → Deck (EnrichedOuter.depth S (d+1) T+1)) ≃ Fin C)
    (hm : 0 < m)


local notation3 (prettyPrint := false) "oldPort" => Flat.portRows T (privatePorts S key₀ T)
local notation3 (prettyPrint := false) "rows" => plan.compiled.privateSiteRows key₀ seeds
local notation3 (prettyPrint := false) "old" q => (M).terminalPrivatePrograms rows number leaf seed q
local notation "p₁" => fieldSewParams G₁ axes d
local notation "g₁" => GridHosts.inputBlockWidth r n axes d
local notation3 (prettyPrint := false) "limit" => max cap₀ (B).sites+scalar₀+1

include hm in
/-- Room and validity for the private scalar fields on the address frame's
actual attachment rule. They are expressed on precisely the network, current
cell map, merged edges, grouped ports and local programs used by the frozen
terminal emitter. The output number of a real cell is needed only on
occupied row addresses. -/
theorem frozen_attached_packet_bounds {word gadgets : ℕ}
    (room : limit < 2^word) (counts : cap₀+gadgets*word ≤ 2^word)
    (installed : (leaf).val.pack.layout = (wiredGrid G₁ axes d order position).groupedRepeat
      (fun _ : Fin tiles => GridHosts.inputBlockWidth r n axes d) order copies)
    (q : (packHistory leaf (M).epoch T).Index) (dir : Directory.Layout) (sitePos : 0<(B).sites) :
    let state := ((packHistory leaf (M).epoch T).term q).val
    let before := (flattenPack T state.pack).layout
    let attached := attachedHosts G₁ Fintype.card_pos count before
    let lane := groupedLane G₁ tiles Fintype.card_pos ((fan S)^T) copies count
    let merged := mergedEdges p₁ hp state.rows.edge
    let ports := (finProdFinEquiv : FreeBlock R tiles ≃ Fin ((R+1)*tiles)).toEmbedding
    let net := finalLayout p₁ attached
    let progs := SewnField.sewnPrograms before lane attached.bundle (fun _ : FreeBlock R tiles => g₁)
      (freeLane hp.block (gridRoom G₁ Fintype.card_pos)) attached.groupOwner (attached.groupAligned hp.block (gridRoom G₁ Fintype.card_pos))
      state.rows.edge oldPort merged ports (old q)
    let cell := fun v => code (reduceMove (EnrichedOuter.depth S (d+1) T) (state.route.origin v))
    let stack := fun c => guessedSize net cell c+siteSize net cell c (fun v => (progs v).program.size)+suppliedSize net cell c
    (∀ c, stack c < 2^word) ∧ (∀ c, stack c+gadgets*word ≤ 2^word) ∧
      (∀ c, stack c ≤ cap₀) ∧
      ∀ (owner : Fin (B).sites → ℕ), (∀ v, owner (state.rows.site v)=(cell v).val) →
        ∀ (c : Fin C) reports, ∀ rec ∈ (FinalCell.directory owner net (fun v => (cell v).val) state.rows.site
          merged ports (fun v => (progs v).program) c.val reports).records, CellSparse.Packet.RecordFields rec limit := by
  intro state before attached lane merged ports
  have same : attached = enrichedBlockHosts G₁ axes d order position count M leaf installed q :=
    enrichedBlockHosts_attached G₁ axes d order position count M leaf installed q
  rw [same]
  intro net progs cell stack
  have all := plan.frozen_signed_packet_fields G order position W tag sites edges _ table x seeds number oldPort
    G₁ count hp code hm installed q dir sitePos
  have cap : cap₀ < 2^word := (le_max_left cap₀ (B).sites).trans_lt
    ((Nat.le_add_right _ scalar₀).trans_lt ((Nat.le_add_right _ 1).trans_lt room))
  exact ⟨fun c => (all.1 c).trans_lt cap,fun c => (Nat.add_le_add_right (all.1 c) _).trans counts,all.1,all.2⟩

end PackedHistoryCircuit.Normalized.SelectedSchedule.SeedPlan

end BorderVNP
end Computability
end OAI
