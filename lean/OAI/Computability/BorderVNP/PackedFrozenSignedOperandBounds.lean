import OAI.Computability.BorderVNP.PackedFrozenSignedBoxResolution
import OAI.Computability.BorderVNP.PackedTerminalRecordWordFits
import OAI.Computability.BorderVNP.PackedHistoryBoxVolume
import OAI.Computability.BorderVNP.PackedBankCompiledScalars
import OAI.Computability.BorderVNP.PackedBankWiredSeedState
import OAI.Computability.BorderVNP.PackedInheritedWorkSignedSewnRoom

/-! # Actual record operands of every attained signed cell, including its final incidence bindings -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace PackedHistoryCircuit.Normalized.SelectedSchedule.SeedPlan

open Crossing Cover BorderVNP.Epoch BorderVNP.Epoch.Round Shortening Shortening.Adaptive Shortening.PublicCapacity
open Packing Packing.DeckGrid Packing.Inherited Packing.PhysicalEpochs Diagonal Diagonal.ExternalSew Diagonal.ExternalSew.RowTrace
open TeamContraction ParseBatch ParseBatchVerifier Prewire VPVNP VPVNP.ParseGrammar EnrichedOuter TeamScales
open Inherited InheritedBank CellAddresses
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
    (number : e.Entry → ℕ) {ap C : ℕ} (oldPort : (Fin ((fan S)^T) × Fin (GridHosts.tileCount (Fintype.card (Cube D)) d)) ↪ Fin ap)
    {R t₁ pins₁ ell inner₁ : ℕ} {Wire : Type}
    (G₁ : Wiring R r t₁ pins₁ ell inner₁ n Wire)
    (count : (fan S)^T*copies=R+1)
    (hp : (fieldSewParams G₁ (Fintype.card (Cube D)) d).Valid)
    (code : (Cube D → Deck (EnrichedOuter.depth S (d+1) T+1)) ≃ Fin C)
    (hm : 0 < m)

local notation3 (prettyPrint := false) "rows" => plan.compiled.privateSiteRows key₀ seeds
local notation3 (prettyPrint := false) "old" q => (M).terminalPrivatePrograms rows number leaf seed q

include hm in
/-- Every local numeric operand in each original attainable branch's installed
records fits the scalar bound, even on teams where the final route revisits a
cell. The term in padded sites charges the greatest relocated box ordinal. -/
theorem frozen_signed_packet_fields
    (installed : (leaf).val.pack.layout = (wiredGrid G₁ axes d order position).groupedRepeat
      (fun _ : Fin tiles => GridHosts.inputBlockWidth r n axes d) order copies)
    (q : (packHistory leaf (M).epoch T).Index) (dir : Directory.Layout) (room : 0<(B).sites) :
    let actual := ((packHistory leaf (M).epoch T).term q).val
    let net := enrichedSewnLayout G₁ axes d order position count M leaf installed q
    let final := enrichedSewnPrograms G₁ axes d order position count M leaf installed oldPort hp q (old q)
    let loc := fun v => code (reduceMove (EnrichedOuter.depth S (d+1) T) (actual.route.origin v))
    let phys := fun v => (final v).program
    let edge := FieldExport.mergedEdges (fieldSewParams G₁ axes d) hp actual.rows.edge
    (∀ c, guessedSize net loc c+siteSize net loc c (fun v => (phys v).size)+suppliedSize net loc c ≤ cap₀) ∧
      ∀ (owner : Fin (B).sites → ℕ), (∀ v, owner (actual.rows.site v)=(loc v).val) →
        ∀ (c : Fin C) reports, ∀ rec ∈ (FinalCell.directory owner net (fun v => (loc v).val) actual.rows.site
          edge finProdFinEquiv.toEmbedding phys c.val reports).records,
          CellSparse.Packet.RecordFields rec (max cap₀ (B).sites+scalar₀+1) := by
  intro actual net final loc phys edge
  have bank := plan.frozenLeaf_bankCap G order position W tag sites edges ports table x
  have capacity := enrichedSewn_address_capacity G₁ axes d order position count M leaf installed oldPort hp q
    rows number seed code B₀ bank
  have born := (EnrichedOuter.Boundary.wiredSeedStatePrograms_bounds S W position tag sites edges ports copies table geometry 0).2.2
  have scalars (v : net.Site) := plan.compiled.terminalPrivatePrograms_localScalars_of_extent key₀ seeds number leaf
    seed hm B₀ (max 2 (max copies K₀)) bank born q v
  have staged (v : net.Site) : (phys v).ScalarBound scalar₀ := by
    have here : (phys v).ScalarBound (max (max (max 2 (max copies K₀)) (coeff*(scale₀+1)))
        (max 1 (phys v).size)) :=
      SewnField.sewnPrograms_scalarBound _ _ _ _ _ _ _ _ _ _ _ (old q) v (scalars v)
    intro a ha
    exact (here a ha).trans (max_le_max le_rfl (max_le_max le_rfl (capacity.2 v)))
  refine ⟨capacity.1,?_⟩
  intro owner owners c reports rec occurrence
  let publicDir := {dir with sites := tiles, entries := (fan S)^T*tiles}
  have cnt := scheduledBoxes_count publicDir (S:=S) (start:=d+1) (T:=T) rfl number room
  have boxes : (∑ i, (FinalCell.slots actual.rows.site (fun v => (phys v).boxes) i).length) ≤ (B).sites := by
    apply le_trans _ cnt
    apply Finset.sum_le_sum
    intro i _
    have slot := plan.frozen_signed_boxes_resolved G order position W tag sites edges ports table x rows number q dir room i
    exact le_of_eq ((congrArg List.length slot).symm.trans (List.length_map ..))
  have out := FinalCell.packet_recordFields net (fun v => (loc v).val) actual.rows.site edge finProdFinEquiv.toEmbedding
    owner phys owners (fun v => (final v).size) staged boxes c.val reports rec occurrence
  have stack : FinalCell.countBase net (fun v => (loc v).val) phys c.val ≤ cap₀ := by
    let previous := (flattenPack T actual.pack).layout
    let prior := old q
    let test := fun v : previous.Site => (loc v).val = c.val
    have same : test = (fun v : previous.Site => reduceMove (EnrichedOuter.depth S (d+1) T) (actual.route.origin v) = code.symm c) := by
      funext v
      exact propext (Fin.val_inj.trans code.eq_symm_apply.symm)
    have raw := (M).terminalPrivatePrograms_bankCap rows number leaf seed true B₀ bank q
    have mass : localRecords previous true prior.bankFields.prior prior.bankFields.payload test ≤ scale₀ := by
      rw [same]
      exact (Nat.le_add_left _ 1).trans (raw (code.symm c))
    exact (enrichedSewn_region_capacity G₁ axes d order position count M leaf installed oldPort hp q prior
      (fun v => (loc v).val) c.val).trans (Nat.mul_le_mul_left 15 mass)
  exact out.mono (Nat.add_le_add_right (Nat.add_le_add_right (max_le_max stack le_rfl) _) 1)

end PackedHistoryCircuit.Normalized.SelectedSchedule.SeedPlan

end BorderVNP
end Computability
end OAI
