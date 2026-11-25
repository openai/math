import OAI.Computability.BorderVNP.PackedFrozenSeedInputs
import OAI.Computability.BorderVNP.PackedFrozenCompiledHistory

/-! # Exact signed terminal readback from the augmented public seed -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace PackedHistoryCircuit.Normalized.SelectedSchedule.SeedPlan

open Crossing Cover BorderVNP.Epoch BorderVNP.Epoch.Round Shortening Shortening.Adaptive Shortening.PublicCapacity
open Shortening.PreparedBins
open Packing.PhysicalEpochs
open Packing Packing.DeckGrid Packing.Inherited Packing.Inherited.FrozenTape Packing.Inherited.WorkWords
open Diagonal.ExternalSew TeamContraction ParseBatch ParseBatchVerifier Prewire VPVNP VPVNP.ParseGrammar
open EnrichedOuter TeamScales VPVNP.VerifierNetwork
open scoped Classical BorderVNP.Epoch.Cube
attribute [local instance] portFintype
set_option maxHeartbeats 3200000
set_option maxRecDepth 8000
set_option backward.isDefEq.respectTransparency false

variable {D m : ℕ} [NeZero D] {K : Type} [Field K] {e : PaidIdentity K D m} {S : SiteSchedule e}
    {n r d T copies headerFactor Q : ℕ} (plan : SeedPlan S n r d T copies headerFactor Q)
    {teams time pins link inner : ℕ} {Edge : Type} [Fintype Edge] (G : Wiring teams r time pins link inner n Edge)
    (order : Fin (GridHosts.tileCount (Fintype.card (Cube D)) d) ≃ (Fin (Fintype.card (Cube D)) → Deck (d+2)))
    (position : (Fin (Fintype.card (Cube D)) → Deck (d+2)) → {v : EuclideanSpace ℝ (Fin D) // ‖v‖ ≤ 1})
    {σ : Type} [Fintype σ] {g : ℕ} {len : Fin n} {state : Fin g}
    (W : WiredWitness G len D (Fintype.card (Cube D)) d order state)
    (tag : GrammarLabel (Fin n × Bool) (Fin g) n ↪ ℕ) {ns ne np : ℕ}
    (sites : (W.routedFine position).Site ↪ Fin ns) (edges : (W.routedFine position).Edge ↪ Fin ne)
    (ports : Fin r × Fin (publicWidth G) ↪ Fin np)
    (table : (seedBundle G (Fintype.card (Cube D)) d order position copies).Tables K) (x : σ → Bool)

local notation "axes" => Fintype.card (Cube D)
local notation "tiles" => GridHosts.tileCount axes d
local notation "w" => 60*logWidth r n
local notation "mass" => initialMass (D:=D) n r d copies headerFactor
local notation "V" => CoverScale.sites (Cube D) (d+1)
local notation "extent" => copies*GridHosts.inputBlockWidth r n axes d
local notation "header" => WorkWords.grouped V extent
local notation "key" => Equiv.toEmbedding (finCongr (seedPortCount (D:=D) d))
local notation3 (prettyPrint := false) "geom" => (plan.execute G order position σ).choose.eval x
local notation3 (prettyPrint := false) "old₀" => Boundary.seedBirthPrograms S order position W tag sites edges ports table geom
local notation3 "fmt" => Boundary.seedFormat G order position copies
local notation3 "source" => plan.frozenStart G order position σ

local notation3 (prettyPrint := false) "seed₀" => plan.frozenLeaf G order position W tag sites edges ports table x

variable (wr : WidthRanges S (d+1) T (60*logWidth r n)) (hm : 0 < m)
    (seeds : ∀ t, ∀ i : Fin S.rounds,
      ((Cube D → Deck (S.level (offset S (d+1) t) (i.val+1)+1)) × (S.source.pattern i).bins.Bin) → ℕ)
    (number : e.Entry → ℕ)

local notation3 "compiled" => plan.compiled
local notation3 (prettyPrint := false) "steps" => (compiled).tapeSteps fmt header key wr hm
local notation3 (prettyPrint := false) "names" => (compiled).privateSiteRows key seeds

/-- Every real choice of the nested processor history returns the terminal
geometry and both site widths, and every saved site has its exact ordered
immutable records in the same numbered terminal packet. -/
theorem frozen_terminal_read (room : 2*(S.publicProgramFactor^T*initialMass (D:=D) n r d copies headerFactor) < 2^(60*logWidth r n))
    (hook : Compiled.HookRoom S T (60*logWidth r n) (initialMass (D:=D) n r d copies headerFactor))
    (q : (packHistory seed₀ (compiled).machine.epoch T).Index) :
    let a := ((packHistory seed₀ (compiled).machine.epoch T).term q).val
    let y := output steps T le_rfl (repeatLeaf (fan S) source T) x ((compiled).machine.packBits seed₀ T le_rfl q)
    let p := (compiled).machine.terminalPrivatePrograms names number seed₀ old₀ q
    (y ∘ Sum.inl) ∘ Sum.inl = a.words ∧
      (∀ b, Covers a.rows.flatten.site (fun v => if b then (p v).program.size else (p v).program.work)
        (assignedColumn b) (y ∘ Sum.inl)) ∧
      (ProgramSchemas.epoch S (d+1) w fmt T).schema.Image (y ∘ Sum.inr)
        (a.rows.flatten.site.trans Fin.valEmbedding) (fun v => (p v).program) := by
  have widths := plan.frozenLeaf_ports G order position table x
  have b := plan.frozenLeaf_bankCap G order position W tag sites edges ports table x
  have pos : 0 < S.publicProgramFactor^T := Nat.pow_pos (by unfold SiteSchedule.publicProgramFactor SiteSchedule.bankRecordFactor epochRecordFactor; positivity)
  have small := (Nat.le_mul_of_pos_left mass pos).trans ((Nat.le_mul_of_pos_left _ (by decide : 0 < 2)))
  have read := (plan.frozenStart_reads G order position σ (small.trans_lt room) W tag sites edges ports table x).2
  exact (compiled).terminal_tape_read fmt header key wr hm seeds number mass source x seed₀ old₀ widths.1 room hook
    widths.2 b ⟨read.1,read.2⟩ q

end PackedHistoryCircuit.Normalized.SelectedSchedule.SeedPlan

end BorderVNP
end Computability
end OAI
