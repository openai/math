import OAI.Computability.BorderVNP.PackedFrozenSeedRead
import OAI.Computability.BorderVNP.PackedTerminalAugmentedPins
import OAI.Computability.BorderVNP.PackedHistoryNormalizedProfile

/-! # All saved terminal pins on the genuine selected profile of the frozen signed grid -/

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


variable {reserve : ℕ} (widths : ℕ → ℕ)
    (ord : ∀ j, Machine.Guess S (d+1) (fun _ _ => 60*logWidth r n) j ≃ Fin (widths j))
    (fit : broadcastWidth (fan S) widths T ≤ reserve)

local notation3 (prettyPrint := false) "epochFormat" => ProgramSchemas.epoch S (d+1) w fmt T
local notation3 (prettyPrint := false) "aug" => compile steps T le_rfl (repeatLeaf (fan S) source T)
local notation3 (prettyPrint := false) "base" => (plan.execute G order position σ).choose

/-- Geometry, the two true private extents (including every zero hole),
and the full chronological tape are on the three zero-gate selections of
one augmented output at the original native profile. -/
theorem frozen_profile_pins (room : 2*(S.publicProgramFactor^T*initialMass (D:=D) n r d copies headerFactor) < 2^(60*logWidth r n))
    (hook : Compiled.HookRoom S T (60*logWidth r n) (initialMass (D:=D) n r d copies headerFactor))
    (q : (packHistory seed₀ (compiled).machine.epoch T).Index) :
    let s := ((packHistory seed₀ (compiled).machine.epoch T).term q).val
    let p := (compiled).machine.terminalPrivatePrograms names number seed₀ old₀ q
    let raw := ((compiled).machine.nativeCode seed₀ base x rfl widths ord fit q).val
    let input := Retained.branch aug (broadcastOrder (fan S) widths ord T) fit x raw
    (Retained.Terminal.route epochFormat).eval input = s.words ∧
      (∀ b, Covers s.rows.flatten.site (fun v => if b then (p v).program.size else (p v).program.work)
        (Retained.Terminal.width epochFormat b) input) ∧
      (epochFormat).schema.Image ((Retained.Terminal.history epochFormat).eval input)
        (s.rows.flatten.site.trans Fin.valEmbedding) (fun v => (p v).program) := by
  intro s p raw input
  let y := output steps T le_rfl (repeatLeaf (fan S) source T) x ((compiled).machine.packBits seed₀ T le_rfl q)
  have original := plan.frozen_terminal_read G order position W tag sites edges ports table x wr hm seeds number room hook q
  have code := (compiled).machine.nativeCode_readProfile seed₀ base x rfl widths ord fit q
  have views := Retained.Terminal.read epochFormat aug (broadcastOrder (fan S) widths ord T) fit x raw
  have rawEq : readProfile (broadcastOrder (fan S) widths ord T) fit raw = (compiled).machine.packBits seed₀ T le_rfl q := code
  rw [rawEq] at views
  refine ⟨views.1.trans original.1,fun b => ?_,views.2.2.symm ▸ original.2.2⟩
  have sets := original.2.1 b
  have selected : (Retained.Terminal.width epochFormat b).eval input = (assignedColumn b).eval (y ∘ Sum.inl) := by
    refine (views.2.1 b).trans (funext fun z => ?_)
    exact (Frame.initial_eval (fun z => Sum.inr (z.1,b,z.2)) (y ∘ Sum.inl) z).symm
  exact ⟨fun i => by rw [selected]; exact sets.live i, fun i hi => by rw [selected]; exact sets.hole i hi⟩

end PackedHistoryCircuit.Normalized.SelectedSchedule.SeedPlan

end BorderVNP
end Computability
end OAI
