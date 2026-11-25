import OAI.Computability.BorderVNP.PackedFrozenNativeProjection
import OAI.Computability.BorderVNP.PackedFrozenSeedInputs
import OAI.Computability.BorderVNP.PackedHistoryReservedExecute

/-! # Canonical histories and returned words of the fixed-address frozen table -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace PackedHistoryCircuit.Normalized.SelectedSchedule.SeedPlan

open Crossing Cover BorderVNP.Epoch BorderVNP.Epoch.Round Shortening Shortening.Adaptive Shortening.PublicCapacity
open Packing Packing.DeckGrid Packing.Inherited Packing.Inherited.FrozenTape
open Diagonal Diagonal.ExternalSew Diagonal.ExternalSew.RowTrace TeamContraction ParseBatch ParseBatchVerifier Prewire
open VPVNP VPVNP.ParseGrammar EnrichedOuter TeamScales VPVNP.VerifierNetwork
open scoped Classical BorderVNP.Epoch.Cube

attribute [local instance] portFintype
set_option maxHeartbeats 2200000
set_option maxRecDepth 6000

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

local notation "w" => 60*logWidth r n
local notation3 (prettyPrint := false) "fmt" => Boundary.seedFormat G order position copies
local notation3 (prettyPrint := false) "source" => plan.frozenStart G order position σ
local notation3 (prettyPrint := false) "geo" => (plan.execute G order position σ).choose
local notation3 (prettyPrint := false) "seed" => plan.frozenLeaf G order position W tag sites edges ports table x
local notation "header" => WorkWords.grouped (CoverScale.sites (Cube D) (d+1))
  (copies*GridHosts.inputBlockWidth r n (Fintype.card (Cube D)) d)
local notation "key" => Equiv.toEmbedding (finCongr (seedPortCount (D:=D) d))

variable (wr : WidthRanges S (d+1) T (60*logWidth r n)) (hm : 0 < «m»)
    {reserve outs field : ℕ} (widths : ℕ → ℕ)
    (slots : ∀ j, Machine.Guess S (d+1) (fun _ _ => 60*logWidth r n) j ≃ Fin (widths j))
    (fits : broadcastWidth (fan S) widths T ≤ reserve)
    (emit : Frame ((σ ⊕ Fin reserve) ⊕ ProgramSchemas.outerPins S (d+1) (60*logWidth r n)
      (Boundary.seedFormat G order position copies) T) (Fin outs × Fin field))
local notation3 (prettyPrint := false) "M" => plan.compiled.machine
local notation3 (prettyPrint := false) "steps" => plan.compiled.tapeSteps fmt header key wr hm
local notation3 (prettyPrint := false) "hist" => compile steps T le_rfl (repeatLeaf (fan S) source T)
local notation3 (prettyPrint := false) "ord" => broadcastOrder (fan S) widths slots T
local notation3 (prettyPrint := false) "code" => (M).nativeCode seed geo x rfl widths slots fits
local notation3 (prettyPrint := false) "tab" ceiling => reservedGeometryTable hist ord fits emit x ceiling

/-- The physical fixed-address table accepts exactly one original history code.
Quantification includes every unused broadcast bit and every failed inner guard. -/
theorem frozenProfile_valid (ceiling : ℕ) (word : Fin reserve → Bool) :
    GeometryOutput.validBit (tab ceiling) (Sum.elim word Fin.elim0)=true ↔
      ∃! q : (packHistory seed (M).epoch T).Index, (code q).val=word := by
  have same := Boundary.seedTapeFrame_geometry S plan G order position geo x
  exact ((reserved_semantics hist ord fits emit x ceiling word).1).trans
    (plan.compiled.tapeCode_valid fmt header key wr hm source geo x same seed rfl widths slots fits word)

/-- On the unique accepted history, the interpreter reads the emitter on the
complete augmented terminal state for that very history. This includes all
immutable rows, private array widths and returned sparse public fields. -/
theorem frozenProfile_words (ceiling : ℕ) (q : (packHistory seed (M).epoch T).Index) :
    nativeTableWords (tab ceiling) (code q).val = fun i => ParseBatchSort.value (fun j =>
      emit.eval (Sum.elim (Sum.elim x (code q).val)
        (output steps T le_rfl (repeatLeaf (fan S) source T) x ((M).packBits seed T le_rfl q))) (i,j)) := by
  have words := (reserved_semantics hist ord fits emit x ceiling (code q).val).2
  unfold emittedWords at words
  rw [(M).nativeCode_readProfile seed geo x rfl widths slots fits q] at words
  exact words

end PackedHistoryCircuit.Normalized.SelectedSchedule.SeedPlan

end BorderVNP
end Computability
end OAI
