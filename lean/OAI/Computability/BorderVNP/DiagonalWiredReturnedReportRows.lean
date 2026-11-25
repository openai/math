import OAI.Computability.BorderVNP.DiagonalReceivedReportUseReadback
import OAI.Computability.BorderVNP.PackedRetainedReportUse
import OAI.Computability.BorderVNP.PackedSeedCoreChoices

/-! # The checked retained source bundles of the prewired named verifier -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.DeckGrid.WiredWitness

open Crossing CellSparse GridBoxes BottomReports Cover TeamContraction GridPlacement
open Diagonal.CellEntries Diagonal.ExternalSew DiagonalTallyCellReports Inherited
open ParseBatch ParseBatchVerifier Prewire VPVNP VPVNP.ParseGrammar
open BorderVNP.Cube.Physical.NativeAssignments
open scoped Classical
variable {R r t pins link inner n g : ℕ} {Edge : Type} [Fintype Edge]
    {G : Wiring R r t pins link inner n Edge} {d : Fin n} {D q depth : ℕ}
    {order : Fin (Fintype.card (Fin q → Deck (depth+2))) ≃ (Fin q → Deck (depth+2))} {state : Fin g}
    (W : WiredWitness G d D q depth order state)
    (position : (Fin q → Deck (depth+2)) → {v : EuclideanSpace ℝ (Fin D) // ‖v‖ ≤ 1})
    {N leaves : ℕ} (origin : Fin N ≃ Fin leaves × (Fin q → Deck (depth+2)))
    (code : GrammarLabel (Fin n × Bool) (Fin g) n ↪ ℕ)
    {s m p qe qa : ℕ} (sites : (W.routedFine position).Site ↪ Fin s) (edges : (W.routedFine position).Edge ↪ Fin m)
    (ports : (Fin r × Fin (publicWidth G)) ↪ Fin p) (channels : ((Fin q → Deck (depth+2)) × Direction q) ↪ Fin qe)
    (groups : Fin (GridHosts.tileCount q depth) ↪ Fin qa)
    {copies : ℕ} (slot base : Fin N → ℕ)

attribute [local instance] reportDeckEq
variable {l : ReportLayout} {C T w n₀ : ℕ} (rows : ReceivedRows (fun _ : Fin T => l) C)
    (tape : Fin T → ℕ → Bool) (start : Fin T → ℕ)
    (assigned : ((t : Fin T) × Fin (rows.cells t).length) → AssignedCell l)
    (same : ∀ j,(assigned j).report=(rows.cells j.1).get j.2) (passes : ∀ j,(assigned j).Passing w n₀)
    (returns : ∀ j, ∃ ret,(assigned j).Returns w n₀ (rows.reportedWithTape tape start (rows.order j)) ret)
    (home : Fin N → Fin C) (prior : Fin N → ℕ → Bool)
local notation3 (prettyPrint := false) "cores" => fun i => W.seedCoreBundle position code sites edges ports
  (origin i).2 (slot i) (base i) copies
local notation3 (prettyPrint := false) "payloads" => fun i => W.seedStored position code sites edges ports channels groups (origin i).2

include same passes returns in
/-- For any returned report tape, the complete chronological source list
used by the numbered operand theorem is the actual retained bundle array
read on those same private bits. It carries the original stable source ordinals. -/
theorem returned_seed_rows
    (inventory : ∀ j,(assigned j).bundles=(BundleDirectory.sourceRows home (rows.order j).val).map cores)
    (stored : ∀ j,(assigned j).report.bundles=(BundleDirectory.sourceRows home (rows.order j).val).map
      (W.retainedBundle (copies := copies) position origin code sites edges ports channels groups slot base prior))
    (c : Fin C) :
    (rows.reportedWithTape tape start c).bundles=(BundleDirectory.sourceRows home c.val).map
      (W.retainedBundle (copies := copies) position origin code sites edges ports channels groups slot base
        (rows.reportSourceBank assigned home)) :=
  rows.reportedWithTape_bundles tape start assigned same passes returns home cores payloads prior inventory stored c

end Packing.DeckGrid.WiredWitness

namespace Cube.Physical.NativeAssignments.ReceivedRows

open Crossing Packing.CellAddresses Packing.BottomReports Packing.Inherited CellSparse DiagonalTallyCellReports
open scoped Classical
variable {D C ns ne np n d blocks b h K s T : ℕ} {P Team : Type} [Fintype P]
    {bits : P → ℕ} {l : ReportLayout} (R : ReceivedRows (fun _ : Fin T => l) C)
    (N : Network D P bits) (cell : N.Site → Fin C)
    (siteID : N.Site ↪ Fin ns) (edgeID : N.Edge ↪ Fin ne) (portID : P ↪ Fin np)
    (state : Site.Programs N) (owners : (Packet n d blocks → Selector n K h) → Fin d → Team)
    (slot : LiveBit N cell ↪ Slot n d blocks (h*b)) (ports : Ports bits)
    (owner : Fin ns → ℕ) (bottom : Fin C → List Bundle)
    (q : Routed (b:=b) (s:=s) owners)
    (raw : (c : Fin C) → Fin (externalBase N cell c (placedSize N state)) → Bool)

local notation3 (prettyPrint := false) "key" => (fun v => (cell v).val)
local notation3 (prettyPrint := false) "progs" => (fun v => (state v).program)
local notation3 (prettyPrint := false) "size" => placedSize N state
local notation3 (prettyPrint := false) "guessed" c => privateWires N cell size c (raw c)
local notation3 (prettyPrint := false) "staged" c => privateStaging N cell size c (raw c)
local notation3 (prettyPrint := false) "supplied" c => pathSupply N cell edgeID portID owners slot ports q c
local notation3 (prettyPrint := false) "originalBank" c => bank N cell c size (guessed c) (staged c) (supplied c)


/-- The bank in which the reported seed uses are looked up is exactly the
received private staging, wire, and supplied endpoint vector of the seed's
current host cell on this same complete routed assignment. -/
theorem sourceBank_assignedAt {J : ℕ} (home : Fin J → Fin C) (j : Fin J) :
    R.reportSourceBank (fun i => R.assignedAt N cell siteID edgeID portID state owners slot ports owner bottom q raw i.1 i.2) home j =
      lookup (originalBank (home j)) := by
  let i := R.order.symm (home j)
  have read := R.assignedAt_pre N cell siteID edgeID portID state owners slot ports owner bottom q raw i.1 i.2
  have hc : R.order i=home j := R.order.apply_symm_apply _
  refine congrArg lookup (read.trans ?_)
  exact congrArg (fun c => originalBank c) hc

end Cube.Physical.NativeAssignments.ReceivedRows

end BorderVNP
end Computability
end OAI
