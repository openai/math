import OAI.Computability.BorderVNP.PackedFrozenSeedInputs
import OAI.Computability.BorderVNP.DiagonalSewnTape
import OAI.Computability.BorderVNP.DiagonalEnrichedSiteWiring

/-! # The installed original grid on the concrete native tape wiring -/

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

/-- All public seed words select exactly the grouped grid at the original tape wiring. -/
theorem frozen_leaf_installed :
    (plan.frozenLeaf G order position W tag sites edges ports table x).val.pack.layout =
      (wiredGrid G axes d order position).groupedRepeat
        (fun _ : Fin tiles => GridHosts.inputBlockWidth r n axes d) order copies := rfl

end PackedHistoryCircuit.Normalized.SelectedSchedule.SeedPlan


namespace Diagonal.CellEntries.SewnTape

open Crossing Cover Packing Packing.DeckGrid Diagonal.ExternalSew GridHosts TeamContraction
open VPVNP ParseBatch ParseBatchVerifier Prewire
open scoped Classical

variable {D R r pins link k d a regs rw ec width copies : ℕ}
    (p : UniversalMachine.Program)
    (fit : 2*((UniversalMachine.programPrefix p).length+(TeamContraction.cutWidth (k+1)+a))+
      R*link+Wires.innerWidth r regs rw ec width ≤ k+1)
    {axes : ℕ} (order : Fin (GridHosts.tileCount axes d) ≃ (Fin axes → Deck (d+2)))
    (position : (Fin axes → Deck (d+2)) → {v : EuclideanSpace ℝ (Fin D) // ‖v‖ ≤ 1})

/-- Installing the actual literal leaves the original grouped grid on exactly the
same slots, for every filled assignment in the chosen native processor program. -/
theorem template_grid_installed (free : Fin (R+1) → Fin r → Fin a → Bool) :
    (wiredGrid (tapeTemplate p fit pins) axes d order position).groupedRepeat
      (fun _ : Fin (GridHosts.tileCount axes d) => GridHosts.inputBlockWidth r (k+1) axes d) order copies =
    (wiredGrid (wiring p fit free pins) axes d order position).groupedRepeat
      (fun _ : Fin (GridHosts.tileCount axes d) => GridHosts.inputBlockWidth r (k+1) axes d) order copies := rfl

open TeamContraction.ProcessorSlots

/-- Directly at the real RAM wiring, including the interpreter prefix, startup
addresses and pin-dependent payload, the installed original layout is the zero seed's grid. -/
theorem native_grid_installed {pc op routines tail : ℕ} (physical : UniversalMachine.Program)
    (P : TeamOpcode.Program pc regs op routines) (data : SiteData R r regs op rw tail)
    (fits : fitsWith physical regs op r rw tail R link (k+1) ec) :
    (wiredGrid (tapeTemplate (regs:=regs) (w:=rw) (e:=ec) (width:=rw+1)
      (a:=setupWidth (rw+1) (k+1)+(prefixCapacity r op regs rw (k+1)+1+tail)) physical fits pins)
      axes d order position).groupedRepeat
      (fun _ : Fin (GridHosts.tileCount axes d) => GridHosts.inputBlockWidth r (k+1) axes d) order copies =
    (wiredGrid (wiringWith physical P data pins link (k+1) ec fits) axes d order position).groupedRepeat
      (fun _ : Fin (GridHosts.tileCount axes d) => GridHosts.inputBlockWidth r (k+1) axes d) order copies := by
  rw [wiringWith_enriched]
  exact template_grid_installed physical fits order position (data.enrichedFree physical P (k+1) ec link)

end Diagonal.CellEntries.SewnTape

end BorderVNP
end Computability
end OAI
