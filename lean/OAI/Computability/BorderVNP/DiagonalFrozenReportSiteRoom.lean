import OAI.Computability.BorderVNP.DiagonalFrozenSignedModels
import OAI.Computability.BorderVNP.PackedSeedLiteralReportRoom
import OAI.Computability.BorderVNP.PackedFrozenBundleShape

/-! # Absolute word range for the original report on a selected signed terminal -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace PackedHistoryCircuit.Normalized.SelectedSchedule.SeedPlan

open Crossing Cover BorderVNP.Epoch BorderVNP.Epoch.Round Shortening Shortening.Adaptive Shortening.PublicCapacity
open Packing Packing.Inherited Packing.DeckGrid Packing.PhysicalEpochs Diagonal Diagonal.CellEntries
open Diagonal.ExternalSew Diagonal.ExternalSew.RowTrace TeamContraction ParseBatch ParseBatchVerifier Prewire VPVNP
open VPVNP.ParseGrammar EnrichedOuter TeamScales BorderVNP.Cube.Physical.NativeAssignments
open scoped Classical BigOperators BorderVNP.Epoch.Cube
attribute [local instance] portFintype
set_option maxHeartbeats 3200000
set_option maxRecDepth 7200
set_option synthInstance.maxSize 4000

variable {D m : ℕ} [NeZero D] {K E Gadget : Type} [Field K] [Field E] {e : PaidIdentity K D m} {S : SiteSchedule e}
    {R r pins link k d a regs rw ec width s copies T w : ℕ}
    (p : UniversalMachine.Program)
    (fit : 2*((UniversalMachine.programPrefix p).length+(TeamContraction.cutWidth (k+1)+a))+
      R*link+Wires.innerWidth r regs rw ec width ≤ k+1)
local notation "axes" => Fintype.card (Cube D)
local notation "tiles" => GridHosts.tileCount (Fintype.card (Cube D)) d
local notation "G₀" => tapeTemplate p fit pins
variable {order : Fin (GridHosts.tileCount (Fintype.card (Cube D)) d) ≃ (Fin (Fintype.card (Cube D)) → Deck (d+2))}
    (W : WiredWitness (tapeTemplate p fit pins) (Fin.last k) D (Fintype.card (Cube D)) d order
      (0 : ParseTable.State (Fin (k+1) × Bool) s))
    (position : (Fin (Fintype.card (Cube D)) → Deck (d+2)) → {v : EuclideanSpace ℝ (Fin D) // ‖v‖ ≤ 1})
    (code : PairedParameters k s ↪ ℕ) {ns ne np : ℕ}
    (sites : (W.routedFine position).Site ↪ Fin ns) (edges : (W.routedFine position).Edge ↪ Fin ne)
    (ports : Fin r × Fin (publicWidth (tapeTemplate p fit pins)) ↪ Fin np)
    (table : (seedBundle (tapeTemplate p fit pins) (Fintype.card (Cube D)) d order position copies).Tables K)
    {budget : ℕ → ℕ} {cap : ℕ → ℕ → ℕ} {deep : S.floor+1+S.drop*T ≤ d+1}
    (C : Compiled (fun _ : Fin (GridHosts.tileCount (Fintype.card (Cube D)) d) =>
      copies*GridHosts.inputBlockWidth r (k+1) (Fintype.card (Cube D)) d) deep budget cap w)
    (words : Boundary.Pins S (d+1) (boundary S (d+1)) w 0 → Bool)
    (good : Boundary.Good budget 0 (Boundary.seedState S (tapeTemplate p fit pins) d order position copies table words))
    (seeds : ∀ h, ∀ i : Fin S.rounds,
      ((Cube D → Deck (S.level (offset S (d+1) h) (i.val+1)+1)) × (S.source.pattern i).bins.Bin) → ℕ)
    (free : Fin (R+1) → Fin r → Fin a → Bool) (count : (fan S)^T*copies = R+1)
    (y : e.Entry → E) (hy : ∀ f : MvPolynomial e.Entry ℤ, MvPolynomial.eval₂Hom (Int.castRingHom K) e.entry f = 0 →
      MvPolynomial.eval₂Hom (Int.castRingHom E) y f = 0)
    (pos : e.Entry → Gadget) (num : Gadget ↪ ℕ)
local notation "goodState" => Boundary.Good (S := S) (start := d+1) (P := Fin tiles)
  (bits := fun _ => copies*GridHosts.inputBlockWidth r (k+1) axes d)
  (shape := boundary S (d+1)) (w := w) budget
local notation "leaf" => (Subtype.mk (Boundary.seedState S G₀ d order position copies table words) good : Admissible goodState 0)
local notation "baseProg" => Boundary.wiredSeedStatePrograms S W position code sites edges ports copies table words
local notation "source" => EnrichedTape.base (Gadget := Gadget) p fit W position leaf rfl
local notation "key" => Equiv.toEmbedding (finCongr (seedPortCount (D:=D) d))
local notation "M" => C.machine
local notation "rows" => C.privateSiteRows key seeds
local notation "oldPorts" => privatePorts S key
local notation "G₁" => SewnTape.wiring p fit free pins
variable (hp : (fieldSewParams (SewnTape.wiring p fit free pins) (Fintype.card (Cube D)) d).Valid)
    (q : (packHistory (Subtype.mk (Boundary.seedState S (tapeTemplate p fit pins) d order position copies table words) good)
      C.machine.epoch T).Index)
local notation3 (prettyPrint := false) "lastState" => ((packHistory (Pack := Admissible goodState) (K := fan S) leaf (M).epoch T).term q).val
local notation3 (prettyPrint := false) "net" => EnrichedTape.network p fit position free count M leaf rfl q
local notation3 (prettyPrint := false) "host" => ((Equiv.sigmaEquivProd (Fin ((fan S)^T)) (Fin axes → Deck (d+2))).symm.toEmbedding.trans
  (enrichedOuterHosts M leaf q).site)
local notation3 (prettyPrint := false) "lastProgs" => C.machine.terminalPrivatePrograms rows (num ∘ pos) leaf baseProg q
local notation3 (prettyPrint := false) "programs" => enrichedSewnPrograms G₁ axes d order position count M leaf rfl (Flat.portRows T (oldPorts T))
  hp q lastProgs
local notation3 (prettyPrint := false) "slabs" => fun j : Fin ((fan S)^T) × (Fin axes → Deck (d+2)) => W.seedSlab position code sites edges ports j.2
local notation3 (prettyPrint := false) "hidden" => W.bottomChoicesEquiv position edges slabs (fun _ => rfl)

open CellAddresses BottomReports DiagonalTallyCellReports

local notation "innerCap₀" => seedBoxCapacity (k+1) r axes d (Fintype.card (Direction axes))
local notation "bodyCap₀" => BottomGridBank.bodyBudget innerCap₀
local notation "groups₀" => Equiv.toEmbedding (Equiv.refl (Fin tiles))
local notation3 (prettyPrint := false) "chan₀" => (groupedGridRows G₀ axes d order position copies).edge
local notation3 (prettyPrint := false) "sizes" => fun v : (net).Site => (programs v).program.size

set_option maxHeartbeats 2400000 in
/-- At the actual terminal host the private report fits even after translation
to its final word address. The one-copy slab is paid by this host's real
retained program, and the physical site allocation pays its absolute end. -/
theorem frozenSigned_reportSiteRoom {cells hw factor : ℕ} (cell : (net).Site → Fin cells)
    (addressFit : ∀ c, guessedSize net cell c+siteSize net cell c sizes+suppliedSize net cell c < 2^hw)
    (copyPos : 0<copies) (rep : (k+1+s+2)^24 ≤ r) (headerFactor : 8 ≤ factor) (small : innerCap₀ ≤ k+1)
    (bounded : ∀ z, code z < Fintype.card (PairedParameters k s))
    (j : Fin ((fan S)^T*tiles)) (slot : ℕ) (bank : ℕ → Bool) (layout : ReportLayout)
    (headerWidth : layout.fieldWidth=factor*logWidth r (k+1)) (bodyWidth : layout.bodyCap=bodyCap₀) :
    let idx := finProdFinEquiv.symm j
    let c := order idx.2
    let v := host (idx.1,c)
    let base := siteBase net cell (cell v) (lastState).rows.site sizes ⟨v,rfl⟩
    (W.seedUseBundle position code sites edges ports chan₀ groups₀ c slot base copies bank).SiteRoom layout hw
      (seedDescriptionWidth (k+1) r axes d (factor*logWidth r (k+1)) bodyCap₀) := by
  intro idx c v base
  let b := W.seedUseBundle position code sites edges ports chan₀ groups₀ c slot base copies bank
  have hr : 1 ≤ r := (Nat.one_le_pow 24 _ (by omega)).trans rep
  have hcard := seed_states_le (k+1) s r rep
  have hg : Fintype.card (Fin (k+1) × Bool)+s+1 ≤ r := by
    simpa only [ParseTable.State,Fintype.card_fin] using hcard
  refine W.seedLiteralReport_siteRoom position code sites edges ports copies j b layout hr hg headerFactor small
    bounded headerWidth bodyWidth rfl rfl le_rfl rfl ?_
  have hw₀ := frozenSigned_birthWidth p fit W position code sites edges ports table C words good seeds free count
    pos num hp q (idx.1,c)
  let slab := W.seedSlab position code sites edges ports c
  have bankSize : copies*slab.stride ≤ sizes v := by
    change copies*slab.stride ≤ (programs v).program.size
    exact hw₀.ge.trans ((programs v).retention.work_le.trans (Nat.le_add_right _ _))
  have span : slab.stride ≤ sizes v := (Nat.le_mul_of_pos_left _ copyPos).trans bankSize
  have endAddr := siteBase_fits net cell (cell v) (lastState).rows.site sizes ⟨v,rfl⟩
  have limit := addressFit (cell v)
  change base+slab.stride < 2^hw
  exact ((Nat.add_le_add_left span base).trans endAddr).trans_lt ((Nat.le_add_right _ _).trans_lt limit)

end PackedHistoryCircuit.Normalized.SelectedSchedule.SeedPlan

end BorderVNP
end Computability
end OAI
