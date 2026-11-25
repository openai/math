import OAI.Computability.BorderVNP.DiagonalCompiledSeedPathUse
import OAI.Computability.BorderVNP.DiagonalNumberedSeedReports

/-! # All copied parameter observations on one frozen numbered history -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace PackedHistoryCircuit.Normalized.SelectedSchedule

open Crossing Cover Shortening Shortening.Adaptive BorderVNP.Epoch BorderVNP.Epoch.Round
open Packing Packing.Inherited Packing.DeckGrid Diagonal Diagonal.ExternalSew Diagonal.CellEntries
open TeamContraction GridHosts ParseBatch ParseBatchVerifier Prewire VPVNP Site.Lineage
open Diagonal.ExternalSew.RowTrace EnrichedOuter EnrichedOuter.Boundary BorderVNP.Cube BorderVNP.Cube.Physical
open scoped Classical BorderVNP.Epoch.Cube
attribute [local instance] portFintype
set_option synthInstance.maxSize 4000
set_option maxHeartbeats 2600000
set_option maxRecDepth 7000

variable {D m : ℕ} [NeZero D] {K E Gadget : Type} [Field K] [Field E] {e : PaidIdentity K D m}
    {S : SiteSchedule e} {R r pins link k d a regs rw ec width s copies T w : ℕ}
    (p : UniversalMachine.Program)
    (fit : 2*((UniversalMachine.programPrefix p).length+(TeamContraction.cutWidth (k+1)+a))+
      R*link+Wires.innerWidth r regs rw ec width ≤ k+1)
local notation "axes" => Fintype.card (Cube D)
local notation "tiles" => tileCount (Fintype.card (Cube D)) d
local notation "G₀" => tapeTemplate p fit pins
variable {order : Fin (tileCount (Fintype.card (Cube D)) d) ≃ (Fin (Fintype.card (Cube D)) → Deck (d+2))}
    (W : WiredWitness (tapeTemplate p fit pins) (Fin.last k) D (Fintype.card (Cube D)) d order
      (0 : ParseTable.State (Fin (k+1) × Bool) s))
    (position : (Fin (Fintype.card (Cube D)) → Deck (d+2)) → {v : EuclideanSpace ℝ (Fin D) // ‖v‖ ≤ 1})
    (code : PairedParameters k s ↪ ℕ) {ns ne np : ℕ}
    (siteID : (W.routedFine position).Site ↪ Fin ns) (edgeID : (W.routedFine position).Edge ↪ Fin ne)
    (portID : (Fin r × Fin (publicWidth (tapeTemplate p fit pins))) ↪ Fin np)
    (table : (seedBundle (tapeTemplate p fit pins) (Fintype.card (Cube D)) d order position copies).Tables K)
    {budget : ℕ → ℕ} {cap : ℕ → ℕ → ℕ} {deep : S.floor+1+S.drop*T ≤ d+1}
    (C : Compiled (fun _ : Fin (tileCount (Fintype.card (Cube D)) d) => copies*inputBlockWidth r (k+1) (Fintype.card (Cube D)) d) deep budget cap w)
    (words : Pins S (d+1) (boundary S (d+1)) w 0 → Bool)
    (good : Good budget 0 (seedState S (tapeTemplate p fit pins) d order position copies table words))
    (seeds : ∀ h, ∀ i : Fin S.rounds,
      ((Cube D → Deck (S.level (offset S (d+1) h) (i.val+1)+1)) × (S.source.pattern i).bins.Bin) → ℕ)
    (number : e.Entry → ℕ)
    (free : Fin (R+1) → Fin r → Fin a → Bool) (count : (fan S)^T*copies = R+1)
    (y : e.Entry → E) (hy : ∀ f : MvPolynomial e.Entry ℤ, MvPolynomial.eval₂Hom (Int.castRingHom K) e.entry f = 0 →
      MvPolynomial.eval₂Hom (Int.castRingHom E) y f = 0) (pos : e.Entry → Gadget)
local notation3 (prettyPrint := false) "ok₀" => EnrichedOuter.Boundary.Good (S := S) (start := d+1) (P := Fin tiles)
  (bits := fun _ => copies*inputBlockWidth r (k+1) axes d) (shape := boundary S (d+1)) (w := w) budget
local notation "leaf₀" => seedMember (G := G₀) (order := order) (copies := copies) (budget := budget) S position table words good
local notation "group₀" => Equiv.toEmbedding (Equiv.refl (Fin (tileCount (Fintype.card (Cube D)) d)))
local notation "chan₀" => Shortening.PublicCapacity.Rows.edge (groupedGridRows G₀ axes d order position copies)
local notation "grid₀" => seedBundle G₀ axes d order position copies
local notation "prog₀" => wiredSeedStatePrograms S W position code siteID edgeID portID copies table words
local notation "key₀" => Equiv.toEmbedding (finCongr (seedPortCount (D := D) d))
local notation "dir₀" => C.privateSiteRows key₀ seeds
local notation "port₀" => privatePorts S key₀
local notation "G₁" => SewnTape.wiring p fit free pins
local notation "src₀" => EnrichedTape.base (Gadget := Gadget) p fit W position leaf₀ rfl
variable (hp : (fieldSewParams (SewnTape.wiring p fit free pins) (Fintype.card (Cube D)) d).Valid)
    (q : (packHistory (Subtype.mk (seedState S (tapeTemplate p fit pins) d order position copies table words) good) C.machine.epoch T).Index) (z : Fin ((fan S)^T) → Fin copies → W.Hidden position)
local notation3 (prettyPrint := false) "state₀" => ((packHistory (Pack := Admissible ok₀) (K := fan S) leaf₀ C.machine.epoch T).term q).val
local notation "last₀" => C.machine.terminalPrivatePrograms dir₀ number leaf₀ prog₀ q
local notation "net₀" => EnrichedTape.network p fit position free count C.machine leaf₀ rfl q
local notation "prog₁" => enrichedSewnPrograms G₁ axes d order position count C.machine leaf₀ rfl
  (Flat.portRows T (port₀ T)) hp q last₀
/-- Use the row-major nested team enumeration of the terminal tagged replay. -/
noncomputable local instance frozenNumberedPowerTeams {j : ℕ} : Fintype (Port (fan S) (Fin copies × Unit) j) :=
  Replay.batchFinite (fan S) (Fin copies × Unit) j

local notation "terminal₀" => EnrichedOuterReplay.terminal C.machine y hy pos leaf₀ src₀ q z
local notation3 (prettyPrint := false) "edges₁" => FieldExport.mergedEdges (fieldSewParams G₁ axes d) hp (state₀).rows.edge
local notation "ports₁" => finProdFinEquiv.toEmbedding

variable {cn cd blocks cb ch ck cs cells : ℕ} {cell : (EnrichedTape.network p fit position free count C.machine (seedMember (G := tapeTemplate p fit pins) (order := order) (copies := copies) (budget := budget) S position table words good) rfl q).Site → Fin cells}
    (slot : LiveBit (EnrichedTape.network p fit position free count C.machine (seedMember (G := tapeTemplate p fit pins) (order := order) (copies := copies) (budget := budget) S position table words good) rfl q) cell ↪ BorderVNP.Cube.Physical.Slot cn cd blocks (ch*cb))
    (path : Physical.Path (EnrichedTape.network p fit position free count C.machine (seedMember (G := tapeTemplate p fit pins) (order := order) (copies := copies) (budget := budget) S position table words good) rfl q) cell cn cd blocks cb ch ck cs)
    (bank : Ports (fun _ : FreeBlock R (tileCount (Fintype.card (Cube D)) d) => inputBlockWidth r (k+1) (Fintype.card (Cube D)) d))


open EnrichedTape DiagonalTallyCellReports
attribute [local instance] WiredWitness.reportDeckEq

/-- The actual report record at each original retained host certifies all
parameter-place observations of the numbered ledger on this same path. -/
theorem Compiled.frozenNumberedSeedObserved {l : ReportLayout} (param : PairedParameters k s ≃ Fin l.parameters)
    {N : ℕ} (origin : Fin N ≃ Fin ((fan S)^T) × (Fin axes → Deck (d+2))) (boxSlot offset : Fin N → ℕ)
    (physical : Fin N → ℕ → Bool)
    (received : ∀ j,C.sourceRecordAt p fit W position (param.toEmbedding.trans Fin.valEmbedding) siteID edgeID portID
      table words good seeds number free count hp q z slot path bank origin boxSlot offset physical l j
      ((enrichedOuterHosts C.machine leaf₀ q).site ⟨(origin j).1,(origin j).2⟩)) :
    EnrichedTape.SeedReportObserved (l := l) p fit W position free count C.machine leaf₀ rfl y hy pos hp.block q z
      slot path bank origin param siteID edgeID portID chan₀ group₀ boxSlot offset physical := by
  intro j h i
  let code := param.toEmbedding.trans Fin.valEmbedding
  have passed := C.passingSeedAt_of_source p fit W position code siteID edgeID portID table words good seeds number
    free count y hy pos hp q z slot path bank origin boxSlot offset physical j (received j) h i
  exact C.wiredSeed_sourceObserved p fit W position code siteID edgeID portID table words good seeds number
    free count y hy pos hp q z slot path bank origin boxSlot offset physical j h i passed

end PackedHistoryCircuit.Normalized.SelectedSchedule

end BorderVNP
end Computability
end OAI
