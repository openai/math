import OAI.Computability.BorderVNP.DiagonalCompiledGuardedHistory
import OAI.Computability.BorderVNP.DiagonalExternalFreeCanonical
import OAI.Computability.BorderVNP.DiagonalEnrichedRealization

/-! # Equation (11.2) on the same chart-specific terms decoded by the signed processor -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace PackedHistoryCircuit.Normalized.SelectedSchedule.SeedPlan

open Crossing Cover BorderVNP.Epoch BorderVNP.Epoch.Round Shortening Shortening.Adaptive Shortening.PublicCapacity
open Packing Packing.Inherited Packing.DeckGrid Packing.PhysicalEpochs Diagonal Diagonal.CellEntries
open Diagonal.ExternalSew TeamContraction ParseBatch ParseBatchVerifier Prewire VPVNP VPVNP.ParseGrammar
open EnrichedOuter TeamScales BorderVNP.Cube.Physical.NativeAssignments BorderVNP.Cube
open Branch ResidueBox ResidueIndex ResiduePins
open scoped Classical BigOperators BorderVNP.Epoch.Cube
attribute [local instance] portFintype
set_option maxHeartbeats 2400000
set_option maxRecDepth 7000
set_option synthInstance.maxSize 4000

variable {D m : ℕ} [NeZero D] {K F : Type} [Field K] [Field F] {e : PaidIdentity K D m} {S : SiteSchedule e}
    {R r pin link k d a regs rw ec width s copies T header work : ℕ}
    (plan : SeedPlan S (k+1) r d T copies header work) (cube : FixedCube F) (φ : F →+* K)
    (ord : Fin (k+1) × Bool ≃ Fin (2*(k+1))) {qchar : ℕ}
    {common : CommonField e (φ ∘ cube.table) qchar k s ord} (chart : AdvisedBranch common)
    (p : UniversalMachine.Program)
    (fit : 2*((UniversalMachine.programPrefix p).length+(TeamContraction.cutWidth (k+1)+a))+
      R*link+Wires.innerWidth r regs rw ec width ≤ k+1)
local notation3 (prettyPrint := false) "pins" => (pairedTableParameters (k+1) s+2)*pin
local notation3 (prettyPrint := false) "scalarIDs" => e.Entry ⊕ TableEntry cube.pred cube.b cube.h cube.copies cube.width
local notation3 (prettyPrint := false) "code" => (ParseTable.numberedLabelEquiv ord k s).toEmbedding.trans Fin.valEmbedding
local notation3 (prettyPrint := false) "num" => (Fintype.equivFin (scalarIDs)).toEmbedding.trans Fin.valEmbedding
local notation3 (prettyPrint := false) "axes" => Fintype.card (Cube D)
local notation3 (prettyPrint := false) "tiles" => GridHosts.tileCount axes d
local notation3 (prettyPrint := false) "G₀" => tapeTemplate p fit pins
variable {order : Fin (GridHosts.tileCount (Fintype.card (Cube D)) d) ≃ (Fin (Fintype.card (Cube D)) → Deck (d+2))}
    (W : WiredWitness (tapeTemplate p fit ((pairedTableParameters (k+1) s+2)*pin)) (Fin.last k) D (Fintype.card (Cube D)) d order
      (0 : ParseTable.State (Fin (k+1) × Bool) s))
    (position : (Fin (Fintype.card (Cube D)) → Deck (d+2)) → {v : EuclideanSpace ℝ (Fin D) // ‖v‖ ≤ 1})
    {ns ne np : ℕ}
    (sites : (W.routedFine position).Site ↪ Fin ns) (edges : (W.routedFine position).Edge ↪ Fin ne)
    (ports : Fin r × Fin (publicWidth (tapeTemplate p fit ((pairedTableParameters (k+1) s+2)*pin))) ↪ Fin np)
    (table : (seedBundle (tapeTemplate p fit ((pairedTableParameters (k+1) s+2)*pin)) (Fintype.card (Cube D)) d order position copies).Tables K)
local notation3 (prettyPrint := false) "M" => plan.compiled.machine
local notation3 (prettyPrint := false) "mass" => initialMass (D:=D) (k+1) r d copies header
local notation3 (prettyPrint := false) "goodState" => Boundary.Good (S := S) (start := d+1) (P := Fin tiles)
  (bits := fun _ => copies*GridHosts.inputBlockWidth r (k+1) axes d)
  (shape := boundary S (d+1)) (w := 60*logWidth r (k+1)) (boundaryBudget S mass)
variable (words : Boundary.Pins S (d+1) (boundary S (d+1)) (60*logWidth r (k+1)) 0 → Bool)
    (good : Boundary.Good (boundaryBudget S (initialMass (D:=D) (k+1) r d copies header)) 0 (Boundary.seedState S (tapeTemplate p fit ((pairedTableParameters (k+1) s+2)*pin)) d order position copies table words))
    (seeds : ∀ h, ∀ i : Fin S.rounds,
      ((Cube D → Deck (S.level (offset S (d+1) h) (i.val+1)+1)) × (S.source.pattern i).bins.Bin) → ℕ)
    (free : Fin (R+1) → Fin r → Fin a → Bool) (count : (fan S)^T*copies = R+1)
local notation3 (prettyPrint := false) "leaf" => (Subtype.mk (Boundary.seedState S G₀ d order position copies table words) good : Admissible goodState 0)
local notation3 (prettyPrint := false) "G₁" => SewnTape.wiring p fit free pins
local notation3 (prettyPrint := false) "Y" => chart.gadgets ∘ Sum.inl
local notation3 (prettyPrint := false) "Hist" => (packHistory (Pack := Admissible goodState) (K := fan S) leaf (M).epoch T).Index
variable (hp : (fieldSewParams (SewnTape.wiring p fit free ((pairedTableParameters (k+1) s+2)*pin)) (Fintype.card (Cube D)) d).Valid)
    (α ξ : ℝ) (calibrated : plan.SignedLabelRows count link (cube.pred+1) α ξ)
    (lit : (UniversalMachine.programPrefix p).length+(TeamContraction.cutWidth (k+1)+a) = literal α (k+1))
    (hd : 0 < BorderVNP.Cube.alphabet α (k+1)) {cells : ℕ}
    (number : (Cube D → Deck (depth S (d+1) T+1)) ≃ Fin cells) (gap : ℕ)

/-- The source indexes a tuple of independent original copies under each outer history. -/
noncomputable local instance selectedBatchFinite {fan copies T : ℕ} : Fintype (Port fan (Fin copies × Unit) T) :=
  Replay.batchFinite fan (Fin copies × Unit) T

local notation3 (prettyPrint := false) "packets" => plan.signedPackets count G₀ order position W code sites edges ports table
  words good cube α ξ calibrated lit hd hp number gap
local notation3 (prettyPrint := false) "banks" => canonicalBank (G := G₁) hp.block (GridHosts.gridRoom G₁ Fintype.card_pos)
local notation3 (prettyPrint := false) "tags" => EnrichedTape.tags (Gadget := scalarIDs) p fit W position free count M leaf rfl
  Y chart.preserves_paid Sum.inl hp.block
local notation3 (prettyPrint := false) "dir" => signedCoreDirectory plan p fit W position code sites edges ports table words
  good seeds free count Sum.inl num hp
local notation3 (prettyPrint := false) "rawWidth" => Fin ((pairedTableParameters (k+1) s+2)*pin) → Bool
local notation3 (prettyPrint := false) "put" => (Sum.inr : TableEntry cube.pred cube.b cube.h cube.copies cube.width → scalarIDs)

/-- A single term in the selected row and history. Its original witnesses,
public packet, substituted free lanes and table-entry coordinates are those
of the one compiler installation used by the physical evaluator. -/
noncomputable abbrev selectedSignedTerms (raw : Fin ((pairedTableParameters (k+1) s+2)*pin) → Bool) (q : Hist) : Type :=
  Σ z : Fin ((fan S)^T) → Fin copies → W.Hidden position, (packets q).Passing (tags q z) (banks raw) put

local notation3 (prettyPrint := false) "Term" => selectedSignedTerms plan cube φ ord chart p fit W position sites edges ports table
  words good free count hp α ξ calibrated lit hd number gap

/-- Each selected history has a genuine finite set of passing assignments on its actual packet. -/
@[instance_reducible] noncomputable def selectedSignedTermFinite (raw : Fin ((pairedTableParameters (k+1) s+2)*pin) → Bool) (q : Hist) :
    Fintype (Term raw q) := by
  letI (z : Fin ((fan S)^T) → Fin copies → W.Hidden position) :
      Fintype ((packets q).Passing (tags q z) (banks raw) put) := (packets q).passingFintype (tags q z) (banks raw) put
  unfold selectedSignedTerms
  infer_instance

/-- Decode on the selected chart with the canonical raw substitution and the
same integer coordinate for each paid or cube scalar, including a zero entry. -/
noncomputable def selectedSignedDecode (raw : Fin ((pairedTableParameters (k+1) s+2)*pin) → Bool) (q : Hist) :
    let B := dir q cube α ξ calibrated lit hd number gap
    {v : B.Route cube.width × B.Bank // B.Guard (banks raw) v} ≃ Term raw q :=
  signedPinnedPaths plan p fit W position code sites edges ports table words good seeds free count Y chart.preserves_paid
    Sum.inl num hp q cube α ξ calibrated lit hd number gap put (banks raw)

/-- The tally is the original numbered coefficient in the row expansion,
including every selected scalar occurrence and every parameter power. -/
noncomputable def selectedSignedAssigned (raw : Fin ((pairedTableParameters (k+1) s+2)*pin) → Bool)
    (path : Σ q : Hist, Term raw q) :=
  EnrichedTape.assigned (Gadget := scalarIDs) p fit W position free count M leaf rfl Y chart.preserves_paid
    Sum.inl hp.block packets put banks ord raw path

end PackedHistoryCircuit.Normalized.SelectedSchedule.SeedPlan

end BorderVNP
end Computability
end OAI
