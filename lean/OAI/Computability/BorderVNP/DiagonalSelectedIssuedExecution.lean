import OAI.Computability.BorderVNP.DiagonalSelectedSignedTerms
import OAI.Computability.BorderVNP.DiagonalSelectedReportRows
import OAI.Computability.BorderVNP.DiagonalIssuedPinExecution
import OAI.Computability.BorderVNP.DiagonalIssuedProfileHeader
import OAI.Computability.BorderVNP.PackedHistorySeedExecution

/-! # The issued read of one selected signed residue column

The public profile, greedy selector declaration, original report bundles,
actual private guards, and (11.2) tally are fixed on the selected frozen
machine. The remaining inputs describe its reached startup, issued calls
and chronological finishing memories on the chosen live pin. -/

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
set_option maxHeartbeats 3500000
set_option maxRecDepth 7000
set_option synthInstance.maxSize 4000

variable {D m : ℕ} [NeZero D] {K F : Type} [Field K] [Field F] {e : PaidIdentity K D m} {S : SiteSchedule e}
    {R r pin link k d a rw ec s copies T header work : ℕ}
    (plan : SeedPlan S (k+1) r d T copies header work) (cube : FixedCube F) (φ : F →+* K)
    (ord : Fin (k+1) × Bool ≃ Fin (2*(k+1))) {qchar : ℕ}
    {common : CommonField e (φ ∘ cube.table) qchar k s ord} (chart : AdvisedBranch common)
    [Fact common.p.Prime] [Algebra (ZMod common.p) chart.E]
    (fit : 2*((UniversalMachine.programPrefix (cube.signedSiteProgram e)).length+(TeamContraction.cutWidth (k+1)+a))+
      R*link+Wires.innerWidth r 64 rw ec (rw+1) ≤ k+1)
local notation3 (prettyPrint := false) "pins" => (pairedTableParameters (k+1) s+2)*pin
local notation3 (prettyPrint := false) "scalarIDs" => e.Entry ⊕ TableEntry cube.pred cube.b cube.h cube.copies cube.width
local notation3 (prettyPrint := false) "code" => (ParseTable.numberedLabelEquiv ord k s).toEmbedding.trans Fin.valEmbedding
local notation3 (prettyPrint := false) "num" => (Fintype.equivFin (scalarIDs)).toEmbedding.trans Fin.valEmbedding
local notation3 (prettyPrint := false) "axes" => Fintype.card (Cube D)
local notation3 (prettyPrint := false) "tiles" => GridHosts.tileCount axes d
local notation3 (prettyPrint := false) "G₀" => tapeTemplate (R:=R) (r:=r) (link:=link) (regs:=64) (w:=rw) (e:=ec) (width:=rw+1) (k:=k) (a:=a) (cube.signedSiteProgram e) fit pins
variable {order : Fin (GridHosts.tileCount (Fintype.card (Cube D)) d) ≃ (Fin (Fintype.card (Cube D)) → Deck (d+2))}
    (W : WiredWitness (tapeTemplate (R:=R) (r:=r) (link:=link) (regs:=64) (w:=rw) (e:=ec) (width:=rw+1) (k:=k) (a:=a) (cube.signedSiteProgram e) fit ((pairedTableParameters (k+1) s+2)*pin)) (Fin.last k) D (Fintype.card (Cube D)) d order
      (0 : ParseTable.State (Fin (k+1) × Bool) s))
    (position : (Fin (Fintype.card (Cube D)) → Deck (d+2)) → {v : EuclideanSpace ℝ (Fin D) // ‖v‖ ≤ 1})
    {ns ne np : ℕ}
    (sites : (W.routedFine position).Site ↪ Fin ns) (edges : (W.routedFine position).Edge ↪ Fin ne)
    (ports : Fin r × Fin (publicWidth (tapeTemplate (R:=R) (r:=r) (link:=link) (regs:=64) (w:=rw) (e:=ec) (width:=rw+1) (k:=k) (a:=a) (cube.signedSiteProgram e) fit ((pairedTableParameters (k+1) s+2)*pin))) ↪ Fin np)
    (table : (seedBundle (tapeTemplate (R:=R) (r:=r) (link:=link) (regs:=64) (w:=rw) (e:=ec) (width:=rw+1) (k:=k) (a:=a) (cube.signedSiteProgram e) fit ((pairedTableParameters (k+1) s+2)*pin)) (Fintype.card (Cube D)) d order position copies).Tables K)
local notation3 (prettyPrint := false) "M" => plan.compiled.machine
local notation3 (prettyPrint := false) "mass" => initialMass (D:=D) (k+1) r d copies header
local notation3 (prettyPrint := false) "goodState" => Boundary.Good (S := S) (start := d+1) (P := Fin tiles)
  (bits := fun _ => copies*GridHosts.inputBlockWidth r (k+1) axes d)
  (shape := boundary S (d+1)) (w := 60*logWidth r (k+1)) (boundaryBudget S mass)
variable (words : Boundary.Pins S (d+1) (boundary S (d+1)) (60*logWidth r (k+1)) 0 → Bool)
    (good : Boundary.Good (boundaryBudget S (initialMass (D:=D) (k+1) r d copies header)) 0 (Boundary.seedState S (tapeTemplate (R:=R) (r:=r) (link:=link) (regs:=64) (w:=rw) (e:=ec) (width:=rw+1) (k:=k) (a:=a) (cube.signedSiteProgram e) fit ((pairedTableParameters (k+1) s+2)*pin)) d order position copies table words))
    (seeds : ∀ h, ∀ i : Fin S.rounds,
      ((Cube D → Deck (S.level (offset S (d+1) h) (i.val+1)+1)) × (S.source.pattern i).bins.Bin) → ℕ)
    (free : Fin (R+1) → Fin r → Fin a → Bool) (count : (fan S)^T*copies = R+1)
local notation3 (prettyPrint := false) "leaf" => (Subtype.mk (Boundary.seedState S G₀ d order position copies table words) good : Admissible goodState 0)
local notation3 (prettyPrint := false) "G₁" => SewnTape.wiring (regs:=64) (w:=rw) (ec:=ec) (width:=rw+1) (cube.signedSiteProgram e) fit free pins
local notation3 (prettyPrint := false) "Y" => chart.gadgets ∘ Sum.inl
local notation3 (prettyPrint := false) "Hist" => (packHistory (Pack := Admissible goodState) (K := fan S) leaf (M).epoch T).Index
variable (hp : (fieldSewParams (SewnTape.wiring (regs:=64) (w:=rw) (ec:=ec) (width:=rw+1) (cube.signedSiteProgram e) fit free ((pairedTableParameters (k+1) s+2)*pin)) (Fintype.card (Cube D)) d).Valid)
    (α ξ : ℝ) (calibrated : plan.SignedLabelRows count link (cube.pred+1) α ξ)
    (lit : (UniversalMachine.programPrefix (cube.signedSiteProgram e)).length+(TeamContraction.cutWidth (k+1)+a) = literal α (k+1))
    (hd : 0 < BorderVNP.Cube.alphabet α (k+1)) {cells : ℕ}
    (number : (Cube D → Deck (depth S (d+1) T+1)) ≃ Fin cells)


open RoutingISA RoutingISA.Evaluator RoutingISA.CellDispatch TeamContraction.ProcessorSlots
open TeamContraction.JointHeader DiagonalTallyCellReports CellMacro.Generator VPVNP.BurstRAM VPVNP.VerifierNetwork

local notation3 (prettyPrint := false) "physical" => cube.signedSiteProgram e
local notation3 (prettyPrint := false) "Raw" => Fin ((pairedTableParameters (k+1) s+2)*pin) → Bool
local notation3 (prettyPrint := false) "tallyDim" => pairedTableParameters (k+1) s+Fintype.card (scalarIDs)
variable (parameters : SignedTaskArena.Parameters) (arenaBase profileBits : ℕ)
    (frame origin : Fin (R+1) → ℕ)
    {σ : Type} [Fintype σ] (input : σ → Bool)
    (initial : ((plan.execute (tapeTemplate (R:=R) (r:=r) (link:=link) (regs:=64) (w:=rw) (e:=ec) (width:=rw+1) (k:=k) (a:=a) (cube.signedSiteProgram e) fit ((pairedTableParameters (k+1) s+2)*pin)) order position σ).choose).eval input = words)
    (widths : ℕ → ℕ) (slots : ∀ i, EnrichedOuter.Machine.Guess S (d+1) (fun _ _ => 60*logWidth r (k+1)) i ≃ Fin (widths i))
    (fits : broadcastWidth (fan S) widths T ≤ profileBits)
local notation3 (prettyPrint := false) "gap" => parameters.privateGap
local notation3 (prettyPrint := false) "geom" => (plan.execute G₀ order position σ).choose
local notation3 (prettyPrint := false) "profile" => (M).nativeCode leaf geom input initial widths slots fits
local notation3 (prettyPrint := false) "banks" => canonicalBank (G:=G₁) hp.block (GridHosts.gridRoom G₁ Fintype.card_pos)
local notation3 (prettyPrint := false) "packets" => plan.signedPackets count G₀ order position W code sites edges ports table
  words good cube α ξ calibrated lit hd hp number gap
local notation3 (prettyPrint := false) "compileDir" => plan.signedCoreDirectory physical fit W position code sites edges ports table
  words good seeds free count (Sum.inl : e.Entry → scalarIDs) num hp
local notation3 (prettyPrint := false) "B" => fun h : Hist => compileDir h cube α ξ calibrated lit hd number gap
local notation3 (prettyPrint := false) "networks" => EnrichedTape.network («pins» := pins) physical fit position free count M leaf rfl
local notation3 (prettyPrint := false) "blockCount" => BorderVNP.Cube.Physical.blocksFor ((R+1)*exterior ξ r (k+1) : ℕ)
  (cube.h*cube.b) ((BorderVNP.Cube.alphabet α (k+1))^(cube.pred+1))
local notation3 (prettyPrint := false) "receipt" => plan.signedReceivedRows physical fit W position code sites edges ports table
  words good seeds free count (Sum.inl : e.Entry → scalarIDs) num hp
local notation3 (prettyPrint := false) "rows" => fun (_ : Raw) (h : Hist) (v : ((B) h).Route cube.width) => receipt h cube α ξ calibrated lit hd number
  parameters arenaBase profileBits frame origin (Subtype.val v)
local notation3 (prettyPrint := false) "teamOf" => fun (h : Hist) (v : ((B) h).Route cube.width) (c : Fin (((B) h).cells)) =>
  ((B) h).owners v.val.1 ((packets h).label c (BorderVNP.Cube.Physical.chosen cube.b cube.width v.val.1))
local notation3 (prettyPrint := false) "original" => fun h : Hist => plan.signedCellBundles physical fit W position code sites edges ports table
  words good seeds free count (Sum.inl : e.Entry → scalarIDs) num hp h cube α ξ calibrated lit hd number parameters arenaBase profileBits
/-- The report layout at a physically selected collection of received rows. -/
private abbrev receivedLayout {t c : ℕ} {L : Fin t → ReportLayout} (_ : ReceivedRows L c) := L

local notation3 (prettyPrint := false) "Terms" => plan.selectedSignedTerms cube φ ord chart physical fit W position sites edges ports table words good
  free count hp α ξ calibrated lit hd number gap
local notation3 (prettyPrint := false) "assigned" => plan.selectedSignedAssigned cube φ ord chart physical fit W position sites edges ports table words good
  free count hp α ξ calibrated lit hd number gap
local notation3 (prettyPrint := false) "decode" => plan.selectedSignedDecode cube φ ord chart physical fit W position sites edges ports table words good
  seeds free count hp α ξ calibrated lit hd number gap

variable {mult : ℕ} (reader : ChosenReader chart (R+1) r mult rw rw pin)
    (pub : Fin (R+1) → Arg → Word rw) (reg : Fin (R+1) → Bank rw) (args : Fin (R+1) → UnitAddresses)
    (limit burst : ℕ) (privateSize : TeamScales.width (k+1) (1/2) ≤ burst)
    (j : Index (Fin (Module.finrank (ZMod common.p) chart.E)) (Fin (pairedTableParameters (k+1) s)) (chart.pinRadius (R+1) r))

/-- Execution of the single installed private-sparse program on a chosen
live reader pin, from its real positive-start and private-call receipts.
All path and tally types are those of the selected numbered expansion. -/
noncomputable def selectedIssuedExecution :=
  letI (i : Raw) (h : Hist) : Fintype (Terms i h) :=
    plan.selectedSignedTermFinite cube φ ord chart physical fit W position sites edges ports table words good
      free count hp α ξ calibrated lit hd number gap i h
  reader.executionOfIssuedCells
    (P := FreeBlock R tiles) («Hist» := Hist) (N := networks)
    (bits := fun _ : FreeBlock R tiles => GridHosts.inputBlockWidth r (k+1) axes d)
    (blocks := fun _ => blockCount) (Term := Terms) (exp := Nat.clog 2 (r*(2*k+1)+1))
    (width := rw) (reserve := profileBits)
    (cap := BorderVNP.Cube.Physical.declarationCap cube.pred (BorderVNP.Cube.alphabet α (k+1)) blockCount cube.b cube.h cube.width)
    (cube.cubeID e) G₁ pub reg args limit burst privateSize
    (B) banks (fun h => ((B) h).owner) original (fun i h v => receivedLayout (rows i h v)) rows teamOf
    (fun _ h v u a => plan.signedReceivedRows_owner physical fit W position code sites edges ports table words good seeds
      free count (Sum.inl : e.Entry → scalarIDs) num hp h cube α ξ calibrated lit hd number parameters arenaBase profileBits
      frame origin v.val u a) (fun h => ((B) h).owner_site)
    (fun h => plan.signedCore_wellFormed physical fit W position code sites edges ports table words good seeds free count
      (Sum.inl : e.Entry → scalarIDs) num hp h cube α ξ calibrated lit hd number gap)
    decode assigned (fun _ h v => ((B) h).issuedHeader (dim:=tallyDim) (digits:=rw) (profile h).val v) j

end PackedHistoryCircuit.Normalized.SelectedSchedule.SeedPlan

end BorderVNP
end Computability
end OAI
