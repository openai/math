import OAI.Computability.BorderVNP.DiagonalSelectedReportRows
import OAI.Computability.BorderVNP.DiagonalRoutedCoreReadback
import OAI.Computability.BorderVNP.DiagonalJointBootedSupport
import OAI.Computability.BorderVNP.DiagonalOriginalPrefixRuns

/-! # The original physical source run at its restored positive start -/

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
    {R r pins link k d a regs rw ec width s copies T header work : ℕ}
    (plan : SeedPlan S (k+1) r d T copies header work)
    (p : UniversalMachine.Program)
    (fit : 2*((UniversalMachine.programPrefix p).length+(TeamContraction.cutWidth (k+1)+a))+
      R*link+Wires.innerWidth r regs rw ec width ≤ k+1)
local notation3 (prettyPrint := false) "axes" => Fintype.card (Cube D)
local notation3 (prettyPrint := false) "tiles" => GridHosts.tileCount (Fintype.card (Cube D)) d
local notation3 (prettyPrint := false) "G₀" => tapeTemplate p fit pins
variable {order : Fin (GridHosts.tileCount (Fintype.card (Cube D)) d) ≃ (Fin (Fintype.card (Cube D)) → Deck (d+2))}
    (W : WiredWitness (tapeTemplate p fit pins) (Fin.last k) D (Fintype.card (Cube D)) d order
      (0 : ParseTable.State (Fin (k+1) × Bool) s))
    (position : (Fin (Fintype.card (Cube D)) → Deck (d+2)) → {v : EuclideanSpace ℝ (Fin D) // ‖v‖ ≤ 1})
    (code : PairedParameters k s ↪ ℕ) {ns ne np : ℕ}
    (sites : (W.routedFine position).Site ↪ Fin ns) (edges : (W.routedFine position).Edge ↪ Fin ne)
    (ports : Fin r × Fin (publicWidth (tapeTemplate p fit pins)) ↪ Fin np)
    (table : (seedBundle (tapeTemplate p fit pins) (Fintype.card (Cube D)) d order position copies).Tables K)
local notation3 (prettyPrint := false) "mass" => initialMass (D:=D) (k+1) r d copies header
local notation3 (prettyPrint := false) "budget" => boundaryBudget S mass
local notation3 (prettyPrint := false) "word₀" => 60*logWidth r (k+1)
local notation3 (prettyPrint := false) "seedBlock" => GridHosts.inputBlockWidth r (k+1) axes d
local notation3 (prettyPrint := false) "seedCap" => seedBoxCapacity (k+1) r axes d (Fintype.card (Direction axes))
local notation3 (prettyPrint := false) "desc" => seedDescriptionWidth (k+1) r axes d (header*logWidth r (k+1)) (BottomGridBank.bodyBudget seedCap)

variable (words : Boundary.Pins S (d+1) (boundary S (d+1)) (60*logWidth r (k+1)) 0 → Bool)
    (good : Boundary.Good (boundaryBudget S (initialMass (D:=D) (k+1) r d copies header)) 0 (Boundary.seedState S (tapeTemplate p fit pins) d order position copies table words))
    (seeds : ∀ h, ∀ i : Fin S.rounds,
      ((Cube D → Deck (S.level (offset S (d+1) h) (i.val+1)+1)) × (S.source.pattern i).bins.Bin) → ℕ)
    (free : Fin (R+1) → Fin r → Fin a → Bool) (count : (fan S)^T*copies = R+1)
    (pos : e.Entry → Gadget) (num : Gadget ↪ ℕ)
local notation3 (prettyPrint := false) "goodState" => Boundary.Good (S := S) (start := d+1) (P := Fin tiles)
  (bits := fun _ => copies*GridHosts.inputBlockWidth r (k+1) axes d)
  (shape := boundary S (d+1)) (w := word₀) budget
local notation3 (prettyPrint := false) "leaf" => (Subtype.mk (Boundary.seedState S G₀ d order position copies table words) good : Admissible goodState 0)
local notation3 (prettyPrint := false) "G₁" => SewnTape.wiring p fit free pins
variable (hp : (fieldSewParams (SewnTape.wiring p fit free pins) (Fintype.card (Cube D)) d).Valid)
open BorderVNP.Cube (TableEntry)
open BorderVNP.Cube.Physical Packing.CellAddresses Packing.BottomReports
open BorderVNP.Packing.RoutingOutputs.NativeDemands
open RoutingISA RoutingISA.Evaluator RoutingISA.Evaluator.SignedPrep
open DiagonalTallyAllocation DiagonalTallyCellReports ReportDirectory

variable {F : Type} [Field F] (cube : FixedCube F) (α ξ : ℝ)
    (calibrated : plan.SignedLabelRows count link (cube.pred+1) α ξ)
    (lit : (UniversalMachine.programPrefix p).length+(TeamContraction.cutWidth (k+1)+a) = literal α (k+1))
    (hd : 0 < BorderVNP.Cube.alphabet α (k+1)) {cells : ℕ}
    (number : (Cube D → Deck (depth S (d+1) T+1)) ≃ Fin cells)

variable (parameters : RoutingISA.SignedTaskArena.Parameters)
local notation3 (prettyPrint := false) "gap" => parameters.privateGap
local notation3 (prettyPrint := false) "deliveries" => freeDirectory R r ((UniversalMachine.programPrefix p).length+(TeamContraction.cutWidth (k+1)+a))
  link tiles seedBlock ((fan S)^T*tiles) desc
variable (arenaBase profileBits : ℕ)
local notation3 (prettyPrint := false) "arena" =>
  (CubeArena.selectedSizes arenaBase (BorderVNP.Cube.alphabet α (k+1)) ((R+1)*exterior ξ r (k+1))
    cells ((boundary S (d+1) T).edges+4*((R+1)*CoverScale.sites (Cube D) (d+1))) (deliveries).candidates
    (R+1) r (k+1) profileBits).selected cube.pred cube.b cube.h cube.copies cube.width
local notation3 (prettyPrint := false) "task" => (SignedTaskArena.Layout.mk arena (cube.cubeID e) parameters)
variable (frameBase outputBase : ℕ) (physicalFrames : Fin (R+1) → ℕ)
local notation3 (prettyPrint := false) "charts" => fun u : Fin (R+1) =>
  reportLayout (task).before (task).after (physicalFrames u)
    (RoutingOutputs.controlsBase ((fun _ : Fin (R+1) => outputBase) u) (arena).cables cells (deliveries).entries ((R+1)*tiles))
    parameters.parameters parameters.siteWidth parameters.bodyCap (arena).stop

open VPVNP.BurstRAM TeamContraction.ProcessorSlots Routing CellMacro.Generator RoutingISA.CompactMachine
local notation3 (prettyPrint := false) "Hist" => (packHistory leaf plan.compiled.machine.epoch T).Index
local notation3 (prettyPrint := false) "core(" h ")" => plan.signedCoreDirectory (R := R) (r := r) (pins := pins) (link := link) (k := k) (d := d) (a := a) (regs := regs) (rw := rw) (ec := ec) (width := width) (s := s) (copies := copies) (T := T) (header := header) (work := work) p fit W position code
  sites edges ports table words good seeds free count pos num hp h cube α ξ calibrated lit hd number gap
local notation3 (prettyPrint := false) "rsrc(" h ")" => plan.signedReportSources (R := R) (r := r) (pins := pins) (link := link) (k := k) (d := d) (a := a) (regs := regs) (rw := rw) (ec := ec) (width := width) (s := s) (copies := copies) (T := T) (header := header) (work := work) p fit W position code
  sites edges ports table words good seeds free count pos num hp h cube α ξ calibrated lit hd number parameters
  arenaBase profileBits physicalFrames (fun _ : Fin (R+1) => outputBase)
local notation3 (prettyPrint := false) "rowsAt(" fs "," h "," v ")" => plan.signedReceivedRows (R := R) (r := r) (pins := pins) (link := link) (k := k) (d := d) (a := a) (regs := regs) (rw := rw) (ec := ec) (width := width) (s := s) (copies := copies) (T := T) (header := header) (work := work) p fit W position code
  sites edges ports table words good seeds free count pos num hp h cube α ξ calibrated lit hd number parameters
  arenaBase profileBits (fs) (fun _ : Fin (R+1) => outputBase) v
variable {clockWidth tallyWidth : ℕ} (pub : Fin (R+1) → Arg → Word clockWidth)
    (reg : Fin (R+1) → Bank clockWidth) (args : Fin (R+1) → UnitAddresses) (readerPin : Fin pins → Bool)
local notation3 (prettyPrint := false) "claims" => Fin ((R+1)*(parameters.parameters+parameters.report.gadgets)*tallyWidth) → Bool

variable (B₀ : (z : {ext // PositiveExterior (SewnTape.wiring p fit free pins) args readerPin clockWidth ext}) → (u : Fin (R+1)) →
      BootedPinStart SparseExterior.driver (SewnTape.wiring p fit free pins) pub reg args readerPin z.val u)
open _root_.OAI.Computability.BorderVNP.Cube.Physical.NativeLedger _root_.OAI.Computability.BorderVNP.Cube.Physical
open TeamContraction.ProcessorSlots.BootedPinStart

variable (limit burst : ℕ) (privateRoom : TeamScales.width (k+1) (1/2) ≤ burst)
    (next : ∀ (z : {ext // PositiveExterior (SewnTape.wiring p fit free pins) args readerPin clockWidth ext ∧
        PinStart.preCallSupport (fun x team => (B₀ x team).start) (cube.cubeID e) ext})
      (u : Fin (R+1)), let node := B₀ ⟨z.val,z.property.1⟩ u
      PositiveContinuation (cube.cubeID e) SparseExterior.driver (k+1) (pub u)
        (TeamSiteEvents.macros (w:=clockWidth) (siteLibrary SparseExterior.driver) (nativeClock (k+1)))
        node.start.bank node.memory node.pins node.used limit)
local notation3 (prettyPrint := false) "teams" => BootedPinStart.supportedTeam (cube.cubeID e) B₀ limit burst privateRoom next
local notation3 (prettyPrint := false) "control" =>
  RoutingOutputs.controlsBase outputBase (arena).cables cells (deliveries).entries ((R+1)*tiles)
variable (gid : _root_.OAI.Computability.BorderVNP.Cube.TableEntry cube.pred cube.b cube.h cube.copies cube.width → Fin parameters.report.gadgets)
    {reserve groups cap : ℕ} (headerData : JointHeader.PositiveFields reserve cube.pred groups cap (R+1)
      (parameters.parameters+parameters.report.gadgets) tallyWidth) (startup : Fin (R+1) → StartupArena)
variable (alignment : physicalFrames = fun _ => frameBase)

set_option maxRecDepth 12000
set_option maxHeartbeats 2600000
/-- The genuine source run for a positive team start with its original
source reports at the constant selected layout. -/
noncomputable def originalAtRestoredFrames (h : Hist) (v : (core(h)).Route cube.width × (core(h)).Bank)
    (src : (rsrc(h)).actual v.1.val) (cc : claims) (start : JointBeforeCells teams) (u : Fin (R+1)) : Prop :=
  let nativeReports := plan.signedReportAssignments p fit W position code sites edges ports table words good seeds
    free count pos num hp h cube α ξ calibrated lit hd number parameters arenaBase profileBits physicalFrames
    (fun _ => outputBase) v.1.val
  let path := rawPath _ (core(h)).cell (core(h)).edgeID (core(h)).programs (core(h)).owners v.1.val v.2
  let tape := cast (congrArg (fun fs => (j : Fin (R+1)) →
    ReportAssignments ((rowsAt(fs,h,v.1.val)).cells j)) alignment) (nativeReports src)
  OriginalPrefixRun task headerData gid ((core(h)).owners v.1.val.1) path frameBase control
    parameters.siteWidth parameters.bodyCap startup (rowsAt((fun _ : Fin (R+1) => frameBase),h,v.1.val))
    u (teams start.1 u) (start.2 u) tape cc

end PackedHistoryCircuit.Normalized.SelectedSchedule.SeedPlan

end BorderVNP
end Computability
end OAI
