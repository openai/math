import OAI.Computability.BorderVNP.DiagonalSelectedReportRows
import OAI.Computability.BorderVNP.DiagonalRoutedCoreReadback
import OAI.Computability.BorderVNP.DiagonalOriginalRegisteredSourceCut

/-! # The original scanner and argument cut on the admitted supported route -/

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
local notation3 (prettyPrint := false) "recv(" h "," v ")" => plan.signedReceivedRows (R := R) (r := r) (pins := pins) (link := link) (k := k) (d := d) (a := a) (regs := regs) (rw := rw) (ec := ec) (width := width) (s := s) (copies := copies) (T := T) (header := header) (work := work) p fit W position code
  sites edges ports table words good seeds free count pos num hp h cube α ξ calibrated lit hd number parameters
  arenaBase profileBits physicalFrames (fun _ : Fin (R+1) => outputBase) v
local notation3 (prettyPrint := false) "routes" => fun h : Hist => (core(h)).Route cube.width
local notation3 (prettyPrint := false) "proposals" => fun (_ : Fin pins → Bool) (h : Hist) (v : (core(h)).Route cube.width) =>
  (u : Fin (R+1)) → ReportAssignments ((recv(h,v.val)).cells u)

variable {clockWidth tallyWidth : ℕ} (pub : Fin (R+1) → Arg → Word clockWidth)
    (reg : Fin (R+1) → Bank clockWidth) (args : Fin (R+1) → UnitAddresses) (readerPin : Fin pins → Bool)
    (layout : WireLayout (R+1) r link) (fixed : Block (R+1)) (hw : 0<clockWidth)
    (agreeWidth : ∀ u, (args u).header = layout.header) (base : Fin (R+1) → ℕ)
local notation3 (prettyPrint := false) "claims" => Fin ((R+1)*(parameters.parameters+parameters.report.gadgets)*tallyWidth) → Bool

/-- The common selected arena used by the report and startup indices. -/
private noncomputable abbrev reportArena := arena

/-- The history index of this installed epoch plan. -/
private noncomputable abbrev reportHist := Hist

variable (hdr : layout.header=JointHeader.PositiveFields.width profileBits cube.pred (BorderVNP.Cube.alphabet α (k+1))
      (declarationCap cube.pred (BorderVNP.Cube.alphabet α (k+1))
        (blocksFor (((R+1)*exterior ξ r (k+1)) : ℕ) (cube.h*cube.b) ((BorderVNP.Cube.alphabet α (k+1))^(cube.pred+1)))
        cube.b cube.h cube.width) (R+1) (parameters.parameters+parameters.report.gadgets) tallyWidth)
    (room : ∀ u, ((SewnTape.wiring p fit free pins).transferFrame u (args u).header (args u).dst).Fits clockWidth (base u))
    (enc : (reportHist (pins:=pins) (order:=order) plan p fit position table words good) ↪ (Fin profileBits → Bool))
    (B₀ : (z : {ext // PositiveExterior (SewnTape.wiring p fit free pins) args readerPin clockWidth ext}) → (u : Fin (R+1)) →
      BootedPinStart SparseExterior.driver (SewnTape.wiring p fit free pins) pub reg args readerPin z.val u)
local notation3 (prettyPrint := false) "U" => fun z u => (B₀ z u).start
local notation3 (prettyPrint := false) "ib" => fun u => (args u).ibase
local notation3 (prettyPrint := false) "hb" => fun u => (args u).hbase
local notation3 (prettyPrint := false) "sb" => fun u => (args u).starbase
local notation3 (prettyPrint := false) "rawPins" => Fin pins → Bool

variable (allowed : (Fin pins → Bool) → (reportHist (pins:=pins) (order:=order) plan p fit position table words good) →
      (Fin ((R+1)*(parameters.parameters+parameters.report.gadgets)*tallyWidth) → Bool) → RawBroadcast
      (reportArena (S:=S) (R:=R) (r:=r) (link:=link) (k:=k) (d:=d) (a:=a) (T:=T) (header:=header) (cells:=cells)
        p cube α ξ arenaBase profileBits) → Prop)
    (template : (Fin pins → Bool) → (reportHist (pins:=pins) (order:=order) plan p fit position table words good) →
      (Fin ((R+1)*(parameters.parameters+parameters.report.gadgets)*tallyWidth) → Bool) → DiagonalTallyPacketEmit.Frame)
    (entries : (Fin pins → Bool) → (reportHist (pins:=pins) (order:=order) plan p fit position table words good) →
      (Fin ((R+1)*(parameters.parameters+parameters.report.gadgets)*tallyWidth) → Bool) → ℕ)
    (frames :
      let ar := reportArena (S:=S) (R:=R) (r:=r) (link:=link) (k:=k) (d:=d) (a:=a) (T:=T) (header:=header) (cells:=cells)
        p cube α ξ arenaBase profileBits
      ∀ i h c, AdmittedPinnedFrames (SewnTape.wiring p fit free pins) args readerPin layout fixed hw agreeWidth base room ar hdr
        (fun z u => (B₀ z u).start) (fun u => (args u).ibase) (fun u => (args u).hbase) (fun u => (args u).starbase)
      (fun _ _ => rfl) (cube.cubeID e)
        (plan.signedCoreDirectory (R:=R) (r:=r) (pins:=pins) (link:=link)
          (k:=k) (d:=d) (a:=a) (regs:=regs) (rw:=rw) (ec:=ec) (width:=width) (s:=s) (copies:=copies)
          (T:=T) (header:=header) (work:=work) p fit W position code sites edges ports table
          words good seeds free count pos num hp h cube α ξ calibrated lit hd number parameters.privateGap).owners
        (plan.signedReportSources (R:=R) (r:=r) (pins:=pins) (link:=link)
          (k:=k) (d:=d) (a:=a) (regs:=regs) (rw:=rw) (ec:=ec) (width:=width) (s:=s) (copies:=copies)
          (T:=T) (header:=header) (work:=work) p fit W position code sites edges ports table
          words good seeds free count pos num hp h cube α ξ calibrated lit hd number parameters
          arenaBase profileBits physicalFrames (fun _ : Fin (R+1) => outputBase)) i (enc h) c (allowed i h c)
        (template i h c) (entries i h c))
    (checked : ∀ i h c v, ParsedPreCall (SewnTape.wiring p fit free pins) args readerPin layout fixed hw agreeWidth base room hdr
        (fun z u => (B₀ z u).start) (fun u => (args u).ibase) (fun u => (args u).hbase) (fun u => (args u).starbase)
      (fun _ _ => rfl) (cube.cubeID e) i ⟨enc h,v,c⟩ → LocalRow.declarationInRange v ∧ allowed i h c v)
    (honest :
      let ar := reportArena (S:=S) (R:=R) (r:=r) (link:=link) (k:=k) (d:=d) (a:=a) (T:=T) (header:=header) (cells:=cells)
        p cube α ξ arenaBase profileBits
      ∀ i h c,
        let owners := (plan.signedCoreDirectory (R:=R) (r:=r) (pins:=pins) (link:=link)
          (k:=k) (d:=d) (a:=a) (regs:=regs) (rw:=rw) (ec:=ec) (width:=width) (s:=s) (copies:=copies)
          (T:=T) (header:=header) (work:=work) p fit W position code sites edges ports table
          words good seeds free count pos num hp h cube α ξ calibrated lit hd number parameters.privateGap).owners
        ∀ v : Routed (b:=cube.b) (s:=cube.width) owners, allowed i h c (routeBroadcast ar owners v).val)
    (decoder : BootedPinStart.PreparedHistoryDecoder SparseExterior.driver (cube.cubeID e) (SewnTape.wiring p fit free pins) pub reg readerPin layout
      hdr enc args fixed hw agreeWidth base room B₀)
local notation3 (prettyPrint := false) "registered" =>
  BootedPinStart.admittedReportRoutes SparseExterior.driver G₁ pub reg readerPin layout args fixed hw
    agreeWidth base room arena (cube.cubeID e) hdr enc B₀ (fun hist => (core(hist)).owners) (fun hist => rsrc(hist))
    allowed template entries frames checked honest

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
local notation3 (prettyPrint := false) "restore" => (decoder.supported limit burst privateRoom next routes proposals registered).val

local notation3 (prettyPrint := false) "chartAt(" fr ")" => reportLayout (task).before (task).after fr
  (RoutingOutputs.controlsBase outputBase (arena).cables cells (deliveries).entries ((R+1)*tiles))
  parameters.parameters parameters.siteWidth parameters.bodyCap (arena).stop
local notation3 (prettyPrint := false) "chartsAt(" fs ")" => fun (u : Fin (R+1)) => chartAt(fs u)
local notation3 (prettyPrint := false) "receipts(" h "," v "," fs ")" => rowsAt(fs,h,(v).val)
variable (alignment : physicalFrames = fun _ => frameBase)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
/-- The admitted decoder preserves the actual report cut of every team on its
chosen input. The proposal is first transported to the common allocation and
then read at that same team's physical header word. -/
noncomputable def signedAdmittedCutAtOriginalFrame (i : rawPins) (h : Hist) (v : (core(h)).Route cube.width) (cc : claims)
    (src : proposals i h v) (u : Fin (R+1)) :=
  let found := BootedPinStart.PreparedHistoryDecoder.admitted_reportCut SparseExterior.driver G₁ pub reg readerPin
    layout args fixed hw agreeWidth base room arena (cube.cubeID e) hdr enc B₀
    (fun hist => (core(hist)).owners) (fun hist => rsrc(hist)) allowed template entries frames checked honest decoder
    limit burst privateRoom next i h v cc src u
  PLift.up <| BootedPinStart.jointReportCutAt.frameObservation (u:=u) (shape:=fun fs => chartsAt(fs))
    (fun fs => receipts(h,v,fs)) alignment rfl (congrArg (fun fr => chartAt(fr)) (congrFun alignment u).symm)
    src found

end PackedHistoryCircuit.Normalized.SelectedSchedule.SeedPlan

end BorderVNP
end Computability
end OAI
