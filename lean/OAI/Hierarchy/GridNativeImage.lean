import OAI.Hierarchy.GridNativeImageLayout
import OAI.Hierarchy.GridNativeController
import OAI.Hierarchy.GridEvaluatorBudget

namespace OAI
/-! # The single controller image installed in the diagonal evaluator -/

noncomputable section
set_option quotPrecheck false
namespace Hierarchy.GridNativeImage
open ThreeFlat Diagonal PhysicalStage NavigationPass NavigationDirectory
open RAM RAM.NavigationNodeRows RAM.PhysicalProcedure Computability.VPVNP.BurstRAM PrivateRAM
open TraceDistribution TraceAdmission TraceNodeHeaders NodePublication GridRegisteredSetting
open UniversalGrid GridThrough
open scoped Classical Fin.CommRing

variable {F : Type} [Field F] [Fintype F] {w pc regs slots S base fuel axes : ℕ}
variable (D : RunData F (64*w) pc regs slots S base fuel axes (w/2))

variable (l : Layout)
local notation "m" => l.dimension
local notation "n" => l.sideMinusOne
local notation "bank" => l.bank
local notation "q" => l.copies
local notation "d" => l.pinWidth
local notation "W" => (64*w)
local notation "J" => (GridDescription.sector w)
local notation "full" => (2^(axes+1) : ℕ)
local notation "span" => (2^(w/2) : ℕ)
local notation "rails" => (GridControllerSimGeometry.railCount m n bank)
local notation "depth" => ((axes+1)+w/2)
local notation "G" => (TraceStaticRow.gateTable D.field D.fit.width D.fit.labels base fuel D.state regs slots depth)
local notation "off" => (1+(depth+depth))
local notation "P" => (D.block.repeat D.passes)
local notation "rem" => (axes+1-(P).charge)
local notation "ss" => ((P).directory rem (axes+1))
local notation "edges" => ((P).finalEdges rem (axes+1))
local notation "desc" => (TraceSourceOwner.shape W pc regs slots S fuel depth (G).internal)
local notation "num" => (directoryCap D.block)
local notation "region" => (GridCompilerAdmission.arena w)

def parameterCount := GridStructuralHeader.wordCount
  (GridStructuralHeader.directory (w:=w) D.block (axes+1) D.passes l.selectorCap).length (TraceReceiverTemplate.count G) (HistoryStageBody.Physical.libraryWords D.block (64*w))

def archive := TraceSeedWriter.archive D.block w (axes+1) off (G).cells l.selectorCap (rails*2+w^2+bank*w^2)
local notation "arc" => (archive D l)
local notation "last" => (TraceRecovery.lastLayer (arc).K ss (arc).cursor (arc).seedLayer)

def node :=
  let trace:=TraceBitHeader.seedTraceWork (w/2) (desc).stride (G).cells D.block.cursorCopies depth
  traceArchive w full span ((S+1)/2) trace (D.issuedUnit w l.degree l.stageRate l.rootRate) num num num

def resources := Resources.gridRows w full (last).count (m+1) span (GridIdleLayout.each m n bank)
  S (node D l).banks.charges (last).first

def simulated : Procedure W :=
  let guardProgram:=GridPhysicalAdmission.program D.block arc ss edges W D.passes
  let publish:=Resources.registerNodes W (compactControl w) ((arc).control+64) (traceLimit w)
    (arc).cursor.header (ss).length (14*J) (node D l) (arc).seedLayer (resources D l)
  let wire:=GridRegisteredPublication.procedure w m n bank q d (parameterCount D l) (l.selectorCap+1)
    l.receiverText S (last).count (ss).length full span l.logRadix l.receiverPC
  guardProgram.seq (publish.seq wire)

def dispatch : Procedure W :=
  let shape:=GridControllerIdle.shape m n bank l.logRadix q d l.receiverPC
  GridSelectorSwitch.program ((12*J:ℕ):Word W)
    (GridControllerIdle.guarded W region shape l.selectorCap) (simulated D l)

def limit (F : Type) [Fintype F] (l : Layout) :=
  let railCount := GridControllerSimGeometry.railCount l.dimension l.sideMinusOne l.bank
  GridPaddedCellImage.limit railCount ((l.sideMinusOne+1)^(l.dimension+1)) l.bank
    (Ordered.hiddenCount railCount l.sideMinusOne) (Ordered.edgeCount railCount l.sideMinusOne) (Fintype.card F)

def emitter : Procedure W := GridCompilerAdmission.emit (dispatch D l) bank n (m+1) (q*d) rails
  (limit F l) (Fintype.card F) ((FieldCode.ofCardLe D.field).encode 0) ((FieldCode.ofCardLe D.field).encode 1)

def machine (X : Catalyst.Approximation F (m+1) (q*d)) := GridNativeEvaluator.machine (emitter D l)
  (12*J) (l.selectorCap+1) (GridNativeEvaluator.parameters (e:=rails) («n»:=n) X D.field)

def navigationTime :=
  let shape:=GridControllerIdle.shape m n bank l.logRadix q d l.receiverPC
  4+max (GridControllerIdle.guardedCost W region shape l.selectorCap)
    (GridEvaluatorBudget.sim w m n q bank d rails l.selectorCap (parameterCount D l) l.receiverText S
      (last).count (ss).length full (2*span) l.logRadix l.receiverPC arc ss edges region)

def emissionTime := GridCompilerAdmission.clock w (m+1) n rails bank (limit F l) (navigationTime D l)

/-- The text is a function of the public shape and the chosen approximation.
Its instructions and numeric constants are identical before and after the
evaluator itself is installed in the padded machine. -/
def replace (M : Machine W pc regs slots) (fit : NativeTrace.Fits M S base depth fuel) :
    RunData F W pc regs slots S base fuel axes (w/2) := {D with machine:=M,fit:=fit}

theorem text_fixed (M : Machine W pc regs slots) (fit : NativeTrace.Fits M S base depth fuel)
    (X : Catalyst.Approximation F (m+1) (q*d)) :
    machine (replace D M fit) l X=machine D l X := rfl

theorem clock_fixed (M : Machine W pc regs slots) (fit : NativeTrace.Fits M S base depth fuel) :
    emissionTime (replace D M fit) l=emissionTime D l := rfl


end Hierarchy.GridNativeImage
end

end OAI
