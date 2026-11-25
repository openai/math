import OAI.Hierarchy.TraceReceiverRegistered
import OAI.Hierarchy.GridInstalledFit
import OAI.Hierarchy.TraceReceiverProgram
import OAI.Hierarchy.GridRegisteredOrder

namespace OAI
/-! # Canonical compact receiving directory and public terminal cardinality -/

noncomputable section
set_option quotPrecheck false
open scoped Fin.CommRing

namespace Hierarchy.GridReceiverDirectory
open ThreeFlat Diagonal PhysicalStage NavigationPass NavigationDirectory NodePublication
open RAM RAM.NavigationNodeRows Computability.VPVNP.BurstRAM PrivateRAM TraceDistribution TraceAdmission TraceNodeHeaders GridRegisteredSetting

variable {F : Type} [Field F] [Fintype F] {w pc rr pp size base fuel axes : ℕ}
variable (D : RunData F (64*w) pc rr pp size base fuel axes (w/2)) (l : GridNativeImage.Layout)
local notation "W" => (64*w)
local notation "depth" => ((axes+1)+w/2)
local notation "G" => TraceStaticRow.gateTable D.field D.fit.width D.fit.labels base fuel D.state rr pp depth
local notation "off" => (1+(depth+depth))
local notation "text" => SelfAdvice.textSize W pc pp
local notation "ed" => GridStructuralHeader.directory (w:=w) D.block (axes+1) D.passes l.selectorCap
local notation "cnt" => TraceReceiverTemplate.count G
local notation "phase" => GridStructuralHeader.receiverPhase w text (GridNativeImage.parameterCount D l)
local notation "V" => TraceAdmission.receiverAge w
local notation "P" => D.block.repeat D.passes
local notation "rem" => (axes+1-(P).charge)
local notation "ss" => (P).directory rem (axes+1)
local notation "J" => GridDescription.sector w
local notation "cap" => directoryCap D.block

/-- The final block of the actual compact tick header carries this second
directory. Its location depends only on the public sizes of the two earlier
blocks, and its phase is the real private tag cell. -/
def archive : NavigationPass.Archive :=
  TraceCompactSeed.archive D.block w (GridStructuralHeader.recipientBase w) (axes+1)
    off (G).cells l.selectorCap (2+text+W*(1+(ed).length+cnt)) phase

local notation "a" => archive D l
local notation "last" => TraceRecovery.lastLayer (a).K ss (a).cursor (a).seedLayer

def node : NodeArchive :=
  let desc:=TraceSourceOwner.shape W pc rr pp size fuel depth (G).internal
  let trace:=TraceBitHeader.seedTraceWork (w/2) desc.stride (G).cells D.block.cursorCopies depth
  receiverArchive V (2^(axes+1)) (2^(w/2)) ((size+1)/2) trace
    (D.issuedUnit w l.degree l.stageRate l.rootRate) cap cap cap

def parameters := Resources.gridRows w (2^(axes+1)) (last).count (l.dimension+1) (2^(w/2))
  (GridIdleLayout.each l.dimension l.sideMinusOne l.bank) size (node D l).banks.charges (last).first

/-- No history, flag, tick index or RAM memory is an argument of this public
directory on the installed evaluator image. -/
def native : TraceReceiverProgram.Directory where
  archive := a
  stages := ss
  edges := (P).finalEdges rem (axes+1)
  repetitions := D.passes
  nodeControl := TickWorkspace.base V 41
  registerHeader := (a).control+64
  registrationLimit := traceLimit w
  resourceBase := 14*J
  node := node D l
  seedLayer := (a).seedLayer
  parameters := parameters D l

theorem hardware_fields :
    (native D l).archive.K=D.block.alphabetCap ∧ (native D l).archive.initialDegree=2^(D.block.exponent 0) ∧
    (native D l).node.childCap=cap ∧ (native D l).node.halfCap=cap ∧ (native D l).node.motifCap=cap :=
  ⟨rfl,rfl,rfl,rfl,rfl⟩

theorem navigation_eq :
    TraceReceiverProgram.navigation D.block W (native D l) =
    (GridPhysicalAdmission.program D.block a ss ((P).finalEdges rem (axes+1)) W D.passes).seq
      (Resources.registerNodes W (TickWorkspace.base V 41) ((a).control+64) (traceLimit w) (a).cursor.header
        (ss).length (14*J) (node D l)
        ((a).cursorSeedSites D.block D.axesFit (w/2) off (G).cells rfl rfl).layer (parameters D l)) := rfl

/-- The literal S43/44 updater on T has exactly the same final number of
roots as its typed physical selection on E. -/
theorem roots (h : D.run.plan.History) : D.roots h=(parameters D l).roots := by
  change D.roots h=(last).count
  rw [GridRegisteredOrder.roots_fixed]
  symm
  apply GridRegisteredOrder.directory_count (P)
  have pass:=D.passesFit
  have lanes : (P).charge+rem=axes+1 := by
    rw [D.block.charge_repeat]
    omega
  rw [lanes]
  rfl

local notation "par" => parameters D l
local notation "units" => D.issuedUnit w l.degree l.stageRate l.rootRate

/-- On the receiver the numerical addresses of the charge table differ from
the sender's. Each registered cost word and every original-lane destination
is nevertheless the very same mathematical ordinal used by the sender. -/
theorem published (h : D.run.plan.History) (count : D.roots h=(par).roots)
    {addr : ℕ} {mem : Memory W} (receipt :
      let idx:=Resources.indexEquiv D.run h count
      Resources.Registered addr (14*J) par
        (fun j => idx (D.run.plan.destination h (GridPhysicalAdmission.initialLane (Nat.succ_pos axes) j)))
        (fun v => units*D.run.chargeAt h D.issuedCharges
          (TraceReceiverSeedWords.start D.machine D.fit D.field D.state D.block D.axesFit) (idx.symm v)) mem) :
    (∀ j,mem (addr+j.val)=((D.dest h j).val : Word W)) ∧
    ∀ i col,(mem (14*J+i.val*((l.dimension+1)+2)+col.val)).val=
      D.costs (GridNativeImage.resources D l) h l.dimension l.sideMinusOne l.bank D.issuedCharges units i col := by
  have rows:=GridRegisteredOrder.registered D par h D.issuedCharges units l.dimension l.sideMinusOne l.bank
    count receipt
  exact GridRegisteredOrder.reads D par h D.issuedCharges units l.dimension l.sideMinusOne l.bank rows

end Hierarchy.GridReceiverDirectory
end

end OAI
