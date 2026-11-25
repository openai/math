import OAI.Hierarchy.GridChosenReceiverPrefix

namespace OAI
/-! # One witnessed chronological path through registration and election -/

noncomputable section
namespace Hierarchy.TraceReceiverElectedJournal

open ThreeFlat Diagonal PhysicalStage NavigationPass NavigationDirectory
open RAM RAM.NavigationNodeRows RAM.PhysicalProcedure RAM.TickStageSpec Computability.VPVNP.BurstRAM PrivateRAM
open TraceDistribution TraceAdmission TraceNodeHeaders NodePublication GridRegisteredSetting GridPhysicalAdmission
open TraceFactorReceiver.Gather Filter GridReceiverDirectory
open scoped Classical Topology

open scoped Fin.CommRing
variable {F : Type} [Field F] [Fintype F] {w pc rr pp size base fuel axes : ℕ}
variable (D : RunData F (64*w) pc rr pp size base fuel axes (w/2)) (l : GridNativeImage.Layout)
set_option quotPrecheck false
local notation "W" => (64*w)
local notation "B" => D.block
local notation "a" => archive D l
local notation "dir" => native D l
local notation "depth" => ((axes+1)+w/2)
local notation "G" => TraceStaticRow.gateTable D.field D.fit.width D.fit.labels base fuel D.state rr pp depth
local notation "off" => (1+(depth+depth))
local notation "P" => (D.block.repeat D.passes)
local notation "rem" => (axes+1-(P).charge)
local notation "X" => D.block.cursorState D.axesFit (w/2) off (G).cells
local notation "ss" => (dir).stages
local notation "edges" => (dir).edges
local notation "u" => TraceAdmission.receiverAge w
local notation "stop" => finish (a).K ss (a).cursor
local notation "x" => (a).terminal ss edges W
local notation "O" => (a).cursorSeedSites D.block D.axesFit (w/2) off (G).cells rfl rfl
local notation "C" => D.issuedCharges
local notation "start" => TraceReceiverSeedWords.start D.machine D.fit D.field D.state D.block D.axesFit
local notation "pairs" => TraceReceiverSeedWords.pairs D.machine D.fit D.field D.state
local notation "node" => (dir).node
local notation "par" => (dir).parameters
local notation "N" => (par).roots
local notation "hdr" => (a).control+64
local notation "destAddr" => (traceLimit w+(ss).length*(par).lanes)
local notation "dst" => (14*GridDescription.sector w)
local notation "cut" => (2^(3*w/5))
local notation "cap" => l.selectorCap
local notation "bits" => GridPhysicalSelector.bits D.run
local notation "units" => D.issuedUnit w l.degree l.stageRate l.rootRate
local notation "T" => ((l.sideMinusOne+1)^(l.dimension+1)*l.copies)
local notation "d" => ((l.dimension+1)+2)
local notation "text" => SelfAdvice.textSize W pc pp
local notation "args" => GridNativeImage.parameterCount D l
local notation "choose" => GridReceiverTickDirectory.receiver w u text args N d T
local notation "histTime" => (cut+(cut+Archive.terminalTime x))
local notation "nav" => TraceReceiverProgram.navigation D.block W dir
local notation "splitLanes" => (by rw [D.block.charge_repeat]; have := D.passesFit; omega :
  axes+1=(P).charge+rem)
local notation "Y" => (splitLanes ▸ X : State (2^D.block.exponent 0) ((P).charge+rem))

variable (geom : ElectionRoom D l) (safe : GridNativeDispatch.WordRoom D)
    (z : D.trace) (sel : Fin (l.selectorCap+1) → Bool)
    (t : Fin ((l.sideMinusOne+1)^(l.dimension+1)*l.copies))
    (input origin endState : Memory (64*w))
local notation "costRows" => (D.costs (GridNativeImage.resources D l) z.1 l.dimension l.sideMinusOne l.bank C units)
local notation "source" => GridStructuralHeader.selectorBit cap sel
local notation "table" => (B).recordTable (B).alphabetCap W D.passes rem Y le_rfl
  (by rw [State.maxWidth_cast_lanes,←Nat.mul_assoc];exact safe)

/-- The same typed branch and native word memories for cache publication and terminal extraction. -/
structure Journal where
  reg : Memory W
  classified : Memory W
  out : Memory W
  path : D.run.ArchivePath z.1 C O
  mid : Memory W
  saved : Memory W
  suffix : List Bool
  count : D.roots z.1=N
  initial : Post a P rem Y (table).records (2^w) cut source input origin out
  read : D.run.plan.read (GridNativeDispatch.actualTable D safe).codes (List.ofFn (fun j : Fin cut=> source j.val))=
    some (z.1,suffix)
  numbered : D.run.FinalNumbered z.1 C O path
  terminal : out=TerminalWireArchive.image x mid
  visits : ∀ (U : Type) (L : (X).Words U),D.run.WordVisits (RecordedWordStep (a).K ((a).control:Word W)
    (((a).control+1:ℕ):Word W) (stop).header (stop).heap mid U (B).publicTemplate) z.1
    (Physical.registerOnLanes B U D.passes rem X splitLanes).1.steps L C O path
  resources : let idx:=Resources.indexEquiv D.run z.1 count
    Resources.Registered destAddr dst par (fun j=>idx (D.run.plan.destination z.1 (initialLane (Nat.succ_pos axes) j)))
      (fun f=>units*D.run.chargeAt z.1 C start (idx.symm f)) reg
  below : ∀ i,i<(a).seed → reg i=input i
  archived : ∀ i,i<hdr → reg i=out i
  charged : (O).Charged (node).banks (natural saved) start pairs
  stored : D.run.ArchiveRowsStored (node).banks (natural saved) z.1 C O path
  savedAt : ∀ i,TickWorkspace.base u 43 ≤ i → i<TickWorkspace.base u 45 → reg i=saved i
  stagePost : TraceRecovery.stagePost (a).K ss (a).cursor (O).layer (·<hdr) (natural out)
    (directoryCap B) (directoryCap B) (fun _=>False)
    (D.run.archiveList z.1 C O path (a).seedData) (D.run.finalArchive z.1 C O path).1
  directory : MountedAt (natural out) (a).K ss (a).cursor
  initialWords : ∀ i,(a).initialRecords ≤ i → i<(a).metadataEnd → mid i=origin i
  cache : ReceiverCache u (a).cursor.header (ss).length (rowBudget W node ((axes+1)*2^(axes+1)))
    (stop).heap node (O).layer (D.run.archiveList z.1 C O path (a).seedData) mid out saved reg
  assigned : GridSimulation.Assigned geom.teams_pos costRows reg classified
  ticked : GridReceiverTickDirectory.Ticked (GridReceiverTickDirectory.banks w u)
    (FactorAllocation.factors w costRows (List.finRange (D.roots z.1)) t) (t.val:Word W) classified endState

theorem recover (elected : Elected D l geom safe z sel t input origin endState) :
    Nonempty (Journal D l geom safe z sel t input origin endState) := by
  obtain ⟨reg,hist,classed,assigned,ticked⟩:=elected
  obtain ⟨out,initial,suffix,path,mid,count,read,numbered,terminal,visits,
    resources,below,archived,saved,charged,stored,savedAt,stagePost,directory,initialWords,cache⟩:=hist
  exact ⟨⟨reg,classed,out,path,mid,saved,suffix,count,initial,read,numbered,terminal,visits,
    resources,below,archived,charged,stored,savedAt,stagePost,directory,initialWords,cache,assigned,ticked⟩⟩

variable {D l geom safe z sel t input origin endState}

theorem Journal.histories (j : Journal D l geom safe z sel t input origin endState) :
    GridReceiverDirectory.Histories D l z sel safe input origin j.reg :=
  ⟨j.out,j.initial,j.suffix,j.path,j.mid,j.count,j.read,j.numbered,j.terminal,j.visits,
    j.resources,j.below,j.archived,j.saved,j.charged,j.stored,j.savedAt,j.stagePost,
    j.directory,j.initialWords,j.cache⟩

theorem Journal.elected (j : Journal D l geom safe z sel t input origin endState) :
    GridReceiverDirectory.Elected D l geom safe z sel t input origin endState :=
  ⟨j.reg,j.histories,j.classified,j.assigned,j.ticked⟩

theorem Journal.layer (j : Journal D l geom safe z sel t input origin endState) :
    (D.run.finalArchive z.1 C O j.path).1=TraceRecovery.lastLayer (a).K ss (a).cursor (a).seedLayer :=
  j.stagePost.2.1

theorem Journal.first (j : Journal D l geom safe z sel t input origin endState) :
    (D.run.finalArchive z.1 C O j.path).1.first=(par).firstFinal :=
  congrArg Layer.first j.layer

theorem Journal.roots (j : Journal D l geom safe z sel t input origin endState) :
    (D.run.finalArchive z.1 C O j.path).1.count=N :=
  congrArg Layer.count j.layer

theorem Journal.card (j : Journal D l geom safe z sel t input origin endState) :
    D.roots z.1=(D.run.finalArchive z.1 C O j.path).1.count :=
  j.count.trans j.roots.symm

end Hierarchy.TraceReceiverElectedJournal
end

end OAI
