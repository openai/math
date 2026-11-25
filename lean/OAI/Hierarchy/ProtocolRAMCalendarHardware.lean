import OAI.Hierarchy.ProtocolRAMRowText
import OAI.Hierarchy.ProtocolRAMCalendarCost

namespace OAI
/-! # ROM, registers and advice parameters of the chronological controller -/

namespace Hierarchy.ProtocolRAM.Calendar
open Computability.VPVNP.BurstRAM PrivateRAM ProbeStage ProbeStage.Native PurchaseStage
open ThreeFlat.RAM DescriptorExpr PhysicalProcedure
open scoped Classical

variable {w q d : ℕ}

def checkText (c : AttemptGate.Check) := 11+4*(19+c.term.work)

theorem text_check (w : ℕ) (c : AttemptGate.Check) : text (c.code w)=checkText c := by
  simp only [AttemptGate.Check.code,SumScores.procedure,PhysicalInputPhases.writing,text,
    Term.labels_eq,SumScores.step_binds,checkText]
  omega

theorem text_tests (w : ℕ) (b : AttemptGate.TestBoard) :
    text (b.code w)=checkText b.excess+checkText b.payload+checkText b.discrepancy := by
  simp [AttemptGate.TestBoard.code,text_seq,text_check]

theorem text_columns (w : ℕ) (ps : List Pass) : text (auditCode w (columns ps))=listText ps := by
  induction ps with
  | nil => exact text_passes w []
  | cons p ps ih =>
    change text ((p.procedure w).seq (auditCode w (columns ps)))=_
    simp only [text_seq,Pass.procedure,text_scan,ih,listText,List.map_cons,List.sum_cons]
    omega

def postText (L : Dispatch) (B : Repair q d) :=
  (checkText B.tests.excess+checkText B.tests.payload+checkText B.tests.discrepancy)+
    rowText (repairMask B)+rowText (invalidExpr (enabledBatch L B))+
    15+21+listText (writes L B)+rowText (verdict (audits L B))

theorem text_post (w : ℕ) (L : Dispatch) (B : Repair q d) :
    text (postFrozen w L B)=postText L B := by
  have clear : text (ProtocolRAMScalarCounts.clear w B.tally 2)=15 := rfl
  have hist : text (ProtocolRAMScalarCounts.counting w B.keys B.tally L.candidates)=21 := rfl
  simp only [postFrozen,finalVerdict,audits,auditCode,Audit.code,inspection,admission,text_seq,
    text_tests,text_scan,clear,hist,text_columns,postText]
  omega

def eventText (C : Chart w q d) : Event→ℕ
  | .attempt a => rowText (guard C a).term+text (C.frozen a).native+
      postText (C.layout a) (repair C a)+text (C.commit a).native
  | .feed b => listText (feedPasses C b)

theorem text_step (C : Chart w q d) (e : Event) : text (step C e)=eventText C e := by
  cases e with
  | feed b => exact text_passes ..
  | attempt a => simp only [step,eventText,text_seq,Pass.procedure,text_scan,text_post]; omega

theorem text_run (C : Chart w q d) (es : List Event) : text (code C es)=15+(es.map (eventText C)).sum := by
  induction es with
  | nil => exact text_passes w []
  | cons e es ih =>
    simp only [code,text_seq,text_step,ih,List.map_cons,List.sum_cons]
    omega

theorem text_checked (C : Chart w q d) (flag : ℕ) : text (checked C flag)=
    15+((events C.mesh).map (eventText C)).sum+rowText (historyFlag C (events C.mesh)) := by
  simp [checked,text_seq,text_run,text_scan]

/-- The bound for every signed stage comes from its concrete sampler program. -/
theorem text_market {z d k : ℕ} (v : Market z d k) :
    text v.prefix.native ≤ rowText v.failures.test+
      PurchaseFrozen.Shelf.hardware d v.sampler.degree v.depth k := by
  change text ((v.failures.pass.procedure _).seq (v.shelf.program v.sampler z d k v.depth))≤_
  rw [text_seq]
  exact Nat.add_le_add (text_scan _ _ _ _).le (v.shelf.hardware_bound ..)

def commitText (s : StockCommit) {q d : ℕ} (rows : ℕ) (b : Batch q d) :=
  listText (s.charges b rows)+rowText (RepairHistogram.pair s.columns)+22+
    listText (StockAccounts.columns s.plan.clip.base s.goods s.plan.limit (.lookup s.plan.bank .row))+
    listText (RepairHistogram.transfers s.plan s.goods)

theorem text_stock (s : StockCommit) (w rows : ℕ) (b : Batch q d) :
    text (s.native w rows b).native=commitText s rows b := by
  have cost : text (ProtocolRAMWeightedScatter.program w s.plan.src s.occurrences)=22 := rfl
  simp only [StockCommit.native,RepairHistogram.commit,RepairHistogram.cappedCode,RepairHistogram.code,
    text_seq,text_passes,text_scan,cost,commitText]
  omega

/-- A last directed link row uses nine fixed-stride field loops; the ROM never
contains a copy of its input or any per-site count. -/
theorem emitter_text (w src dst n : ℕ) :
    text (ProtocolRAMAddEmit.emit w src dst n)=9*text (ProtocolRAMFieldLoop.procedure w 0 0 0) := by rfl

def sinkText {r edges : ℕ} (s : Sink r edges) :=
  rowText (RouteSettlement.words s.banks)+22+15+
    rowText (packed s.owners (RouteSettlement.fields s.banks s.geometry))+
    9*(15+6+3)

theorem text_sink {r edges : ℕ} (w : ℕ) (s : Sink r edges) : text (s.native w)=sinkText s := by
  have fixed : text (ProtocolRAMWeightedScatter.program w s.source r)=22 := rfl
  have fields : text (ProtocolRAMFieldLoop.procedure w 0 0 0)=15+6+3 := rfl
  simp [Sink.native,RouteSettlement.reporter,RouteSettlement.code,controller,text_seq,text_scan,text_passes,
    report,Pass.procedure,fixed,emitter_text,fields,sinkText,listText,Nat.add_assoc]
  omega

theorem text_complete {r edges : ℕ} (C : Chart w q d) (flag : ℕ) (f : Sink r edges) :
    text (complete C flag f)=15+((events C.mesh).map (eventText C)).sum+
      rowText (historyFlag C (events C.mesh))+sinkText f := by
  simp [complete,text_seq,text_checked,text_sink]


end Hierarchy.ProtocolRAM.Calendar

end OAI
