import OAI.Computability.BorderVNP.DiagonalTallyReportMemory
import OAI.Computability.BorderVNP.DiagonalResidueRAMLeadSum
import OAI.Computability.BorderVNP.RoutingISATableState

/-! # Publishing supplemental counters and guessing the actual compact report bits -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace DiagonalTallyCellReports

open VPVNP.BurstRAM VPVNP.BurstRAM.PrivateRAM RoutingISA DiagonalResidueRAM Packing.BottomReports

/-- Actual terminal register values after the cell's count and bundle writers. -/
structure ReportCell.PublishRegs {l : ReportLayout} (c : ReportCell l) (q : LocalReportCursor)
    (r : Reg → ℕ) : Prop where
  control : r 2 = l.control
  number : r 7 = c.number
  start : r 4 = c.external+c.supplied
  packet : r 8 = l.supplement+c.number*l.supplementStride
  external : r 22 = q.external
  supplement : r 28 = q.supplement
  rows : r 29 = q.previousRows

/-- Bounds and pointer reads for the terminal three native stores. The tail-directory
pointer is read after both counter stores. -/
structure ReportCell.PublishFit {l : ReportLayout} (c : ReportCell l) (q : LocalReportCursor)
    (w : ℕ) (m : ℕ → ℕ) : Prop where
  counters : m (l.control+14) = l.counters
  widths : m (l.control+7) = l.tailWidths
  controlEnd : l.control+14 < 2^w
  counterEnd : l.counters+2*c.number+1 < 2^w
  widthEnd : l.tailWidths+c.number < 2^w
  supplementLe : l.supplement+c.number*l.supplementStride ≤ q.supplement
  externalLe : c.external+c.supplied ≤ q.external
  firstClear : l.control+7 ≠ l.counters+2*c.number
  pastClear : l.control+7 ≠ l.counters+2*c.number+1

/-- Memory after installing the record count, its actual scalar payload length, and the
exact number of supplemental bits obtained from the external cursor difference. -/
def ReportCell.publishImage {l : ReportLayout} (c : ReportCell l) (q : LocalReportCursor)
    (m : ℕ → ℕ) : ℕ → ℕ :=
  let counted := Writer.write m (l.counters+2*c.number)
    [q.previousRows,q.supplement-(l.supplement+c.number*l.supplementStride)]
  Function.update counted (l.tailWidths+c.number) (q.external-(c.external+c.supplied))

/-- The actual bit guesses follow the three scalar stores in chronological order. -/
def ReportCell.finalImage {l : ReportLayout} (c : ReportCell l) (q : LocalReportCursor) (m : ℕ → ℕ) :=
  Writer.write (c.publishImage q m) (c.external+c.supplied) (c.bits.map Bool.toNat)

/-- Every physical report lane contains its prescribed choice in the complete image. -/
theorem ReportCell.finalBits {l : ReportLayout} (c : ReportCell l) (q : LocalReportCursor) (m : ℕ → ℕ) :
    CellPacket.WordsAt (c.finalImage q m) (c.external+c.supplied) (c.bits.map Bool.toNat) :=
  Writer.write_read _ _ _

/-- The two counter words and the actual tail width survive the subsequent guesses
when their physical addresses lie outside the compact bit interval. -/
theorem ReportCell.finalCounters {l : ReportLayout} (c : ReportCell l) (q : LocalReportCursor) (m : ℕ → ℕ)
    (eqEnd : q.external=c.external+c.supplied+c.tailWidth)
    (separate : l.tailWidths+c.number < l.counters+2*c.number ∨ l.counters+2*c.number+2 ≤ l.tailWidths+c.number)
    (counterGap : l.counters+2*c.number+2 ≤ c.external+c.supplied ∨ q.external ≤ l.counters+2*c.number)
    (widthGap : l.tailWidths+c.number < c.external+c.supplied ∨ q.external ≤ l.tailWidths+c.number) :
    CellPacket.WordsAt (c.finalImage q m) (l.counters+2*c.number)
      [q.previousRows,q.supplement-(l.supplement+c.number*l.supplementStride)] ∧
    c.finalImage q m (l.tailWidths+c.number)=c.tailWidth := by
  have len : (c.bits.map Bool.toNat).length=c.tailWidth := by simp [bits_length]
  constructor
  · intro i
    have hi : i.val<2 := i.isLt
    rw [finalImage,Writer.write_outside _ _ _ _ (by rw [len]; omega),publishImage,
      Function.update_of_ne (by omega)]
    exact Writer.write_read _ _ _ i
  · rw [finalImage,Writer.write_outside _ _ _ _ (by rw [len]; omega),publishImage,Function.update_self,eqEnd]
    omega

private theorem publish_trace {w : ℕ} (pub : Arg → Word w) (mac : TeamOpcode.Macros w 8)
    (s : Bank w) (m : Memory w) {es t mt} (r : Runs pub mac publishCell s m es t mt) :
    TraceOK es [] publishCell.slots := by
  have h := effect_runs pub mac false s m publishCell (by decide)
  obtain ⟨rfl,_,_⟩ := r.unique_of_deterministic (by decide) h
  simp [publishCell,readControl,Code.block,effect,TraceOK,tick,Code.slots]

/-- Native execution writes both counters and the tail width, resets the bit cursor,
and leaves the exact positive deterministic trace. -/
theorem publishCell_runs {w : ℕ} (pub : Arg → Word w) (mac : TeamOpcode.Macros w 8)
    (s : Bank w) (m : Memory w) (l : ReportLayout) (c : ReportCell l) (q : LocalReportCursor)
    (regs : c.PublishRegs q (readings s)) (fit : c.PublishFit q w (readings m)) :
    ∃ es t mt, Runs pub mac publishCell s m es t mt ∧ TraceOK es [] publishCell.slots ∧
      traceCost es=publishCell.slots ∧ readings mt=c.publishImage q (readings m) ∧
      readings t 22=c.external+c.supplied ∧ readings t 18=q.external-(c.external+c.supplied) := by
  let z := NatState.ofWords s m
  obtain ⟨r₂,r₇,r₄,r₈,r₂₂,r₂₈,r₂₉⟩ := regs
  obtain ⟨hc,ht,bc,br,bt,hs,he,clear₁,clear₂⟩ := fit
  change z.reg 2=_ at r₂
  change z.reg 7=_ at r₇
  change z.reg 4=_ at r₄
  change z.reg 8=_ at r₈
  change z.reg 22=_ at r₂₂
  change z.reg 28=_ at r₂₈
  change z.reg 29=_ at r₂₉
  change z.mem (l.control+14)=_ at hc
  change z.mem (l.control+7)=_ at ht
  have hw : w ≠ 0 := by rintro rfl; simp at bc
  have safe : publishCell.fixedSafe w (readings pub) z := by
    simp (config := {decide := true}) [publishCell,readControl,Code.block,Code.fixedSafe,Code.fixedEval,
      Code.safeReadOnly,Code.evalNat,addressOpFits,addressOp,Function.update,hw,r₂,r₇,r₄,r₈,r₂₂,r₂₈,
      r₂₉,hc,ht,clear₁,clear₂,bc,br,bt,hs,he]
    omega
  obtain ⟨es,t,mt,r,_,state⟩ := publishCell.runFixed pub mac s m safe
  change NatState.ofWords t mt = publishCell.fixedEval (readings pub) z at state
  have tr := publish_trace pub mac s m r
  refine ⟨es,t,mt,r,tr,(plain_return publishCell (by decide) r).1.trans tr.1,?_,?_,?_⟩
  · change (NatState.ofWords t mt).mem = _
    rw [state]
    simp (config := {decide := true}) [publishCell,readControl,Code.block,Code.fixedEval,Code.evalNat,addressOp,
      ReportCell.publishImage,Writer.write,Function.update,r₂,r₇,r₄,r₈,r₂₂,r₂₈,r₂₉,hc,ht,clear₁,clear₂]
    rfl
  · change (NatState.ofWords t mt).reg 22 = _
    rw [state]
    simp [publishCell,readControl,Code.block,Code.fixedEval,Code.evalNat,addressOp,Function.update,r₄]
  · change (NatState.ofWords t mt).reg 18 = _
    rw [state]
    simp [publishCell,readControl,Code.block,Code.fixedEval,Code.evalNat,addressOp,Function.update,r₄,r₂₂]

/-- All and only the actual report choices are consumed on this execution. Its counter
stores, compact report image and native tick charge refer to the same path. -/
theorem publishGuess_runs {w : ℕ} (pub : Arg → Word w) (mac : TeamOpcode.Macros w 8)
    (s : Bank w) (m : Memory w) (l : ReportLayout) (c : ReportCell l) (q : LocalReportCursor)
    (regs : c.PublishRegs q (readings s)) (fit : c.PublishFit q w (readings m))
    (eqEnd : q.external=c.external+c.supplied+c.tailWidth) :
    ∃ es t mt, Runs pub mac (.seq publishCell guessReports) s m es t mt ∧
      TraceOK es c.bits (publishCell.slots+(6*c.bits.length+6)) ∧
      traceCost es=publishCell.slots+(6*c.bits.length+6) ∧ readings mt=c.finalImage q (readings m) ∧
      ∀ j : Reg, j.val<33 → j≠18 → j≠22 → t j=s j := by
  obtain ⟨xs,u,mu,ru,tu,_,mi,hs,hn⟩ := publishCell_runs pub mac s m l c q regs fit
  have he := (s 22).isLt
  change readings s 22 < 2^w at he
  rw [regs.external,eqEnd] at he
  have hl : (u 18).val=c.bits.length := by rw [show (u 18).val=_ from hn,eqEnd,c.bits_length]; omega
  obtain ⟨ys,t,rt,tt,keep⟩ := guessReports_runs pub mac u mu (c.external+c.supplied) c.bits hs hl
    (by rwa [c.bits_length])
  have run := ru.seq rt
  have tr : TraceOK (xs++ys) c.bits (publishCell.slots+(6*c.bits.length+6)) := by
    simpa only [List.nil_append] using tu.append tt
  refine ⟨_,_,_,run,tr,(plain_return _ (by decide) run).1.trans tr.1,?_,?_⟩
  · rw [guessed_readings _ _ _ (by have := fit.controlEnd; omega),mi]
    rfl
  · intro j hj h18 h22
    have kept : ∀ i : Reg, i.val<33 → i≠18 → i≠22 → publishCell.keeps i=true := by decide
    exact (keep j hj).trans (ru.keepsReg (kept j hj h18 h22))

end DiagonalTallyCellReports

end BorderVNP
end Computability
end OAI
