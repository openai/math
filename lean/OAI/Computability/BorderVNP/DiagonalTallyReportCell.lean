import OAI.Computability.BorderVNP.DiagonalTallyReportCost
import OAI.Computability.BorderVNP.DiagonalTallyReportPublish
import OAI.Computability.BorderVNP.RoutingISATableEvents

/-! # Native execution and exact chronological choices of one owned cell -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace DiagonalTallyCellReports

open VPVNP.BurstRAM RoutingISA DiagonalResidueRAM

/-- Full native memory image for an owned cell, including its exact physically sampled tail. -/
def ReportCell.image {l : ReportLayout} (c : ReportCell l) (q : ReportCursor) (m : ℕ → ℕ) :=
  c.finalImage (c.localEnd q) (c.prefixImage q m)

/-- All numeric input and allocation conditions of an owned cell, on its chronological
natural memory images. No machine execution is assumed. -/
def ReportCell.Input {l : ReportLayout} (c : ReportCell l) (q : ReportCursor)
    (w p description : ℕ) (m : ℕ → ℕ) :=
  c.PrefixInput q w p description m ∧ c.PublishFit (c.localEnd q) w (c.prefixImage q m)

/-- Work for exactly this cell's compiled native instructions. -/
def ReportCell.work {l : ReportLayout} (c : ReportCell l) (q : ReportCursor) :=
  c.prefixCost q+publishCell.slots+(6*c.bits.length+6)

/-- Each step preserves the uniform outer inputs and advances the four persistent cursors.
The only choices are the emitted count and use flags of this one cell. -/
theorem ReportCell.runs {w : ℕ} (pub : Arg → Word w) (mac : TeamOpcode.Macros w 8)
    (s : Bank w) (m : Memory w) (l : ReportLayout) (c : ReportCell l) (q : ReportCursor)
    (p description : ℕ) (hs : l.stable (readings s)) (hq : q.loaded (readings s))
    (cursor : (s 0).val=p) (input : c.Input q w p description (readings m)) :
    ∃ es t mt, Runs pub mac cellReports s m es t mt ∧ TraceOK es c.bits es.length ∧
      traceCost es ≤ c.work q ∧ l.stable (readings t) ∧ (c.after q).loaded (readings t) ∧
      (t 0).val=p+6 ∧ readings mt=c.image q (readings m) := by
  obtain ⟨a,u,mu,r₁,c₁,pre,img⟩ := c.prefix_runs pub mac s m l q p description hs hq cursor input.1
  obtain ⟨loc,ptr,num,start,sbase⟩ := pre
  obtain ⟨ls,lq,_,_,ext,_,supp,rows⟩ := loc
  have regs : c.PublishRegs (c.localEnd q) (readings u) := ⟨ls.1,num,start,sbase,ext,supp,rows⟩
  obtain ⟨b,t,mt,r₂,tr₂,cb,img₂,keep⟩ := publishGuess_runs pub mac u mu l c (c.localEnd q)
    regs (img ▸ input.2) (c.external_end q)
  have fields := r₁.unsigned_events (by decide)
  have tr₁ : TraceOK a [] a.length :=
    ⟨rfl,List.flatMap_eq_nil_iff.mpr fun e he => (fields e he).1,fun e he => (fields e he).2⟩
  have run := r₁.seq r₂
  refine ⟨_,t,mt,run,?_,?_,l.stable_after run hs (by decide),?_,?_,?_⟩
  · rw [List.length_append,tr₂.1]
    simpa only [List.nil_append] using tr₁.append tr₂
  · rw [show traceCost (a++b)=traceCost a+traceCost b from VPVNP.RAMBuckets.cost_append ..,cb,work,
      Nat.add_assoc]
    exact Nat.add_le_add_right c₁ _
  · rw [c.global_end q] at lq
    obtain ⟨packed,desc,refs,prior⟩ := lq
    exact ⟨(congrArg Fin.val (keep 20 (by decide) (by decide) (by decide))).trans packed,
      (congrArg Fin.val (keep 30 (by decide) (by decide) (by decide))).trans desc,
      (congrArg Fin.val (keep 31 (by decide) (by decide) (by decide))).trans refs,
      (congrArg Fin.val (keep 32 (by decide) (by decide) (by decide))).trans prior⟩
  · exact (congrArg Fin.val (keep 0 (by decide) (by decide) (by decide))).trans ptr
  · rw [img₂,img,image]

end DiagonalTallyCellReports

end BorderVNP
end Computability
end OAI
