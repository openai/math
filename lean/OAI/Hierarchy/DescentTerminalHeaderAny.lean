import OAI.Hierarchy.DescentTerminalHeaderPrefixAny
import OAI.Hierarchy.DescentTerminalDenseHeaderRAM

namespace OAI
/-! # The four native scans on a complete dense header -/
namespace Hierarchy.DescentTerminalDenseHeaderRAM
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure ProtocolRAM
open scoped Fin.CommRing
noncomputable section
variable {w n : ℕ}

def mem1 (L : Layout) (n : ℕ) (m : Memory w) :=
  DescentTerminalHeaderPrefixRAM.result L.rem.base n (.read L.next) (offsetExpr L) m
def mem2 (L : Layout) (n : ℕ) (m : Memory w) :=
  DescentTerminalHeaderPrefixRAM.result L.whole.base n .add (carryExpr L) (mem1 L n m)
def mem3 (L : Layout) (n : ℕ) (m : Memory w) := image L.index.base n (previous L.whole) (mem2 L n m)
def finalMem (L : Layout) (n : ℕ) (m : Memory w) := image L.control.base n (fmtExpr L) (mem3 L n m)

private theorem four_scans (A B C D : Procedure w) {s₀ s₁ s₂ s₃ s₄ : Memory w}
    {a b c d : ℕ} (ra : A.Exec s₀ s₁ a) (rb : B.Exec s₁ s₂ b)
    (rc : C.Exec s₂ s₃ c) (rd : D.Exec s₃ s₄ d) :
    (((A.seq B).seq C).seq D).Exec s₀ s₄ (a+b+c+d) := by
  have ab : (A.seq B).Exec s₀ s₂ (a+b) :=
    @Procedure.Exec.then w A B s₀ s₁ s₂ a b (@ra) (@rb)
  have abc : ((A.seq B).seq C).Exec s₀ s₃ (a+b+c) :=
    @Procedure.Exec.then w (A.seq B) C s₀ s₂ s₃ (a+b) c (@ab) (@rc)
  exact @Procedure.Exec.then w ((A.seq B).seq C) D s₀ s₃ s₄ (a+b+c) d (@abc) (@rd)

theorem exec_any (L : Layout) (m : Memory w) (fit : Fits L w n) :
    (program w n L).Exec m (finalMem L n m) (cost n L) ∧ CheapCode (program w n L) := by
  have r:=fit.rem.2.2;have u:=fit.whole.2.2;have i:=fit.index.2.2
  have nR:=fit.remRoom;have nU:=fit.wholeRoom;have nI:=fit.indexRoom;have endAt:=fit.endAt
  have source {a} (ha:L.rem.base≤a) (b) (hb:b∈[L.widths,L.offset,L.next,L.carry,L.format]) :
      b.Fits w a := fits_mono (fit.source b hb) ha
  have idx {a} (ha:L.rem.base≤a) : (offsetExpr L).Fits w a :=
    ⟨source ha L.offset (by simp),source ha L.widths (by simp),trivial⟩
  have prev {b : Bank} {a : ℕ} (f:b.Fits w a) : (previous b).Fits w a :=
    ⟨trivial,trivial,trivial,f,trivial,trivial⟩
  have key {a : ℕ} (ha:L.whole.base≤a) : (sourceKey L).Fits w a :=
    ⟨idx (by omega),prev (fits_mono fit.rem ha)⟩
  let remScan := DescentTerminalHeaderPrefixRAM.program w L.rem.base n (.read L.next) (offsetExpr L)
  let wholeScan := DescentTerminalHeaderPrefixRAM.program w L.whole.base n .add (carryExpr L)
  let indexScan := scan w L.index.base n (previous L.whole)
  let formatScan := scan w L.control.base n (fmtExpr L)
  have p1 := @DescentTerminalHeaderPrefixRAM.exec_any w L.rem.base n (.read L.next) (offsetExpr L) m
      (fit.source L.next (by simp)) (idx le_rfl) (by omega)
  have carryFit : (carryExpr L).Fits w L.whole.base :=
    ⟨source (by omega) L.carry (by simp),key le_rfl⟩
  have formatFit : (fmtExpr L).Fits w L.control.base :=
    ⟨source (by omega) L.format (by simp),key (by omega)⟩
  have p2 := @DescentTerminalHeaderPrefixRAM.exec_any w L.whole.base n .add (carryExpr L) (mem1 L n m)
      trivial carryFit (by omega)
  have p3 := @scan_exec w L.index.base n (previous L.whole) (mem2 L n m) (prev fit.whole) (by omega)
  have p4 := @scan_exec w L.control.base n (fmtExpr L) (mem3 L n m) formatFit endAt
  refine ⟨?_,@cheap w n L⟩
  exact @four_scans w remScan wholeScan indexScan formatScan m (mem1 L n m)
    (mem2 L n m) (mem3 L n m) (finalMem L n m) _ _ _ _ (@p1) (@p2) (@p3) (@p4)

theorem before_inputs (L : Layout) (m : Memory w) (fit : Fits L w n) {a : ℕ} (ha:a<L.rem.base) :
    finalMem L n m a=m a := by
  have r:=fit.rem.2.2;have u:=fit.whole.2.2;have i:=fit.index.2.2
  simp [finalMem,mem1,mem2,mem3,DescentTerminalHeaderPrefixRAM.result,image,fillSegment,
    not_le.mpr ha,not_le.mpr (show a<L.whole.base by omega),
    not_le.mpr (show a<L.index.base by omega),not_le.mpr (show a<L.control.base by omega)]

/-- Any truthful width-prefix issuance theorem applies to these actual
deterministic memory words, even if the source theorem quantified its
output memory existentially. -/
theorem physical (L : Layout) (m : Memory w) (fit : Fits L w n) {budget : ℕ} {post : Memory w→Prop}
    (trueHeader : ∃after,(program w n L).Exec m after budget ∧ post after) : post (finalMem L n m) :=
  actual_after _ m _ (exec_any L m fit).1 trueHeader

end
end Hierarchy.DescentTerminalDenseHeaderRAM

end OAI
