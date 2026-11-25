import OAI.Computability.BorderVNP.CellGadgetEmit
import OAI.Computability.BorderVNP.CellEmitStatementCost

/-! # The physical charge of one reported subtotal row -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace CellSparse.Packet.Emit

open CellMacro.Generator ExactQuantumFactoring.BitStackProgram
open ExactQuantumFactoring.BitStackProgram.Procedure
open private rectangle from OAI.Computability.BorderVNP.CellGadgetEmit

variable {A : Type} {ea : A → List Bool} {dir : A → Directory} {label : A → ℕ} {bits : A → List ℕ}

/-- Total size of the fixed generator templates used to allocate and consume one
local prefix-count rectangle. -/
def scopedGlue : ℕ := layoutSize (.lit 0) + (serialized 8 (.fixed .guess)).length +
  (serialized 8 (.seq (.fixed (.literal false)) (.seq (.fixed .nand) (.fixed .guard)))).length+1

private theorem scoped_nat {a b c d e f g h m n u w : ℕ}
    (ha : a ≤ 10^19*(m+w+1)) (hb : b ≤ 3*(u+w+1)) (hc : c ≤ 3*(u+w+1))
    (hd : d ≤ 10^20*(a+b+1)) (he : e ≤ 10^20*(a+c+1))
    (hf : f ≤ 10^12*(n+e)) (hg : g ≤ 10^12*(d+f)) (hh : h = g) :
    h ≤ 10^70*(m+n+u+w+1) := by omega

/-- Scoping local flags has affine overhead in the actual scalar and statement
calls. Both fixed loop bodies are printed once, regardless of flag count. -/
theorem meter_scopedFlags {n : A → ℕ} {s : A → Stmt} (hn : Procedure ea Nat.bits n)
    (hs : Statement ea s) (x : A) :
    (scopedFlags hn hs).meter x ≤ 10^70*(hn.meter x+hs.meter x+(ea x).length+scopedGlue+1) := by
  let bound := litAddr hn
  let begin := constStmt ea (.fixed .guess)
  let finish := constStmt ea (.seq (.fixed (.literal false)) (.seq (.fixed .nand) (.fixed .guard)))
  let firstLoop := loopStmt bound begin
  let finalLoop := loopStmt bound finish
  let rest := seqStmt hs finalLoop
  apply scoped_nat (a := addrMeter bound x) (b := begin.meter x) (c := finish.meter x)
    (d := firstLoop.meter x) (e := finalLoop.meter x) (f := rest.meter x) (g := (seqStmt firstLoop rest).meter x)
  · apply (meter_litAddr hn x).trans
    apply Nat.mul_le_mul_left
    unfold scopedGlue; omega
  · apply (meter_constStmt ea _ x).trans
    apply Nat.mul_le_mul_left
    unfold scopedGlue; omega
  · apply (meter_constStmt ea _ x).trans
    apply Nat.mul_le_mul_left
    unfold scopedGlue; omega
  · exact meter_loopStmt ..
  · exact meter_loopStmt ..
  · exact meter_seqStmt ..
  · exact meter_seqStmt ..
  · rfl

/-- All genuine child invocations of a reported row, measured on their actual
words. The count and rectangular-scratch routines are charged on one binary
number. The factor sweep and terminal printer each use their own localized input. -/
noncomputable def rowCharge (D : Directory) (i : ℕ) (bs : List ℕ) : ℕ :=
  let cap := D.visitCount
  let aux := (cap+1)*(cap+1)
  getVisitCount.meter D + gadgetRectangle.meter cap + gadgetInit.meter cap +
  (Local.sweepPrinter .gadget).meter ((cap,aux,i),D) + Finish.printer.meter (0,aux,cap,bs)

private theorem row_nat {G R I S F A B C N W Z V K P T Q U Y H : ℕ}
    (hA : A ≤ 6*(N+G)) (hB : B ≤ 6*(A+R)) (hC : C ≤ 3*(Z+1))
    (hP : P ≤ 2*10^9*(B+V)) (hT : T ≤ 2*10^9*(A+P))
    (hQ : Q ≤ 2*10^9*(T+N)) (hU : U ≤ 6*(Q+S))
    (hY : Y ≤ 10^32*(C+B+A+K+F)) (hH : H ≤ 6*(A+I)) :
    10^70*(B+10^12*(H+10^12*(U+Y))+Z+W+1) ≤
      10^140*(N+V+K+Z+W+(G+R+I+S+F)+1) := by omega

/-- The actual full row printer has affine overhead in its genuine local
subcalls, with no polynomial evaluated on the ambient directory by the
constant-size scalar or local finish printers. -/
theorem gadgetRow_meter_le (hd : Procedure ea Typed.directory dir) (hi : Procedure ea Nat.bits label)
    (hs : Procedure ea Typed.naturals bits) (x : A) :
    (gadgetRowStmt hd hi hs).meter x ≤ 10^140*(hd.meter x+hi.meter x+hs.meter x+
      (ea x).length+scopedGlue+rowCharge (dir x) (label x) (bits x)+1) := by
  let D := dir x
  let c := D.visitCount
  let a := (c+1)*(c+1)
  let i := label x
  let bs := bits x
  let cp := getVisitCount.comp hd
  let ax := rectangle cp
  let zero := constant ea Nat.bits 0
  let ai := ax.pair hi
  let ps := cp.pair ai
  let args := ps.pair hd
  let sweep := Local.sweepStmt .gadget hd ps
  let term := Finish.localStmt zero ax cp hs
  let init := gadgetInit.comp cp
  let tail := seqStmt sweep term
  let check := seqStmt init tail
  have h₁ : cp.meter x ≤ 6*(hd.meter x+getVisitCount.meter D) := meter_comp ..
  have h₂ : ax.meter x ≤ 6*(cp.meter x+gadgetRectangle.meter c) := meter_comp ..
  have hz : zero.meter x ≤ 3*((ea x).length+1) := by
    simpa only [show (0 : ℕ).bits = [] by rfl,List.length_nil,Nat.add_zero] using meter_constant ea Nat.bits 0 x
  have hf : term.meter x ≤ 10^32*(zero.meter x+ax.meter x+cp.meter x+hs.meter x+
    Finish.printer.meter (0,a,c,bs)) := Finish.local_meter ..
  have hi' : init.meter x ≤ 6*(cp.meter x+gadgetInit.meter c) := meter_comp ..
  have hs' : sweep.meter x ≤ 6*(args.meter x+(Local.sweepPrinter .gadget).meter ((c,a,i),D)) :=
    meter_comp ..
  have htail := meter_seqStmt sweep term x
  have hcheck := meter_seqStmt init tail x
  have hscope := meter_scopedFlags ax check x
  apply hscope.trans
  have htail' : tail.meter x ≤ _ := htail
  have hcheck' : check.meter x ≤ 10^12*(init.meter x+10^12*(sweep.meter x+term.meter x)) :=
    hcheck.trans (Nat.mul_le_mul_left _ (Nat.add_le_add_left htail' _))
  apply (Nat.mul_le_mul_left _ (Nat.add_le_add_right (Nat.add_le_add_right (Nat.add_le_add_right
    (Nat.add_le_add_left hcheck' _) _) _) _)).trans
  exact row_nat h₁ h₂ hz (meter_pair ax hi x) (meter_pair cp ai x) (meter_pair ps hd x) hs' hf hi'

end CellSparse.Packet.Emit

end BorderVNP
end Computability
end OAI
