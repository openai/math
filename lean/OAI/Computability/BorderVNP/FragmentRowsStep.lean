import OAI.Computability.BorderVNP.FragmentRowsCable

/-! # Native transition for each actual populated delivery or cable -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.FragmentRows

open Diagonal.ExternalSew.Fragments VPVNP.BurstRAM VPVNP.BurstRAM.PrivateRAM

set_option maxHeartbeats 3000000 in
/-- Emit one positive interval precisely when its row points into the supplied
bank. Private-description deliveries are skipped at their actual offset. -/
theorem data_step_run {w : ℕ} (pub : Arg → Word w) (mac : TeamOpcode.Macros w 8)
    (r : Bank w) (m : Memory w) (l : Layout) (before : ℕ → ℕ) (i used : ℕ)
    (fit : l.Fits w before) (ready : l.Ready (.ofWords r m)) (freeze : l.Frozen before (readings m))
    (idx : readings r 15 = i) (cnt : readings r 14 = used) (hi : i < l.count)
    (room : used < 2*l.host.count+l.count) :
    BoundedRun pub mac dataStep r m dataStep.slots
      (StepResult l (readings m) i used (l.liveRow before i)) := by
  have hreg (j : Reg) (hj : j.val ≤ 13 ∨ j.val = 16) : readings r j = l.regValue j.val := ready j hj
  have atRow (j : ℕ) (hj : j < 7) : readings m (l.deliveries+7*i+j) = before (l.deliveries+7*i+j) :=
    freeze _ (Or.inr (Or.inl ⟨by omega,by omega⟩))
  have t4 := atRow 4 (by decide)
  have t5 := atRow 5 (by decide)
  have t6 := atRow 6 (by decide)
  have cFit : before (l.deliveries+7*i+4) < l.cells := fit.dataCell i hi
  have supplied := freeze (l.supplied+before (l.deliveries+7*i+4)) (Or.inr (Or.inr (Or.inl ⟨by
    dsimp [Layout.supplied]; omega,by omega⟩)))
  have absBase := freeze (l.host.cells+2*before (l.deliveries+7*i+4)+1) (Or.inr (Or.inr (Or.inr ⟨by omega,by omega⟩)))
  have ends := fit.dataEnd
  have capacity := fit.quadEnd
  have supEnd := fit.relativeEnd
  have bankEnd := fit.cellEnd
  by_cases small : before (l.deliveries+7*i+5) < before (l.supplied+before (l.deliveries+7*i+4))
  · by_cases zero : before (l.deliveries+7*i+6) = 0
    · apply run_step_of_eval pub mac r m l .data i used _ ready
      · simp (config := {decide := true}) [Pass.step,dataStep,Code.block,Code.fixedSafe,Code.fixedEval,
          Code.safeReadOnly,Code.evalNat,NatState.ofWords,addressOpFits,addressOp,hreg,Layout.regValue,idx,t4,t5,t6,supplied,small,zero]
        omega
      · simp (config := {decide := true}) [Pass.step,dataStep,Code.block,Code.fixedEval,Code.evalNat,
          NatState.ofWords,addressOp,hreg,Layout.regValue,idx,cnt,t4,t5,t6,supplied,small,zero,
          Layout.liveRow,live,Layout.row,Packing.BottomReports.Writer.write]
    have pos : 0 < before (l.deliveries+7*i+6) := Nat.pos_of_ne_zero zero
    let q : Quad := ⟨before (l.deliveries+7*i+4),before (l.deliveries+7*i+5),
      before (l.host.cells+2*before (l.deliveries+7*i+4)+1)+before (l.deliveries+7*i+5),
      before (l.deliveries+7*i+6)⟩
    have src := fit.dataSource i hi q (by simp [q,Layout.liveRow,live,Layout.row,small,pos])
    dsimp only [q] at src
    apply run_step_of_eval pub mac r m l .data i used _ ready
    · simp (config := {decide := true}) [Pass.step,dataStep,Code.block,Code.fixedSafe,Code.fixedEval,
        Code.safeReadOnly,Code.evalNat,NatState.ofWords,addressOpFits,addressOp,hreg,Layout.regValue,idx,cnt,
        t4,t5,t6,supplied,small,zero,absBase,appendQuad]
      omega
    · simp (config := {decide := true}) [Pass.step,dataStep,Code.block,Code.fixedEval,Code.evalNat,
        NatState.ofWords,addressOp,hreg,Layout.regValue,idx,cnt,t4,t5,t6,supplied,small,zero,pos,absBase,
        appendQuad,Layout.liveRow,live,Layout.row,Quad.words,Packing.BottomReports.Writer.write]
  · apply run_step_of_eval pub mac r m l .data i used _ ready
    · simp (config := {decide := true}) [Pass.step,dataStep,Code.block,Code.fixedSafe,Code.fixedEval,
        Code.safeReadOnly,Code.evalNat,NatState.ofWords,addressOpFits,addressOp,hreg,Layout.regValue,idx,t4,t5,supplied,small]
      omega
    · simp (config := {decide := true}) [Pass.step,dataStep,Code.block,Code.fixedEval,Code.evalNat,
        NatState.ofWords,addressOp,hreg,Layout.regValue,idx,cnt,t4,t5,supplied,small,Layout.liveRow,
        live,Layout.row,Packing.BottomReports.Writer.write]

/-- One verified iteration of any of the three fixed native passes. -/
theorem step_run {w : ℕ} (pub : Arg → Word w) (mac : TeamOpcode.Macros w 8)
    (r : Bank w) (m : Memory w) (l : Layout) (before : ℕ → ℕ) (p : Pass) (i used : ℕ)
    (fit : l.Fits w before) (ready : l.Ready (.ofWords r m)) (freeze : l.Frozen before (readings m))
    (idx : readings r 15 = i) (cnt : readings r 14 = used) (hi : i < p.count l)
    (room : used < 2*l.host.count+l.count) :
    BoundedRun pub mac p.step r m p.step.slots (StepResult l (readings m) i used (p.row l before i)) := by
  cases p with
  | cable side => exact cable_step_run pub mac r m l before side i used fit ready freeze idx cnt hi room
  | data => exact data_step_run pub mac r m l before i used fit ready freeze idx cnt hi room

end RoutingISA.FragmentRows

end BorderVNP
end Computability
end OAI
