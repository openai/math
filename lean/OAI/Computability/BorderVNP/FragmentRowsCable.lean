import OAI.Computability.BorderVNP.FragmentRowsState

/-! # Actual native transition for a sparse cable end -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.FragmentRows

open Diagonal.ExternalSew.Fragments Cube.HostScatter VPVNP.BurstRAM VPVNP.BurstRAM.PrivateRAM

private theorem keeps_ready (p : Pass) (j : Reg) (hj : j.val ≤ 13 ∨ j.val = 16) : p.step.keeps j = true := by
  revert j
  cases p with
  | cable side => cases side <;> decide
  | data => decide

/-- Preserve the fixed source registers and install the three verified scalar
and memory outputs of a straight-line step. -/
theorem run_step_of_eval {w : ℕ} (pub : Arg → Word w) (mac : TeamOpcode.Macros w 8)
    (r : Bank w) (m : Memory w) (l : Layout) (p : Pass) (i used : ℕ) (o : Option Quad)
    (ready : l.Ready (.ofWords r m))
    (safe : p.step.fixedSafe w (readings pub) (.ofWords r m))
    (ok : let z := p.step.fixedEval (readings pub) (.ofWords r m)
          z.reg 15 = i+1 ∧ z.reg 14 = used+o.toList.length ∧
          z.mem = Packing.BottomReports.Writer.write (readings m) (l.quads+4*used) (o.toList.flatMap Quad.words)) :
    BoundedRun pub mac p.step r m p.step.slots (StepResult l (readings m) i used o) := by
  obtain ⟨es,t,mt,run,ticks,eq⟩ := p.step.runFixed pub mac r m safe
  exact ⟨es,t,mt,run,ticks,fun j h => (congrArg Fin.val (run.keepsReg (keeps_ready p j h))).trans (ready j h),eq ▸ ok⟩

set_option maxHeartbeats 3000000 in
/-- Scan the actual three-word cable, skip padding and same-cell ends, and
append the addressed crossing interval for the selected endpoint. -/
theorem cable_step_run {w : ℕ} (pub : Arg → Word w) (mac : TeamOpcode.Macros w 8)
    (r : Bank w) (m : Memory w) (l : Layout) (before : ℕ → ℕ) (side : Bool) (i used : ℕ)
    (fit : l.Fits w before) (ready : l.Ready (.ofWords r m)) (freeze : l.Frozen before (readings m))
    (idx : readings r 15 = i) (cnt : readings r 14 = used) (hi : i < l.host.count)
    (room : used < 2*l.host.count+l.count) :
    BoundedRun pub mac (cableStep side) r m (cableStep side).slots
      (StepResult l (readings m) i used (cable l.host before side i)) := by
  have hreg (j : Reg) (hj : j.val ≤ 13 ∨ j.val = 16) : readings r j = l.regValue j.val := ready j hj
  have tri (j : ℕ) (hj : j < 3) : readings m (l.host.cables+3*i+j) = before (l.host.cables+3*i+j) :=
    freeze _ (Or.inl ⟨by omega,by omega⟩)
  have t0 := tri 0 (by decide)
  have t1 := tri 1 (by decide)
  have t2 := tri 2 (by decide)
  simp only [Nat.add_zero] at t0
  have ends := fit.cableEnd
  have capacity := fit.quadEnd
  by_cases same : before (l.host.cables+3*i) = before (l.host.cables+3*i+1)
  · apply run_step_of_eval pub mac r m l (.cable side) i used _ ready
    · simp (config := {decide := true}) [Pass.step,cableStep,Code.block,Code.fixedSafe,Code.fixedEval,
        Code.safeReadOnly,Code.evalNat,NatState.ofWords,addressOpFits,addressOp,hreg,Layout.regValue,idx,t0,t1,same]
      omega
    · simp (config := {decide := true}) [Pass.step,cableStep,Code.block,Code.fixedEval,Code.evalNat,
        NatState.ofWords,addressOp,hreg,Layout.regValue,idx,cnt,t0,t1,same,cable,Cube.HostScatter.Layout.cell,
        Packing.BottomReports.Writer.write]
  by_cases zero : before (l.host.cables+3*i+2) = 0
  · apply run_step_of_eval pub mac r m l (.cable side) i used _ ready
    · simp (config := {decide := true}) [Pass.step,cableStep,Code.block,Code.fixedSafe,Code.fixedEval,
        Code.safeReadOnly,Code.evalNat,NatState.ofWords,addressOpFits,addressOp,hreg,Layout.regValue,idx,t0,t1,t2,same,zero]
      omega
    · simp (config := {decide := true}) [Pass.step,cableStep,Code.block,Code.fixedEval,Code.evalNat,
        NatState.ofWords,addressOp,hreg,Layout.regValue,idx,cnt,t0,t1,t2,same,zero,cable,
        Cube.HostScatter.Layout.cell,Cube.HostScatter.Layout.width,Packing.BottomReports.Writer.write]
  have cFit := fit.cableCell i hi side zero (by simpa [Cube.HostScatter.Layout.cell] using same)
  have sFit := fit.cableSource i hi side zero (by simpa [Cube.HostScatter.Layout.cell] using same)
  have relFit := fit.relativeEnd
  have bankFit := fit.cellEnd
  have offs := freeze (l.host.relative+2*i+side.toNat) (Or.inr (Or.inr (Or.inl ⟨by omega,by
    dsimp [Layout.supplied]; cases side <;> simp <;> omega⟩)))
  let cell := l.host.cell before i side
  have absBase := freeze (l.host.cells+2*cell+1) (Or.inr (Or.inr (Or.inr ⟨by omega,by change cell < l.cells at cFit; omega⟩)))
  dsimp only [cell] at absBase
  dsimp only [Layout.supplied] at relFit
  cases side <;> simp [Cube.HostScatter.Layout.cell,Cube.HostScatter.Layout.dest] at cFit sFit offs absBase <;>
    apply run_step_of_eval pub mac r m l (.cable _) i used _ ready
  all_goals first
    | simp (config := {decide := true}) [Pass.step,cableStep,Code.block,Code.fixedSafe,Code.fixedEval,Code.safeReadOnly,
        Code.evalNat,NatState.ofWords,addressOpFits,addressOp,hreg,Layout.regValue,idx,cnt,t0,t1,t2,same,zero,
        offs,absBase,appendQuad]
      omega
    | simp (config := {decide := true}) [Pass.step,cableStep,Code.block,Code.fixedEval,Code.evalNat,
        NatState.ofWords,addressOp,hreg,Layout.regValue,idx,cnt,t0,t1,t2,same,zero,offs,absBase,appendQuad,cable,
        Cube.HostScatter.Layout.cell,Cube.HostScatter.Layout.width,Cube.HostScatter.Layout.dest,
        Quad.words,Packing.BottomReports.Writer.write]

end RoutingISA.FragmentRows

end BorderVNP
end Computability
end OAI
