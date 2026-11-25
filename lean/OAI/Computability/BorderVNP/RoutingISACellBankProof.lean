import OAI.Computability.BorderVNP.RoutingISACellBanks
import OAI.Computability.BorderVNP.RoutingISATableEvents

/-! # Execution proof for the physical cell receiving directory -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.CellBanks

open VPVNP.BurstRAM

private theorem setup_run {w : ℕ} (pub : Arg → Word w) (macros : TeamOpcode.Macros w 8)
    (l : Layout) (s : Bank w) (m : Memory w) (frame : readings pub 0 = l.frame)
    (fields : l.Fields (readings m)) (fit : l.Fits w) :
    BoundedRun pub macros setup s m setup.slots (fun z ↦ l.Ready z 0 ∧ z.mem = readings m) := by
  obtain ⟨cells,groups,labels,owners,dest,powers,header,controls,axis,place,start,stride⟩ := fields
  have next : l.controls+9+1 = l.controls+10 := by omega
  have fr := fit.frameRoom
  have hw : w ≠ 0 := by rintro rfl; simp at fr
  have fs (d : Reg) (f : Word 8) (z : NatState) (h : f.val ≤ 92) :
      (readFrame d 62 63 f).fixedSafe w (readings pub) z :=
    readFrame_fixedSafe d f _ _ _ (by rw [frame]; omega)
  apply (setup.runFixed pub macros s m ?_).mono le_rfl
  · rintro z rfl
    simp (config := {decide:=true}) [setup,Code.block,readFrame_fixedEval,Code.fixedEval,Code.evalNat,
      addressOp,requireLt,Layout.Ready,NatState.ofWords,frame,cells,groups,labels,owners,dest,
      powers,header,controls,axis,place,start,stride,next,fit.positive,fit.divisor]
  · have cr := fit.controlRoom
    have hh := fit.headerRoom
    have pow := fit.powerRoom
    simp (disch := decide) [setup,Code.block,Code.fixedSafe,readFrame_fixedEval,Code.fixedEval,
      Code.safeReadOnly,Code.evalNat,addressOpFits,addressOp,requireLt,fs,
      NatState.ofWords,frame,cells,groups,labels,owners,dest,powers,header,controls,
      axis,place,start,stride,next,fit.positive,fit.divisor]
    omega

private theorem step_run {w : ℕ} (pub : Arg → Word w) (macros : TeamOpcode.Macros w 8)
    (l : Layout) (orig : ℕ → ℕ) (fit : l.Fits w) {i : ℕ} (hi : i < l.cells)
    (s : Bank w) (m : Memory w) (ready : l.Ready (.ofWords s m) i)
    (memory : readings m = l.written orig i) :
    BoundedRun pub macros step s m step.slots
      (fun z ↦ l.Ready z (i+1) ∧ z.mem = l.written orig (i+1)) := by
  let z := NatState.ofWords s m
  change z.mem = l.written orig i at memory
  change l.Ready z i at ready
  obtain ⟨r0,r1,r2,r3,r4,r5,r6,r7,r8,r9,r10,r11⟩ := ready
  have g : l.group orig i < l.groups := Nat.mod_lt _ fit.positive
  have oldL : z.mem (l.labels+i) = orig (l.labels+i) := by
    rw [memory]
    apply l.written_outside
    obtain h | h := fit.labelsOff <;> omega
  have oldO : z.mem (l.owners+l.group orig i) = l.owner orig i := by
    rw [memory,Layout.owner]
    apply l.written_outside
    obtain h | h := fit.ownersOff <;> omega
  have gExpr : (orig (l.labels+i)/l.place)%l.groups = l.group orig i := rfl
  have imul : i*2 = 2*i := Nat.mul_comm ..
  have lab := fit.labelRoom
  have own := fit.ownerRoom
  have tab := fit.tableRoom
  have bank := fit.bankRoom
  have prod := Nat.mul_le_mul_right l.stride hi.le
  apply (step.runFixed pub macros s m ?_).mono le_rfl
  · rintro u rfl
    change l.Ready (step.fixedEval _ z) (i+1) ∧ (step.fixedEval _ z).mem = l.written orig (i+1)
    simp (config := {decide:=true}) [step,Code.block,Code.fixedEval,Code.evalNat,addressOp,
      Layout.Ready,r0,r1,r2,r3,r4,r5,r6,r7,r8,r9,r10,r11,oldL,gExpr,oldO,imul]
    rw [memory,Layout.written]
    rfl
  · change step.fixedSafe w (readings pub) z
    simp (config := {decide:=true}) [step,Code.block,Code.fixedSafe,Code.fixedEval,Code.safeReadOnly,
      Code.evalNat,addressOpFits,addressOp,r1,r2,r4,r5,r6,r7,r8,r9,r10,r11,oldL,gExpr,imul,
      fit.divisor,fit.positive]
    omega

/-- The actual native code visits each cell once and installs its chosen owner
and bank address. The exact memory image includes preservation of every word
outside the two-word-per-cell table. -/
theorem install_run {w : ℕ} (pub : Arg → Word w) (macros : TeamOpcode.Macros w 8)
    (l : Layout) (s : Bank w) (m : Memory w) (frame : readings pub 0 = l.frame)
    (fields : l.Fields (readings m)) (fit : l.Fits w) :
    BoundedRun pub macros install s m (setup.slots+l.cells*15+1)
      (fun z ↦ z.mem = l.written (readings m) l.cells) := by
  let I (i : ℕ) (z : NatState) := l.Ready z i ∧ z.mem = l.written (readings m) i
  have first := setup_run pub macros l s m frame fields fit
  have tail (t : Bank w) (mt : Memory w) (h : l.Ready (.ofWords t mt) 0 ∧ readings mt = readings m) :=
    run_counted_loop pub macros 11 3 step l.cells step.slots I
      (fun _ _ hz ↦ ⟨hz.1.2.2.2.2.2.2.2.2.2.2.2,hz.1.2.2.2.1⟩)
      (fun i hi u mu hu ↦ step_run pub macros l (readings m) fit hi u mu hu.1 hu.2)
      0 (Nat.zero_le _) t mt h
  exact (first.seq tail).mono (by change _ + ((l.cells-0)*15+1) ≤ _; omega) (fun _ h ↦ h.2)

end RoutingISA.CellBanks

end BorderVNP
end Computability
end OAI
