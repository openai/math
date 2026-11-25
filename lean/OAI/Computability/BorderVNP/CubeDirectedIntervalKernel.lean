import OAI.Computability.BorderVNP.CubeDirectedInterval

/-! # Native per-cable instruction block for the public cube-packet interval pass -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cube.NativeIntervals

open RoutingISA VPVNP.BurstRAM VPVNP.BurstRAM.PrivateRAM

/-- Read the two processed cells and their width. Preserve direction, and add the
whole live cable to its ordered-label counter with one native store per result. -/
def cableStep : Code := .block [
  .binary .mul 14 2 13, .binary .add 14 3 14, .load 15 14,
  .binary .add 14 14 1, .load 16 14, .binary .add 14 14 1, .load 17 14,
  .binary .add 18 8 13,
  .ifEq 15 16 (.store 18 0) (.block [
    .binary .add 19 5 15, .load 19 19, .binary .add 20 5 16, .load 20 20,
    .binary .mul 19 19 6, .binary .add 19 19 20, .binary .add 19 7 19,
    .load 20 19, .store 18 20, .binary .add 20 20 17, .store 19 20]),
  .binary .add 13 13 1]

set_option maxHeartbeats 2000000 in
/-- The fixed native instruction block reads this cable's real row and label words,
stores its correct ordered-bin ordinal, and retains every other completed interval. -/
theorem run_cableStep {w : ℕ} (pub : Arg → Word w) (macros : TeamOpcode.Macros w 8)
    (l : Layout) (before : ℕ → ℕ) (fit : l.Fits w before) {i : ℕ} (hi : i < l.count)
    (s : Bank w) (m : Memory w) (ready : l.Ready (.ofWords s m)) (idx : (s 13).val = i)
    (image : l.Image before i (readings m)) :
    BoundedRun pub macros cableStep s m cableStep.slots (fun z =>
      l.Ready z ∧ z.reg 13 = i+1 ∧ l.Image before (i+1) z.mem) := by
  let z := NatState.ofWords s m
  have r0 : z.reg 0 = 0 := ready 0 (by decide)
  have r1 : z.reg 1 = 1 := ready 1 (by decide)
  have r2 : z.reg 2 = 3 := ready 2 (by decide)
  have r3 : z.reg 3 = l.cables := ready 3 (by decide)
  have r5 : z.reg 5 = l.labels := ready 5 (by decide)
  have r6 : z.reg 6 = l.alphabet := ready 6 (by decide)
  have r7 : z.reg 7 = l.widths := ready 7 (by decide)
  have r8 : z.reg 8 = l.ordinals := ready 8 (by decide)
  have r13 : z.reg 13 = i := idx
  have same (a : ℕ) (ha : a ∈ [l.cables+3*i,l.cables+3*i+1,l.cables+3*i+2,
      l.labels+l.src before i,l.labels+l.dst before i]) : z.mem a = before a :=
    image.outside _ (fit.input i hi a ha).1 (fit.input i hi a ha).2
  have e0 : z.mem (l.cables+3*i) = l.src before i := same _ (by simp)
  have e1 : z.mem (l.cables+3*i+1) = l.dst before i := same _ (by simp)
  have e2 : z.mem (l.cables+3*i+1+1) = l.width before i := same (l.cables+3*i+2) (by simp)
  have ls : z.mem (l.labels+l.src before i) = before (l.labels+l.src before i) := same _ (by simp)
  have ld : z.mem (l.labels+l.dst before i) = before (l.labels+l.dst before i) := same _ (by simp)
  have key := l.key_lt fit hi
  have width := image.widths _ key
  change z.mem (l.widths+l.key before i) = l.prefix before i (l.key before i) at width
  have keyEq : before (l.labels+l.src before i)*l.alphabet+before (l.labels+l.dst before i) = l.key before i := rfl
  have a0 : 3*i < 2^w := by have := fit.cableFit; omega
  have a1 : l.cables+3*i < 2^w := by have := fit.cableFit; omega
  have a2 : l.cables+3*i+1 < 2^w := by have := fit.cableFit; omega
  have a3 : l.cables+3*i+1+1 < 2^w := by have := fit.cableFit; omega
  have ao : l.ordinals+i < 2^w := by have := fit.ordinalsFit; omega
  have ai : i+1 < 2^w := by have := fit.countFit; omega
  have asrc := (fit.labelsFit i hi (l.src before i) (by simp)).1
  have adst := (fit.labelsFit i hi (l.dst before i) (by simp)).1
  have ak : l.key before i < 2^w := key.trans fit.squareFit
  have am : before (l.labels+l.src before i)*l.alphabet < 2^w := by omega
  have aw : l.widths+l.key before i < 2^w := by have := fit.widthsFit; omega
  have updateFits (hc : l.src before i ≠ l.dst before i) :
      z.mem (l.widths+l.key before i)+l.width before i < 2^w := by
    rw [width]
    simpa [Layout.prefix,Finset.sum_range_succ,hc] using fit.volume (i+1) hi (l.key before i)
  have safe : cableStep.fixedSafe w (readings pub) z := by
    by_cases eq : l.src before i = l.dst before i
    · simp (config := {decide := true}) [cableStep,Code.block,Code.fixedSafe,Code.fixedEval,
        Code.safeReadOnly,Code.evalNat,addressOpFits,addressOp,r0,r1,r2,r3,r8,r13,e0,e1,e2,
        eq,a0,a1,a2,a3,ai,ao]
    · simp (config := {decide := true}) [cableStep,Code.block,Code.fixedSafe,Code.fixedEval,
        Code.safeReadOnly,Code.evalNat,addressOpFits,addressOp,r1,r2,r3,r5,r6,r7,r8,r13,e0,e1,e2,ls,ld,
        keyEq,eq,a0,a1,a2,a3,ai,ao,asrc,adst,ak,am,aw,updateFits eq]
  apply (cableStep.runFixed pub macros s m safe).mono le_rfl
  rintro t rfl
  refine ⟨ready.fixed (c := cableStep) (by decide) _,?_,?_⟩
  · change (cableStep.fixedEval (readings pub) z).reg 13 = i+1
    by_cases eq : l.src before i = l.dst before i <;>
      simp (config := {decide := true}) [cableStep,Code.block,Code.fixedEval,Code.evalNat,addressOp,
        r0,r1,r2,r3,r5,r6,r7,r8,r13,e0,e1,eq]
  have wrote : (cableStep.fixedEval (readings pub) z).mem = l.store before z.mem i := by
    by_cases eq : l.src before i = l.dst before i <;>
      simp (config := {decide := true}) [cableStep,Code.block,Code.fixedEval,Code.evalNat,addressOp,
        r0,r1,r2,r3,r5,r6,r7,r8,r13,e0,e1,e2,ls,ld,keyEq,eq,Layout.store]
  rw [wrote]
  exact image.store fit hi

end Cube.NativeIntervals

end BorderVNP
end Computability
end OAI
