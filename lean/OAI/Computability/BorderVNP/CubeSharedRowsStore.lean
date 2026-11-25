import OAI.Computability.BorderVNP.CubeSharedRowsLoad

/-! # Appending the actual seven-word shared transmission record -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cube.SharedRows

open RoutingISA VPVNP.BurstRAM VPVNP.BurstRAM.PrivateRAM

/-- Write the complete kind-zero shared interval in the transmission ABI.
The inner symbol and output cursor are then advanced. -/
def storeFields : Code := .block [
  .store 16 0, .binary .add 16 16 1, .store 16 17,
  .binary .add 16 16 1, .store 16 18, .binary .add 16 16 1, .store 16 19,
  .binary .add 16 16 1, .store 16 0, .binary .add 16 16 1, .store 16 20,
  .binary .add 16 16 1, .store 16 21,
  .binary .add 14 14 1, .binary .add 15 15 1]

/-- The full row-emission instruction sequence. -/
def emitPair : Code := .seq loadFields storeFields

/-- Configuration of the nested symbol loops and the contiguous output prefix. -/
structure LoopState (l : Layout) (before : ℕ → ℕ) (s t : ℕ) (z : NatState) : Prop where
  /-- Stable public layout. -/
  ready : l.Ready z
  /-- Outer symbol. -/
  outer : z.reg 13 = t
  /-- Inner symbol. -/
  inner : z.reg 14 = s
  /-- First free output record. -/
  cursor : z.reg 15 = l.rowIndex s t
  /-- The actual seven fields of all completed records. -/
  image : l.Image before (l.rowIndex s t) z.mem

set_option maxHeartbeats 2000000 in
private theorem run_store {w : ℕ} (pub : Arg → Word w) (macros : TeamOpcode.Macros w 8)
    (l : Layout) (before : ℕ → ℕ) (fit : l.Fits w before) {s t : ℕ} (hs : s < t) (ht : t < l.groups)
    (bank : Bank w) (m : Memory w) (buffer : Buffered l before s t (.ofWords bank m))
    (image : l.Image before (l.rowIndex s t) (readings m)) :
    BoundedRun pub macros storeFields bank m storeFields.slots (LoopState l before (s+1) t) := by
  let z := NatState.ofWords bank m
  have r0 : z.reg 0 = 0 := buffer.ready 0 (by decide)
  have r1 : z.reg 1 = 1 := buffer.ready 1 (by decide)
  obtain ⟨r13,r14,r15⟩ := buffer.counters
  change z.reg 13 = t at r13
  change z.reg 14 = s at r14
  change z.reg 15 = l.rowIndex s t at r15
  have r16 : z.reg 16 = l.address (l.rowIndex s t) := buffer.record
  obtain ⟨r17,r18,r19,r20,r21⟩ := buffer.fields
  change z.reg 17 = _ at r17
  change z.reg 18 = _ at r18
  change z.reg 19 = _ at r19
  change z.reg 20 = _ at r20
  change z.reg 21 = _ at r21
  have hrow := l.index_lt hs ht
  have ha : l.address (l.rowIndex s t)+6 < 2^w := by
    have ha := fit.recordsFit
    dsimp [Layout.address] at *
    omega
  have hi : s+1 < 2^w := by have := fit.groupFit; omega
  have hc : l.rowIndex s t+1 < 2^w := by have := fit.countFit; omega
  have hsafe : storeFields.fixedSafe w (readings pub) z := by
    simp (config := {decide := true}) [storeFields,Code.block,Code.fixedSafe,Code.fixedEval,
      Code.safeReadOnly,Code.evalNat,addressOpFits,addressOp,r1,r14,r15,r16,hi,hc]
    omega
  apply (storeFields.runFixed pub macros bank m hsafe).mono le_rfl
  rintro out rfl
  change LoopState l before (s+1) t (storeFields.fixedEval (readings pub) z)
  have wrote : (storeFields.fixedEval (readings pub) z).mem =
      writeRow z.mem (l.address (l.rowIndex s t)) (l.row before s t) := by
    simp (config := {decide := true}) [storeFields,Code.block,Code.fixedEval,Code.evalNat,addressOp,
      r0,r1,r16,r17,r18,r19,r20,r21,writeRow,Layout.row]
  refine ⟨buffer.ready.fixed (c := storeFields) (by decide) _,?_,?_,?_,?_⟩
  · simpa (config := {decide := true}) [storeFields,Code.block,Code.fixedEval,Code.evalNat,addressOp] using r13
  · simp (config := {decide := true}) [storeFields,Code.block,Code.fixedEval,Code.evalNat,addressOp,r14,r1]
  · simp (config := {decide := true}) [storeFields,Code.block,Code.fixedEval,Code.evalNat,addressOp,r15,r1,Layout.rowIndex,Nat.add_assoc]
  · rw [wrote]
    exact image.step ht hs

/-- Each genuinely executed symbol-pair step emits its declared interval, keeps the outer symbol
fixed, and advances both the inner symbol and contiguous record cursor by one. -/
theorem run_emitPair {w : ℕ} (pub : Arg → Word w) (macros : TeamOpcode.Macros w 8)
    (l : Layout) (before : ℕ → ℕ) (fit : l.Fits w before) {s t : ℕ} (hs : s < t) (ht : t < l.groups)
    (bank : Bank w) (m : Memory w) (state : LoopState l before s t (.ofWords bank m)) :
    BoundedRun pub macros emitPair bank m (loadFields.slots+storeFields.slots) (LoopState l before (s+1) t) := by
  apply (run_loadFields pub macros l before fit hs ht bank m state.ready state.outer state.inner state.cursor state.image).seq
  intro u mu hu
  apply run_store pub macros l before fit hs ht u mu hu.1
  rw [show readings mu = _ from hu.2]
  exact state.image

end Cube.SharedRows

end BorderVNP
end Computability
end OAI
