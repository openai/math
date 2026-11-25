import OAI.Computability.BorderVNP.CubeDirectedInterval

/-! # Native initialization of the directed cable interval scan

The public setup loads the six pointers and sizes from the frame. A counted loop
clears the entire square table, including equal-label pairs. It makes no writes
to cable ordinals. Their entries are assigned when the scan reaches the cable.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cube.NativeIntervals

open RoutingISA VPVNP.BurstRAM VPVNP.BurstRAM.PrivateRAM

/-- Load the geometry and scratch configuration, then compute the square table length. -/
def setup : Code := .block [
  .constant 0 0, .constant 1 1, .constant 2 3,
  readFrame 3 62 63 6, readFrame 4 62 63 7, readFrame 5 62 63 48,
  readFrame 6 62 63 56, readFrame 7 62 63 57, readFrame 8 62 63 58,
  .binary .mul 9 6 6]

private theorem read_eval (d : Reg) (f : Word 8) (pub : Arg → ℕ) (s : NatState) :
    (readFrame d 62 63 f).fixedEval pub s = ⟨Function.update
      (Function.update (Function.update s.reg 63 f.val) 62 (pub 0+f.val)) d
        (s.mem (pub 0+f.val)), s.mem⟩ := by
  simp (config := { decide := true }) [readFrame, Code.block, Code.fixedEval, Code.evalNat, addressOp,
    Function.update_comm (show (62 : Reg) ≠ 63 by decide)]

private theorem read_safe (d : Reg) (f : Word 8) (pub : Arg → ℕ) (s : NatState)
    (w : ℕ) (hf : pub 0+f.val < 2^w) :
    (readFrame d 62 63 f).fixedSafe w pub s := by
  simp (config := { decide := true }) [readFrame, Code.block, Code.fixedSafe, Code.fixedEval,
    Code.safeReadOnly, Code.evalNat, addressOpFits, hf]
  omega

/-- Execute the fixed configuration code from any incoming register bank. -/
theorem run_setup {w : ℕ} (pub : Arg → Word w) (macros : TeamOpcode.Macros w 8)
    (s : Bank w) (m : Memory w) (l : Layout) (fit : l.Fits w (readings m))
    (hf : (pub 0).val = l.frame) (fields : l.Fields (readings m)) :
    BoundedRun pub macros setup s m setup.slots (fun z => l.Ready z ∧ z.mem = readings m) := by
  obtain ⟨h3,h4,h5,h6,h7,h8⟩ := fields
  have hs : l.alphabet*l.alphabet < 2^w := by simpa only [pow_two] using fit.squareFit
  have ha := fit.frameFit
  have hf' : readings pub 0 = l.frame := hf
  have fs (d : Reg) (f : Word 8) (z : NatState) (h : f.val ≤ 58) :
      (readFrame d 62 63 f).fixedSafe w (readings pub) z :=
    read_safe d f _ _ _ (by rw [hf']; omega)
  apply (Code.runFixed setup pub macros s m ?_).mono le_rfl
  · rintro _ rfl
    constructor
    · intro j hj
      rcases j with ⟨j,hj'⟩
      change j ≤ 9 at hj
      interval_cases j <;>
        simp (config := { decide := true }) [setup, Code.block, read_eval, Code.fixedEval, Code.evalNat,
          addressOp, NatState.ofWords, hf', h3,h4,h5,h6,h7,h8, Layout.regValue, pow_two]
    · simp (config := { decide := true }) [setup, Code.block, read_eval, Code.fixedEval, Code.evalNat,
        NatState.ofWords]
  · simp (config := { decide := true }) [setup, Code.block, Code.fixedSafe, Code.fixedEval,
      Code.safeReadOnly, Code.evalNat, addressOpFits, read_eval, NatState.ofWords, hf', h6, hs,
      fs _ _ _ (by decide : (6 : Word 8).val ≤ 58), fs _ _ _ (by decide : (7 : Word 8).val ≤ 58),
      fs _ _ _ (by decide : (48 : Word 8).val ≤ 58), fs _ _ _ (by decide : (56 : Word 8).val ≤ 58),
      fs _ _ _ (by decide : (57 : Word 8).val ≤ 58), fs _ _ _ (by decide : (58 : Word 8).val ≤ 58)]
    constructor
    · rintro rfl
      simp at ha
    · omega

/-- Clear one directed label-pair entry on each loop iteration. -/
def clear : Code := .block [
  .copy 13 0, .whileLt 13 9 (.block [.binary .add 14 7 13, .store 14 0, .binary .add 13 13 1])]

private theorem zero_succ (base n : ℕ) (mem : ℕ → ℕ) :
    Function.update (zeroPrefix base n mem) (base+n) 0 = zeroPrefix base (n+1) mem := by
  funext a
  by_cases h : a = base+n
  · simp [h,zeroPrefix]
  · rw [Function.update_of_ne h]
    have he : (base ≤ a ∧ a < base+n) ↔ (base ≤ a ∧ a < base+(n+1)) := by omega
    simp only [zeroPrefix, he]

/-- After clearing, all directed widths are zero and the other addresses have their incoming words. -/
theorem run_clear {w : ℕ} (pub : Arg → Word w) (macros : TeamOpcode.Macros w 8)
    (l : Layout) (s : Bank w) (m : Memory w) (ready : l.Ready (.ofWords s m))
    (widthsFit : l.widths+l.alphabet^2 ≤ 2^w) (squareFit : l.alphabet^2 < 2^w) :
    BoundedRun pub macros clear s m (4*l.alphabet^2+2)
      (fun z => l.Ready z ∧ z.mem = zeroPrefix l.widths (l.alphabet^2) (readings m)) := by
  let b := Code.block [.binary .add 14 7 13, .store 14 0, .binary .add 13 13 1]
  let P (i : ℕ) (z : NatState) := l.Ready z ∧ z.reg 13 = i ∧ z.mem = zeroPrefix l.widths i (readings m)
  have regs (i : ℕ) (z : NatState) (h : P i z) : z.reg 13 = i ∧ z.reg 9 = l.alphabet^2 :=
    ⟨h.2.1, h.1 9 (by decide)⟩
  have step (i : ℕ) (hi : i < l.alphabet^2) (u : Bank w) (mu : Memory w)
      (h : P i (.ofWords u mu)) : BoundedRun pub macros b u mu 3 (P (i+1)) := by
    let z := NatState.ofWords u mu
    have h0 : z.reg 0 = 0 := h.1 0 (by decide)
    have h1 : z.reg 1 = 1 := h.1 1 (by decide)
    have h7 : z.reg 7 = l.widths := h.1 7 (by decide)
    have h13 : z.reg 13 = i := h.2.1
    have fit : l.widths+i < 2^w := by omega
    have inc : i+1 < 2^w := by omega
    have hs : b.fixedSafe w (readings pub) z := by
      simp (config := { decide := true }) [b, Code.block, Code.fixedSafe, Code.fixedEval,
        Code.safeReadOnly, Code.evalNat, addressOpFits, h1,h7,h13,fit,inc]
    apply (b.runFixed pub macros u mu hs).mono (by decide)
    rintro y rfl
    refine ⟨Layout.Ready.fixed h.1 (c := b) (by decide) _, ?_, ?_⟩
    · change (b.fixedEval (readings pub) z).reg 13 = i+1
      simp (config := { decide := true }) [b, Code.block, Code.fixedEval, Code.evalNat, addressOp,h13,h1]
    · change (b.fixedEval (readings pub) z).mem = _
      simp (config := { decide := true }) [b, Code.block, Code.fixedEval, Code.evalNat, addressOp,h7,h13,h0]
      rw [show z.mem = _ from h.2.2, zero_succ]
  have start := (Code.copy 13 0).runFixed pub macros s m trivial
  have run := start.seq (b := .whileLt 13 9 b) (t := (l.alphabet^2-0)*(3+1)+1) (Q := P (l.alphabet^2))
    (fun u mu hu => run_counted_loop pub macros 13 9 b (l.alphabet^2) 3 P regs step 0 (Nat.zero_le _) u mu (by
      rw [hu]
      refine ⟨Layout.Ready.fixed ready (c := .copy 13 0) (by decide) _, ?_, ?_⟩
      · simp [Code.fixedEval,Code.evalNat, show (NatState.ofWords s m).reg 0 = 0 from ready 0 (by decide)]
      · funext a
        simp [zeroPrefix, Code.fixedEval, NatState.ofWords]))
  exact run.mono (by change 1+(l.alphabet^2-0)*(3+1)+1 ≤ _; omega) fun _ h => ⟨h.1,h.2.2⟩

/-- Load the geometry configuration and initialize its pair-width scratch array. -/
def init : Code := .seq setup clear

/-- Full native initialization, with the instruction budget uniform in the incoming bank and memory. -/
theorem run_init {w : ℕ} (pub : Arg → Word w) (macros : TeamOpcode.Macros w 8)
    (l : Layout) (s : Bank w) (m : Memory w) (fit : l.Fits w (readings m))
    (hf : (pub 0).val = l.frame) (fields : l.Fields (readings m)) :
    BoundedRun pub macros init s m (setup.slots+(4*l.alphabet^2+2))
      (fun z => l.Ready z ∧ z.mem = zeroPrefix l.widths (l.alphabet^2) (readings m)) := by
  apply (run_setup pub macros s m l fit hf fields).seq
  intro u mu hu
  exact (run_clear pub macros l u mu hu.1 fit.widthsFit fit.squareFit).mono le_rfl
    fun z hz => ⟨hz.1, by rw [hz.2, show readings mu = readings m from hu.2]⟩

end Cube.NativeIntervals

end BorderVNP
end Computability
end OAI
