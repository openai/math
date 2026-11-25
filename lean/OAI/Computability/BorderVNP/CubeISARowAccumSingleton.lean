import OAI.Computability.BorderVNP.CubeISARowAccum

/-! # Counting singleton cut bits from the two packed endpoint labels

Repeated quotient and remainder by the alphabet size give the endpoint
symbols in coordinate order. A singleton contributes one bit in precisely
those directions in which the two symbols differ.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cube.RowAccum

open RoutingISA VPVNP.BurstRAM Physical

/-- Crossing bit determined by the two radix digits at a candidate cut. -/
def unequalDigit (d x y i : ℕ) : ℕ :=
  if x / d^i % d = y / d^i % d then 0 else 1

/-- The native digit comparison gives the physical crossing bit for the actual endpoint labels. -/
theorem unequalDigit_crossCount {n d blocks h K : ℕ} (b s : ℕ)
    (select : Packet n d blocks → Selector n K h) (z : SingleSlot n d blocks (h*b)) (j : Fin (n+1)) :
    unequalDigit d (finFunctionFinEquiv z.1.val.1).val (finFunctionFinEquiv z.1.val.2).val j =
      crossCount b s select (.inr z) j := by
  have digit (u : Label (n+1) d) : (finFunctionFinEquiv u).val / d^j.val % d = (u j).val :=
    congrArg (fun v : Label (n+1) d => (v j).val) (finFunctionFinEquiv.symm_apply_apply u)
  rw [unequalDigit,digit z.1.val.1,digit z.1.val.2]
  by_cases eq : z.1.val.1 j = z.1.val.2 j <;> simp [crossCount,eq,Fin.val_inj]

/-- Image after the singleton has updated the first `i` candidate cuts. -/
def singleImage (original : ℕ → ℕ) (base d x y i a : ℕ) : ℕ :=
  original a + if base ≤ a ∧ a < base+i then unequalDigit d x y (a-base) else 0

private theorem singleImage_succ (old : ℕ → ℕ) (base d x y i : ℕ) :
    Function.update (singleImage old base d x y i) (base+i)
      (singleImage old base d x y i (base+i) + unequalDigit d x y i) =
    singleImage old base d x y (i+1) := by
  funext a
  by_cases eq : a = base+i
  · subst a
    simp [singleImage]
  · rw [Function.update_of_ne eq]
    have same : (base ≤ a ∧ a < base+i) ↔ (base ≤ a ∧ a < base+(i+1)) := by omega
    simp only [singleImage,same]

/-- The final memory word for cut `j` contains exactly the physical singleton contribution. -/
theorem singleImage_crossCount {n d blocks h K : ℕ} (old : ℕ → ℕ) (base b s : ℕ)
    (select : Packet n d blocks → Selector n K h) (z : SingleSlot n d blocks (h*b)) (j : Fin (n+1)) :
    singleImage old base d (finFunctionFinEquiv z.1.val.1) (finFunctionFinEquiv z.1.val.2)
        (n+1) (base+j) = old (base+j) + crossCount b s select (.inr z) j := by
  rw [singleImage, ite_eq_left (by have := j.isLt; omega), Nat.add_sub_cancel_left,
    unequalDigit_crossCount b s select z j]

/-- Registers 45–47 hold the row base, dimension and radix. Registers 51,52 are
successive quotients of the input labels. -/
def singleStep : RoutingISA.Code := .block [
  .binary .mod 53 51 47, .binary .mod 54 52 47,
  .ifEq 53 54 (.constant 54 0) (.copy 54 55),
  .binary .add 53 45 50, .load 56 53, .binary .add 56 56 54, .store 53 56,
  .binary .div 51 51 47, .binary .div 52 52 47, .binary .add 50 50 55]

/-- Tally all singleton cuts, taking the ordered packed labels from registers 24 and 25. -/
def singleLoop : RoutingISA.Code := .seq (.block [.constant 50 0,.constant 55 1,.copy 51 24,.copy 52 25])
  (.whileLt 50 46 singleStep)

private def singleReady (base dim d : ℕ) (z : NatState) : Prop :=
  z.reg 45 = base ∧ z.reg 46 = dim ∧ z.reg 47 = d

private theorem singleReady_keep {base dim d : ℕ} {z : NatState} {c : RoutingISA.Code}
    (hz : singleReady base dim d z) (hc : c.protects 50 = true) (env : Arg → ℕ) :
    singleReady base dim d (c.fixedEval env z) :=
  ⟨(c.fixedEval_protected env z hc 45 (by decide)).trans hz.1,
    (c.fixedEval_protected env z hc 46 (by decide)).trans hz.2.1,
    (c.fixedEval_protected env z hc 47 (by decide)).trans hz.2.2⟩

/-- Each scanned coordinate takes boundedly many physical instructions. The final
image adds one bit exactly on the differing coordinates and preserves every other word. -/
theorem singleLoop_run {w : ℕ} (pub : Arg → Word w) (macros : TeamOpcode.Macros w 8)
    (r : Bank w) (m : Memory w) (base dim d x y : ℕ)
    (rb : (r 45).val = base) (rdim : (r 46).val = dim) (rd : (r 47).val = d)
    (rx : (r 24).val = x) (ry : (r 25).val = y)
    (hd : 0 < d) (room : base+dim ≤ 2^w)
    (fit : ∀ j < dim, readings m (base+j) + unequalDigit d x y j < 2^w) :
    BoundedRun pub macros singleLoop r m (13*dim+5) (fun z =>
      z.mem = singleImage (readings m) base d x y dim) := by
  let image := singleImage (readings m) base d x y
  let P i z := singleReady base dim d z ∧ z.reg 50 = i ∧ z.reg 55 = 1 ∧
    z.reg 51 = x / d^i ∧ z.reg 52 = y / d^i ∧ z.mem = image i
  have oneFit : 1 < 2^w := (Nat.succ_le_of_lt hd).trans_lt (rd ▸ (r 47).isLt)
  have regs i z (hz : P i z) : z.reg 50 = i ∧ z.reg 46 = dim := ⟨hz.2.1,hz.1.2.1⟩
  have step (i : ℕ) (hi : i < dim) (t : Bank w) (mt : Memory w) (hp : P i (.ofWords t mt)) :
      BoundedRun pub macros singleStep t mt 12 (P (i+1)) := by
    let z := NatState.ofWords t mt
    have hz : singleReady base dim d z := hp.1
    obtain ⟨b,_,rad⟩ := hz
    have idx : z.reg 50 = i := hp.2.1
    have one : z.reg 55 = 1 := hp.2.2.1
    have xq : z.reg 51 = x / d^i := hp.2.2.2.1
    have yq : z.reg 52 = y / d^i := hp.2.2.2.2.1
    have mem : z.mem = image i := hp.2.2.2.2.2
    have old : z.mem (base+i) = readings m (base+i) := by simp [mem,image,singleImage]
    have room' : base+i < 2^w := by omega
    have inc : i+1 < 2^w := (Nat.succ_le_of_lt hi).trans_lt (rdim ▸ (r 46).isLt)
    have safe : singleStep.fixedSafe w (readings pub) z := by
      have cap := fit i hi
      by_cases eq : x / d^i % d = y / d^i % d <;>
        simp [unequalDigit,eq] at cap <;>
        simp (config := {decide := true}) [singleStep,RoutingISA.Code.block,RoutingISA.Code.fixedSafe,
          RoutingISA.Code.fixedEval,RoutingISA.Code.safeReadOnly,RoutingISA.Code.evalNat,addressOpFits,
          addressOp,b,rad,idx,one,xq,yq,eq,old,cap,room',inc,hd]
    apply (singleStep.runFixed pub macros t mt safe).mono (by decide)
    rintro u rfl
    change P (i+1) (singleStep.fixedEval (readings pub) z)
    refine ⟨singleReady_keep hp.1 (by decide) _,?_⟩
    have endmem := singleImage_succ (readings m) base d x y i
    change Function.update (image i) (base+i) (image i (base+i) + unequalDigit d x y i) = image (i+1) at endmem
    rw [← mem] at endmem
    by_cases eq : x / d^i % d = y / d^i % d <;>
      simp (config := {decide := true}) [singleStep, RoutingISA.Code.block, RoutingISA.Code.fixedEval,
        RoutingISA.Code.evalNat,addressOp,rad,b,one,idx,xq,yq,eq,Nat.div_div_eq_div_mul,pow_succ] <;>
      simpa [unequalDigit,eq] using endmem
  let init := RoutingISA.Code.block [.constant 50 0,.constant 55 1,.copy 51 24,.copy 52 25]
  have ready : singleReady base dim d (.ofWords r m) := ⟨rb,rdim,rd⟩
  have run := (init.runFixed pub macros r m (by
    simp [init,RoutingISA.Code.block,RoutingISA.Code.fixedSafe,RoutingISA.Code.safeReadOnly,oneFit])).seq
    (b := .whileLt 50 46 singleStep) (t := (dim-0)*(12+1)+1) (Q := P dim)
    (fun t mt eq => run_counted_loop pub macros 50 46 singleStep dim 12 P regs step 0 (by omega) t mt (by
      rw [eq]
      refine ⟨singleReady_keep ready (by decide) _,?_⟩
      simp (config := {decide := true}) [init,RoutingISA.Code.block,RoutingISA.Code.fixedEval,
        RoutingISA.Code.evalNat,NatState.ofWords,readings,rx,ry]
      funext a
      simp [image,singleImage]))
  exact run.mono (by change 4+(dim-0)*(12+1)+1 ≤ _; omega) fun _ hz => hz.2.2.2.2.2

end Cube.RowAccum

end BorderVNP
end Computability
end OAI
