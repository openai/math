import OAI.Computability.BorderVNP.CubeISAOwnedRows
import OAI.Computability.BorderVNP.CubeISARowAccumSingleton
import OAI.Computability.BorderVNP.RoutingISARegisterFrame

/-! # Native local tallies for a whole accepted singleton interval

One classified ordered label pair supplies its two packed endpoint words.
Only that pair's occupied interval is traversed. Each offset executes the
physical cut scan, adding one precisely on directions where the two radix
digits differ.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.SingleTally

open Cube.RowAccum VPVNP.BurstRAM

/-- Initialize the actual row base, dimension, and radix for the accepted pair. -/
def setup : Code := .block [.copy 45 9, .binary .add 46 5 1, .copy 47 10]

/-- Run one actual coordinate-tally scan per scalar singleton offset. -/
def family : Code := .seq setup (Owned.bitLoop singleLoop)

/-- Memory after `k` bits of one singleton family have been added. -/
def familyImage (mem : ℕ → ℕ) (base dim d x y k addr : ℕ) :=
  mem addr + k*(if base ≤ addr ∧ addr < base+dim then unequalDigit d x y (addr-base) else 0)

private theorem image_step (mem : ℕ → ℕ) (base dim d x y k : ℕ) :
    singleImage (familyImage mem base dim d x y k) base d x y dim =
      familyImage mem base dim d x y (k+1) := by
  funext a
  by_cases h : base ≤ a ∧ a < base+dim <;> simp [singleImage, familyImage, h, Nat.succ_mul, Nat.add_assoc]

/-- The singleton callback computes its exact aggregate row image and
preserves the outer candidate registers. It accepts every legal layout. -/
theorem family_run {w : ℕ} (pub : Arg → Word w) (macros : TeamOpcode.Macros w 8)
    (r : Bank w) (m : Memory w) (base n d x y bits : ℕ)
    (r0 : (r 0).val = 0) (r1 : (r 1).val = 1) (rb : (r 9).val = base)
    (rn : (r 5).val = n) (rd : (r 10).val = d) (rx : (r 24).val = x) (ry : (r 25).val = y)
    (r21 : (r 21).val = bits) (hd : 0 < d) (dim : n+1 < 2^w) (room : base+(n+1) ≤ 2^w)
    (fit : ∀ j < n+1, readings m (base+j) + bits*unequalDigit d x y j < 2^w) :
    TestRun pub macros family r m (5 + bits*(13*(n+1)+7)) True (fun z =>
      z.mem = familyImage (readings m) base (n+1) d x y bits ∧
      ∀ j : Reg, j.val < 24 → j ≠ 20 → z.reg j = (r j).val) := by
  let I (k : ℕ) (z : NatState) : Prop := z.reg 20 = k ∧ z.reg 21 = bits ∧ z.reg 1 = 1 ∧
    z.reg 45 = base ∧ z.reg 46 = n+1 ∧ z.reg 47 = d ∧ z.reg 24 = x ∧ z.reg 25 = y ∧
    z.mem = familyImage (readings m) base (n+1) d x y k ∧
    ∀ j : Reg, j.val < 24 → j ≠ 20 → z.reg j = (r j).val
  have regs (j : ℕ) (z : NatState) (hj : I j z) := And.intro hj.1 hj.2.1
  have visit (k : ℕ) (hk : k < bits) (u : Bank w) (mm : Memory w) (hh : I k (.ofWords u mm)) :
      TestRun pub macros singleLoop u mm (13*(n+1)+5) True (Owned.nextAt I 20 k) := by
    obtain ⟨h20,h21,h1,h45,h46,h47,h24,h25,hm,hr⟩ := hh
    have cap (j : ℕ) (hj : j < n+1) : readings mm (base+j) + unequalDigit d x y j < 2^w := by
      change (NatState.ofWords u mm).mem _ + _ < _
      rw [hm]
      simp only [familyImage, Nat.le_add_right, Nat.add_lt_add_iff_left, hj, and_self, ite_true,
        Nat.add_sub_cancel_left]
      have h := Nat.mul_le_mul_right (unequalDigit d x y j) hk
      rw [Nat.succ_mul] at h
      exact (by omega : readings m (base+j) + k*unequalDigit d x y j + unequalDigit d x y j ≤
        readings m (base+j)+bits*unequalDigit d x y j).trans_lt (fit j hj)
    have run := singleLoop_run pub macros u mm base (n+1) d x y h45 h46 h47 h24 h25 hd room cap
    obtain ⟨es,t,mt,rt,cost,mem⟩ := run
    have keep (j : Reg) (hj : j.val < 50) : (t j).val = (u j).val :=
      congrArg Fin.val (rt.keepsReg ((by decide : ∀ j : Reg, j.val < 50 → singleLoop.keeps j = true) j hj))
    have br : BoundedRun pub macros singleLoop u mm (13*(n+1)+5) (Owned.nextAt I 20 k) := by
      refine ⟨es,t,mt,rt,cost,(keep 1 (by decide)).trans h1,(keep 20 (by decide)).trans h20,?_⟩
      have hm' : readings mt = familyImage (readings m) base (n+1) d x y (k+1) := by
        change (NatState.ofWords t mt).mem = _
        rw [mem, show readings mm = _ from hm, image_step]
      have eq (j : Reg) (hj : j.val < 50) (hne : j ≠ 20) :
          (Owned.increment 20 (.ofWords t mt)).reg j = (u j).val :=
        (Function.update_of_ne hne ..).trans (keep j hj)
      refine ⟨?_, (eq 21 (by decide) (by decide)).trans h21, (eq 1 (by decide) (by decide)).trans h1,
        (eq 45 (by decide) (by decide)).trans h45, (eq 46 (by decide) (by decide)).trans h46,
        (eq 47 (by decide) (by decide)).trans h47, (eq 24 (by decide) (by decide)).trans h24,
        (eq 25 (by decide) (by decide)).trans h25, hm', fun j hj hne => (eq j (by omega) hne).trans (hr j hj hne)⟩
      simp [Owned.increment, NatState.ofWords, readings, keep 20 (by decide), show (u 20).val = k from h20]
    exact br.asTest (by decide)
  have safe : setup.fixedSafe w (readings pub) (.ofWords r m) := by
    simpa (config := {decide := true}) [setup,Code.block,Code.fixedSafe,Code.safeReadOnly,
      Code.fixedEval,Code.evalNat,addressOpFits,NatState.ofWords,readings,rn,r1] using dim
  have init := (setup.runFixed pub macros r m safe).asTest (by decide)
  have run := init.seq (b := Owned.bitLoop singleLoop) (cb := 2 + bits*(13*(n+1)+7))
    (ob := True) (Q := I bits) (fun u mm hu => by
      have hz : readings u 0 = 0 := by
        have e := congrArg (fun z : NatState => z.reg 0) hu
        exact (e.trans (setup.fixedEval_protected _ _ (by decide : setup.protects 45 = true) 0 (by decide))).trans r0
      apply (Owned.bitLoop_run singleLoop bits (fun _ => 13*(n+1)+5) (fun _ => True) I
        (r21 ▸ (r 21).isLt) regs visit u mm hz ?_).mono (by simp) (by simp) (fun _ h => h)
      change I 0 ⟨Function.update (NatState.ofWords u mm).reg 20 0,(NatState.ofWords u mm).mem⟩
      rw [hu]
      refine ⟨by simp,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
      · simpa (config := {decide := true}) [setup,Code.block,Code.fixedEval,Code.evalNat,NatState.ofWords,readings] using r21
      · simpa (config := {decide := true}) [setup,Code.block,Code.fixedEval,Code.evalNat,NatState.ofWords,readings] using r1
      · simpa (config := {decide := true}) [setup,Code.block,Code.fixedEval,Code.evalNat,NatState.ofWords,readings] using rb
      · simp (config := {decide := true}) [setup,Code.block,Code.fixedEval,Code.evalNat,addressOp,NatState.ofWords,readings,rn,r1]
      · simpa (config := {decide := true}) [setup,Code.block,Code.fixedEval,Code.evalNat,NatState.ofWords,readings] using rd
      · simpa (config := {decide := true}) [setup,Code.block,Code.fixedEval,Code.evalNat,NatState.ofWords,readings] using rx
      · simpa (config := {decide := true}) [setup,Code.block,Code.fixedEval,Code.evalNat,NatState.ofWords,readings] using ry
      · funext a
        simp [setup,Code.block,Code.fixedEval,Code.evalNat,familyImage,NatState.ofWords]
      · intro j hj hne
        change Function.update _ _ _ _ = _
        rw [Function.update_of_ne hne]
        exact setup.fixedEval_protected _ _ (by decide : setup.protects 45 = true) j (by omega))
  exact run.mono (by change 3+(2+_) ≤ _; omega) (by simp) (fun _ hz => hz.2.2.2.2.2.2.2.2)

end RoutingISA.SingleTally

end BorderVNP
end Computability
end OAI
