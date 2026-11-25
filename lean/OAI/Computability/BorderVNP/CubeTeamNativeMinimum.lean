import OAI.Computability.BorderVNP.CubeFirstMinimum
import OAI.Computability.BorderVNP.RoutingISATableState

/-! # Native first-minimum scan of the team load array

Register 3 holds the number of teams and register 6 the base address of
their loads. The scan compares in increasing team order and changes its
incumbent exactly on a strict improvement. Registers below 9 and all
shared-memory words survive.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cube.TeamNative

open RoutingISA VPVNP.BurstRAM VPVNP.BurstRAM.PrivateRAM

/-- Initialize the incumbent at team zero. -/
def minimumStart : Code := .block [.copy 10 0, .load 11 6, .copy 9 1]

/-- Read one candidate, update the incumbent on a strict decrease and advance. -/
def minimumStep : Code := .block [
  .binary .add 12 6 9, .load 13 12,
  .ifLt 13 11 (.block [.copy 10 9, .copy 11 13]) .nop,
  .binary .add 9 9 1]

/-- Read the full team-load array, returning its first minimizer in 10
and the minimum itself in 11. -/
def teamMinimum : Code := minimumStart.seq (.whileLt 9 3 minimumStep)

private def PrefixBest {r : ℕ} (f : Fin (r+1) → ℕ) (i : ℕ) (b : Fin (r+1)) : Prop :=
  b.val < i ∧ ∀ j : Fin (r+1), j.val < i → f b ≤ f j ∧ (f j ≤ f b → b ≤ j)

private theorem prefix_step {r i : ℕ} (f : Fin (r+1) → ℕ) {b : Fin (r+1)}
    (hi : i < r+1) (h : PrefixBest f i b) :
    PrefixBest f (i+1) (if f ⟨i,hi⟩ < f b then ⟨i,hi⟩ else b) := by
  by_cases hc : f ⟨i,hi⟩ < f b
  · rw [ite_eq_left hc]
    refine ⟨Nat.lt_succ_self _, fun j hj => ?_⟩
    by_cases he : j.val = i
    · obtain rfl : j = ⟨i,hi⟩ := Fin.ext he
      exact ⟨le_rfl, fun _ => le_rfl⟩
    · have hj' := (h.2 j (by omega)).1
      exact ⟨hc.le.trans hj',fun hz => False.elim (hc.not_ge (hj'.trans hz))⟩
  · rw [ite_eq_right hc]
    refine ⟨h.1.trans (Nat.lt_succ_self _), fun j hj => ?_⟩
    by_cases he : j.val = i
    · obtain rfl : j = ⟨i,hi⟩ := Fin.ext he
      exact ⟨le_of_not_gt hc, fun _ => h.1.le⟩
    · exact h.2 j (by omega)

/-- Exact native cost and output of the team minimum search. -/
theorem run_teamMinimum {w r : ℕ} (pub : Arg → Word w) (macros : TeamOpcode.Macros w 8)
    (s : Bank w) (m : Memory w) (base : ℕ) (f : Fin (r+1) → ℕ)
    (h0 : readings s 0 = 0) (h1 : readings s 1 = 1) (h3 : readings s 3 = r+1)
    (h6 : readings s 6 = base) (hm : ∀ j, readings m (base+j.val) = f j)
    (hb : ∀ j : Fin (r+1), base+j.val < 2^w) :
    BoundedRun pub macros teamMinimum s m (12*(r+1)) (fun z =>
      (∀ j : Reg, j.val < 9 → z.reg j = readings s j) ∧ z.mem = readings m ∧
        z.reg 10 = (firstMinimum f).val ∧ z.reg 11 = f (firstMinimum f)) := by
  let P (i : ℕ) (z : NatState) := (∀ j : Reg, j.val < 9 → z.reg j = readings s j) ∧
    z.mem = readings m ∧ z.reg 9 = i ∧ ∃ b : Fin (r+1),
      z.reg 10 = b.val ∧ z.reg 11 = f b ∧ PrefixBest f i b
  have regs (i : ℕ) (z : NatState) (h : P i z) : z.reg 9 = i ∧ z.reg 3 = r+1 :=
    ⟨h.2.2.1, (h.1 3 (by decide)).trans h3⟩
  have step (i : ℕ) (hi : i < r+1) (u : Bank w) (mu : Memory w)
      (h : P i (.ofWords u mu)) : BoundedRun pub macros minimumStep u mu 9 (P (i+1)) := by
    let z := NatState.ofWords u mu
    obtain ⟨hs,hm',h9,b,h10,h11,hbest⟩ := h
    change z.reg 9 = i at h9
    change z.reg 10 = b.val at h10
    change z.reg 11 = f b at h11
    have h1' : z.reg 1 = 1 := (hs 1 (by decide)).trans h1
    have h6' : z.reg 6 = base := (hs 6 (by decide)).trans h6
    have hval : z.mem (base+i) = f ⟨i,hi⟩ := (congrFun hm' (base+i)).trans (hm ⟨i,hi⟩)
    have haddr : base+i < 2^w := hb ⟨i,hi⟩
    have hR : r+1 < 2^w := h3 ▸ (show readings s 3 < _ from (s 3).isLt)
    have inc : i+1 < 2^w := Nat.lt_of_le_of_lt hi hR
    have hsaf : minimumStep.fixedSafe w (readings pub) z := by
      by_cases hc : f ⟨i,hi⟩ < f b <;>
        simp (config := {decide := true}) [minimumStep, Code.block, Code.fixedSafe, Code.fixedEval,
          Code.safeReadOnly, Code.evalNat, addressOpFits, addressOp, h1', h6', h9,h11,
          haddr,hval,inc,hc]
    apply (minimumStep.runFixed pub macros u mu hsaf).mono (by decide)
    rintro y rfl
    refine ⟨fun j hj => (minimumStep.fixedEval_protected _ z (by decide) j hj).trans (hs j hj), ?_⟩
    refine ⟨?_,?_,(if f ⟨i,hi⟩ < f b then ⟨i,hi⟩ else b), ?_, ?_, prefix_step f hi hbest⟩ <;>
      by_cases hc : f ⟨i,hi⟩ < f b <;>
      simp (config := {decide := true}) [minimumStep, Code.block, Code.fixedEval, Code.evalNat,
        addressOp, ← show z = NatState.ofWords u mu from rfl, h9,h10,h11,h1',h6',hm ⟨i,hi⟩,hc,
        show z.mem = readings m from hm']
  have start := minimumStart.runFixed pub macros s m (by
    simp [minimumStart, Code.block, Code.fixedSafe, Code.safeReadOnly])
  have run := start.seq (b := .whileLt 9 3 minimumStep) (t := (r+1-1)*(9+1)+1)
    (Q := P (r+1)) (fun u mu hu => run_counted_loop pub macros 9 3 minimumStep (r+1) 9
      P regs step 1 (by omega) u mu (by
        rw [hu]
        refine ⟨fun j hj => minimumStart.fixedEval_protected _ _ (by decide) j hj, rfl, ?_, 0, ?_, ?_, ?_⟩
        · simp (config := {decide := true}) [minimumStart, Code.block, Code.fixedEval, Code.evalNat,
            NatState.ofWords, h1]
        · simp (config := {decide := true}) [minimumStart, Code.block, Code.fixedEval, Code.evalNat,
            NatState.ofWords, h0]
        · simpa (config := {decide := true}) [minimumStart, Code.block, Code.fixedEval, Code.evalNat,
            NatState.ofWords, h6] using hm 0
        · refine ⟨by simp, fun j hj => ?_⟩
          obtain rfl : j = 0 := Fin.ext (by simpa using hj)
          exact ⟨le_rfl,fun _ => le_rfl⟩))
  apply run.mono (by change 3+(r+1-1)*(9+1)+1 ≤ 12*(r+1); omega)
  rintro z ⟨hs,hm',_,b,h10,h11,hb'⟩
  have he := (firstMinimum_eq_iff f b).2
    ⟨fun j => (hb'.2 j j.isLt).1, fun j => (hb'.2 j j.isLt).2⟩
  exact ⟨hs,hm',he.symm ▸ h10, he.symm ▸ h11⟩

end Cube.TeamNative

end BorderVNP
end Computability
end OAI
