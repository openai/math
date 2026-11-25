import OAI.Computability.BorderVNP.CubeISALocalRowCode

/-! # Returning from the native local row tally

The post-tally fragment restores the vertex cursor before scanning the actual
and declared rows. The strict-row return also undoes the orientation swap
used to tally the second set of singletons.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.LocalRow

open VPVNP.BurstRAM CubeLengths

variable {w : ℕ} (pub : Arg → Word w) (mac : TeamOpcode.Macros w 8)

/-- The five fixed instructions restore the cursor and prepare the two-array comparison. -/
theorem finish_run (r : Bank w) (m : Memory w) (n actual claimed saved : ℕ)
    (zero : readings r 0 = 0) (one : readings r 1 = 1) (dim : readings r 5 = n)
    (left : readings r 9 = actual) (right : readings r 59 = claimed) (cursor : readings r 61 = saved)
    (fit : n+1 < 2^w) :
    BoundedRun pub mac finish r m 5 (fun z =>
      z.reg 7 = saved ∧ z.reg 56 = 0 ∧ z.reg 57 = n+1 ∧ z.reg 58 = actual ∧
        z.reg 59 = claimed ∧ z.reg 60 = 1 ∧ z.mem = readings m) := by
  apply (finish.runFixed pub mac r m (by
    simp (config := {decide := true}) [finish,Code.block,Code.fixedSafe,Code.fixedEval,
      Code.safeReadOnly,Code.evalNat,addressOpFits,NatState.ofWords,dim,one,fit])).mono le_rfl
  rintro _ rfl
  simp (config := {decide := true}) [finish,Code.block,Code.fixedEval,Code.evalNat,addressOp,
    NatState.ofWords,zero,one,dim,left,right,cursor]

/-- Return and compare every computed count. Successful runs restore the original vertex
cursor, preserve memory and characterize exactly equality with the advertised row. -/
theorem finishCompare_run (r : Bank w) (m : Memory w) (n actual claimed saved : ℕ)
    (zero : readings r 0 = 0) (one : readings r 1 = 1) (dim : readings r 5 = n)
    (left : readings r 9 = actual) (right : readings r 59 = claimed) (cursor : readings r 61 = saved)
    (fit : n+1 < 2^w) (roomA : actual+(n+1) ≤ 2^w) (roomB : claimed+(n+1) ≤ 2^w) :
    TestRun pub mac (.seq finish compare) r m (5+((n+1)*(rowBody.slots+1)+1))
      (∀ j : Fin (n+1), readings m (actual+j.val) = readings m (claimed+j.val))
      (fun z => z.mem = readings m ∧ z.reg 7 = saved) := by
  let first := (finish_run pub mac r m n actual claimed saved zero one dim left right cursor fit).asTest
    (by decide)
  apply (first.seq (b := compare) (cb := (n+1)*(rowBody.slots+1)+1) (ob := ∀ j : Fin (n+1),
    readings m (actual+j.val) = readings m (claimed+j.val))
    (Q := fun z => z.mem = readings m ∧ z.reg 7 = saved) ?_).mono le_rfl (by simp) (fun _ h => h)
  intro t mt h
  obtain ⟨h7,h56,h57,h58,h59,h60,hmem⟩ := h
  change readings mt = readings m at hmem
  apply (compare_run pub mac t mt actual claimed (n+1) h56 h57 h58 h59 h60 roomA roomB).mono le_rfl
  · rw [hmem]
  · intro z kept
    exact ⟨kept.1.trans hmem,(kept.2 7 (by decide)).trans h7⟩

/-- Restoring the strict row's ordered endpoint registers costs three copies before
the same exact comparison. The scan returns the caller's cursor and preserves memory. -/
theorem swapFinishCompare_run (r : Bank w) (m : Memory w) (n actual claimed saved : ℕ)
    (zero : readings r 0 = 0) (one : readings r 1 = 1) (dim : readings r 5 = n)
    (left : readings r 9 = actual) (right : readings r 59 = claimed) (cursor : readings r 61 = saved)
    (fit : n+1 < 2^w) (roomA : actual+(n+1) ≤ 2^w) (roomB : claimed+(n+1) ≤ 2^w) :
    TestRun pub mac (.seq SingleTally.swap (.seq finish compare)) r m (3+(5+((n+1)*(rowBody.slots+1)+1)))
      (∀ j : Fin (n+1), readings m (actual+j.val) = readings m (claimed+j.val))
      (fun z => z.mem = readings m ∧ z.reg 7 = saved) := by
  have prep : BoundedRun pub mac SingleTally.swap r m 3 (fun z => z.reg 0 = 0 ∧ z.reg 1 = 1 ∧
      z.reg 5 = n ∧ z.reg 9 = actual ∧ z.reg 59 = claimed ∧ z.reg 61 = saved ∧ z.mem = readings m) := by
    apply (SingleTally.swap.runFixed pub mac r m (by
      simp [SingleTally.swap,Code.block,Code.fixedSafe,Code.safeReadOnly])).mono le_rfl
    rintro _ rfl
    simp (config := {decide := true}) [SingleTally.swap,Code.block,Code.fixedEval,Code.evalNat,
      NatState.ofWords,zero,one,dim,left,right,cursor]
  apply ((prep.asTest (by decide)).seq (b := .seq finish compare) (cb := 5+((n+1)*(rowBody.slots+1)+1))
    (ob := ∀ j : Fin (n+1), readings m (actual+j.val) = readings m (claimed+j.val))
    (Q := fun z => z.mem = readings m ∧ z.reg 7 = saved) ?_).mono le_rfl (by simp) (fun _ h => h)
  intro t mt h
  obtain ⟨hz,ho,hd,ha,hb,hc,hmem⟩ := h
  change readings mt = readings m at hmem
  simpa only [hmem] using finishCompare_run pub mac t mt n actual claimed saved hz ho hd ha hb hc
    fit roomA roomB

end RoutingISA.LocalRow

end BorderVNP
end Computability
end OAI
