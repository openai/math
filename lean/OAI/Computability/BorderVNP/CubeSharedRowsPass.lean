import OAI.Computability.BorderVNP.CubeSharedRowsStore

/-! # Sparse native enumeration of all and only distinct symbol-pair lists -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cube.SharedRows

open RoutingISA VPVNP.BurstRAM VPVNP.BurstRAM.PrivateRAM

/-- Emit one triangular row of the public symbol-pair matrix. -/
def outerStep : Code := .seq (.copy 14 0) (.seq (.whileLt 14 13 emitPair) (.binary .add 13 13 1))

/-- The group-pair array is built without a scan of the packet population. -/
def pass : Code := .seq (.block [.copy 13 0,.copy 15 12]) (.whileLt 13 3 outerStep)

/-- The prefix before beginning outer symbol `t`. -/
structure OuterState (l : Layout) (before : ℕ → ℕ) (t : ℕ) (z : NatState) : Prop where
  /-- Public configuration registers. -/
  ready : l.Ready z
  /-- Outer symbol counter. -/
  outer : z.reg 13 = t
  /-- Free descriptor cursor at the beginning of the new triangular row. -/
  cursor : z.reg 15 = l.rowIndex 0 t
  /-- Actual fields of the emitted symbol pairs. -/
  image : l.Image before (l.rowIndex 0 t) z.mem

private theorem outer_next (l : Layout) (t : ℕ) : l.rowIndex t t = l.rowIndex 0 (t+1) := by
  simp [Layout.rowIndex,choose_succ_two,Nat.add_assoc]

private theorem run_outer {w : ℕ} (pub : Arg → Word w) (macros : TeamOpcode.Macros w 8)
    (l : Layout) (before : ℕ → ℕ) (fit : l.Fits w before) {t : ℕ} (ht : t < l.groups)
    (bank : Bank w) (m : Memory w) (st : OuterState l before t (.ofWords bank m)) :
    BoundedRun pub macros outerStep bank m (3 + l.groups*(loadFields.slots+storeFields.slots+1))
      (OuterState l before (t+1)) := by
  have regs (i : ℕ) (z : NatState) (hi : LoopState l before i t z) :
      z.reg 14 = i ∧ z.reg 13 = t := ⟨hi.inner,hi.outer⟩
  have step (i : ℕ) (hi : i < t) (s : Bank w) (mu : Memory w) (hz : LoopState l before i t (.ofWords s mu)) :=
    run_emitPair pub macros l before fit hi ht s mu hz
  have start := (Code.copy 14 0).runFixed pub macros bank m trivial
  have after (u : Bank w) (mu : Memory w) (hu : LoopState l before t t (.ofWords u mu)) :
      BoundedRun pub macros (.binary .add 13 13 1) u mu 1 (OuterState l before (t+1)) := by
    have one : (u 1).val = 1 := hu.ready 1 (by decide)
    have pos : t+1 < 2^w := by have := fit.groupFit; omega
    have ct : (u 13).val = t := hu.outer
    have code := (Code.binary .add 13 13 1).runFixed pub macros u mu
      (by simpa [Code.fixedSafe,Code.safeReadOnly,addressOpFits,NatState.ofWords,readings,ct,one] using pos)
    apply code.mono le_rfl
    rintro z rfl
    refine ⟨hu.ready.fixed (c := .binary .add 13 13 1) (by decide) _,?_,?_,?_⟩
    · simp (config := {decide := true}) [Code.fixedEval,Code.evalNat,addressOp,NatState.ofWords,readings,ct,one]
    · simpa (config := {decide := true}) [← outer_next,Code.fixedEval,Code.evalNat] using hu.cursor
    · simpa only [← outer_next,Code.fixedEval] using hu.image
  have result := start.seq (b := .seq (.whileLt 14 13 emitPair) (.binary .add 13 13 1))
    (t := (t-0)*(loadFields.slots+storeFields.slots+1)+1+1) (Q := OuterState l before (t+1))
    (fun u mu hu => (run_counted_loop pub macros 14 13 emitPair t _ (fun i z => LoopState l before i t z)
      regs step 0 (Nat.zero_le _) u mu (by
        rw [hu]
        exact ⟨st.ready.fixed (c := .copy 14 0) (by decide) _, st.outer,st.ready 0 (by decide),st.cursor,st.image⟩)).seq after)
  apply result.mono _ fun _ => id
  change 1+((t-0)*(loadFields.slots+storeFields.slots+1)+1+1) ≤ _
  rw [Nat.sub_zero]
  have := Nat.mul_le_mul_right (loadFields.slots+storeFields.slots+1) ht.le
  omega

/-- Native execution appends one seven-word record per unordered distinct symbol pair.
The cost depends quadratically on the alphabet size, independently of the shared width. -/
theorem run_pass {w : ℕ} (pub : Arg → Word w) (macros : TeamOpcode.Macros w 8)
    (l : Layout) (bank : Bank w) (m : Memory w) (fit : l.Fits w (readings m))
    (ready : l.Ready (.ofWords bank m)) :
    BoundedRun pub macros pass bank m (3 + l.groups*(3+l.groups*(loadFields.slots+storeFields.slots+1)+1))
      (OuterState l (readings m) l.groups) := by
  let setup := Code.block [.copy 13 0,.copy 15 12]
  have init := setup.runFixed pub macros bank m (by trivial)
  have regs (i : ℕ) (z : NatState) (hz : OuterState l (readings m) i z) : z.reg 13 = i ∧ z.reg 3 = l.groups :=
    ⟨hz.outer,hz.ready 3 (by decide)⟩
  have hi : l.Image (readings m) (l.rowIndex 0 0) (readings m) := by
    constructor
    · intro t ht s hs hlt
      simp [Layout.rowIndex] at hlt
      omega
    · exact fun _ _ => rfl
  have run := init.seq (b := .whileLt 13 3 outerStep)
    (t := (l.groups-0)*(3+l.groups*(loadFields.slots+storeFields.slots+1)+1)+1)
    (Q := OuterState l (readings m) l.groups) (fun u mu hu =>
      run_counted_loop pub macros 13 3 outerStep l.groups _ (OuterState l (readings m)) regs
        (fun _ ht s m hz => run_outer pub macros l _ fit ht s m hz) 0 (Nat.zero_le _) u mu (by
          rw [hu]
          refine ⟨ready.fixed (c := setup) (by decide) _,?_,?_,hi⟩
          · exact ready 0 (by decide)
          · simpa (config := {decide := true}) [setup,Code.block,Code.fixedEval,Code.evalNat,Layout.rowIndex,Layout.regValue] using ready 12 (by decide)))
  apply run.mono _ fun _ => id
  change 2+((l.groups-0)*_+1) ≤ _
  rw [Nat.sub_zero]
  omega

end Cube.SharedRows

end BorderVNP
end Computability
end OAI
