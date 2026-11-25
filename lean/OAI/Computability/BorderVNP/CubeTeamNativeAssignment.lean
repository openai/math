import OAI.Computability.BorderVNP.CubeTeamNativeFrame

/-! # The finite native group assignment pass of Section 8.2

The native pass scans the current team totals, records the selected team and
increments its scaled weight. Its work is linear in the number of groups
times the number of teams.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cube.TeamNative

open RoutingISA VPVNP.BurstRAM VPVNP.BurstRAM.PrivateRAM

/-- Commit one owner and its increased load, then advance the group cursor. -/
def commitGroup : Code := .block [
  .binary .add 14 5 8, .load 15 14, .binary .add 16 11 15,
  .binary .add 17 7 8, .store 17 10, .binary .add 18 6 10, .store 18 16,
  .binary .add 8 8 1]

/-- Process all groups in numeric symbol order. -/
def assignmentLoop : Code := .seq (.copy 8 0) (.whileLt 8 4 (teamMinimum.seq commitGroup))

/-- Section 8.2's native frame read, team initialization, and group traversal. -/
def assignGroupsNative : Code := loadTeamLayout.seq (clearTotals.seq assignmentLoop)

/-- Total tick bound, including the setup and both terminating guards. -/
def assignmentTicks (l : Layout) : ℕ :=
  loadTeamLayout.slots + (4*(l.r+1)+2 + (l.groups*(12*(l.r+1)+9)+2))

private theorem run_commitGroup {w : ℕ} (pub : Arg → Word w) (macros : TeamOpcode.Macros w 8)
    (s : Bank w) (m : Memory w) (l : Layout) (ws orig : ℕ → ℕ) (k : ℕ) (hk : k < l.groups)
    (al : l.Allocated w) (hr : l.Ready (.ofWords s m)) (t : Tables l ws orig k (readings m))
    (h8 : readings s 8 = k) (h10 : readings s 10 = (owner l.r ws k).val)
    (h11 : readings s 11 = loads l.r ws k (owner l.r ws k))
    (hw : orig (l.weights+k) = ws k) (hsum : ∑ i ∈ Finset.range l.groups, ws i < 2^w) :
    BoundedRun pub macros commitGroup s m 8 (fun z =>
      l.Ready z ∧ z.reg 8 = k+1 ∧ Tables l ws orig (k+1) z.mem) := by
  let z := NatState.ofWords s m
  let j := owner l.r ws k
  have h1 : z.reg 1 = 1 := hr.oneReg
  have h5 : z.reg 5 = l.weights := hr.weightBase
  have h6 : z.reg 6 = l.totals := hr.totalBase
  have h7 : z.reg 7 = l.owners := hr.ownerBase
  change z.reg 8 = k at h8
  change z.reg 10 = j.val at h10
  change z.reg 11 = loads l.r ws k j at h11
  have hread : z.mem (l.weights+k) = ws k :=
    (t.other _ (al.weightsTotals k hk) (al.weightsOwners k hk)).trans hw
  have hweight := al.weightsFit k hk
  have howner := al.ownersFit k hk
  have htotal := al.totalsFit j
  have inc : k+1 < 2^w := Nat.lt_of_le_of_lt hk (hr.groupCount ▸ (s 4).isLt)
  have hsum' : loads l.r ws k j + ws k < 2^w := by
    apply lt_of_le_of_lt _ hsum
    apply (Nat.add_le_add_right (loads_le _ _ _ _) _).trans
    rw [← Finset.sum_range_succ]
    exact Finset.sum_le_sum_of_subset (Finset.range_mono hk)
  have safe : commitGroup.fixedSafe w (readings pub) z := by
    simp (config := {decide := true}) [commitGroup,Code.block,Code.fixedSafe,Code.fixedEval,
      Code.safeReadOnly,Code.evalNat,addressOp,addressOpFits,h1,h5,h6,h7,h8,h10,h11,hread,
      inc,hweight,howner,htotal,hsum']
  apply (commitGroup.runFixed pub macros s m safe).mono (by decide)
  rintro y rfl
  refine ⟨hr.congr (fun a ha => commitGroup.fixedEval_protected _ _ (by decide) a ha), ?_, ?_⟩
  · change (commitGroup.fixedEval _ z).reg 8 = k+1
    simp (config := {decide := true}) [commitGroup,Code.block,Code.fixedEval,Code.evalNat,
      addressOp,h1,h8]
  · change Tables l ws orig (k+1) (commitGroup.fixedEval _ z).mem
    convert t.commit al hk using 1
    simp (config := {decide := true}) [commitGroup,Code.block,Code.fixedEval,Code.evalNat,
      addressOp,h5,h6,h7,h8,h10,h11,hread,commitWords,j]
    rfl

/-- The loop consumes a linearly bounded minimum scan per group and returns all
actual owners and loads while preserving every other word. -/
theorem run_assignmentLoop {w : ℕ} (pub : Arg → Word w) (macros : TeamOpcode.Macros w 8)
    (s : Bank w) (m : Memory w) (l : Layout) (ws orig : ℕ → ℕ) (al : l.Allocated w)
    (ready : l.Ready (.ofWords s m)) (initial : Tables l ws orig 0 (readings m))
    (hw : ∀ i < l.groups, orig (l.weights+i) = ws i)
    (hsum : ∑ i ∈ Finset.range l.groups, ws i < 2^w) :
    BoundedRun pub macros assignmentLoop s m (l.groups*(12*(l.r+1)+9)+2)
      (fun z => l.Ready z ∧ Tables l ws orig l.groups z.mem) := by
  let b := teamMinimum.seq commitGroup
  let cost := 12*(l.r+1)+8
  let P (i : ℕ) (z : NatState) := l.Ready z ∧ z.reg 8 = i ∧ Tables l ws orig i z.mem
  have regs (i : ℕ) (z : NatState) (h : P i z) : z.reg 8 = i ∧ z.reg 4 = l.groups :=
    ⟨h.2.1,h.1.groupCount⟩
  have step (i : ℕ) (hi : i < l.groups) (u : Bank w) (mu : Memory w)
      (h : P i (.ofWords u mu)) : BoundedRun pub macros b u mu cost (P (i+1)) := by
    have run := run_teamMinimum pub macros u mu l.totals (loads l.r ws i)
      h.1.zeroReg h.1.oneReg h.1.teamCount h.1.totalBase h.2.2.totals al.totalsFit
    apply run.seq
    rintro v mv ⟨hp,hm,h10,h11⟩
    change readings mv = readings mu at hm
    exact run_commitGroup pub macros v mv l ws orig i hi al (h.1.congr fun a ha =>
      hp a (by omega)) (by rw [hm]; exact h.2.2) ((hp 8 (by decide)).trans h.2.1)
      h10 h11 (hw i hi) hsum
  have run := ((Code.copy 8 0).runFixed pub macros s m trivial).seq (b := .whileLt 8 4 b)
    (t := (l.groups-0)*(cost+1)+1) (Q := P l.groups) (fun u mu hu =>
    run_counted_loop pub macros 8 4 b l.groups cost P regs step 0 (by omega) u mu (by
      rw [hu]
      refine ⟨ready.congr (fun j hj => Code.fixedEval_protected _ _ _ (by decide) j hj), ?_, initial⟩
      simpa [Code.fixedEval,Code.evalNat] using ready.zeroReg))
  exact run.mono (by
    change 1+(l.groups-0)*(12*(l.r+1)+8+1)+1 ≤ _
    rw [Nat.sub_zero, show 12*(l.r+1)+8+1 = 12*(l.r+1)+9 by omega]
    omega)
    fun _ h => ⟨h.1,h.2.2⟩

/-- The full native program from a physical input frame. It implements the public
group assignment for every admissible word array, including an empty group list. -/
theorem run_assignGroupsNative {w : ℕ} (pub : Arg → Word w) (macros : TeamOpcode.Macros w 8)
    (s : Bank w) (m : Memory w) (l : Layout) (ws : ℕ → ℕ) (al : l.Allocated w)
    (fit : readings pub 0+77 < 2^w) (frame : l.Frame (readings pub 0) (readings m))
    (hw : ∀ i < l.groups, readings m (l.weights+i) = ws i)
    (hsum : ∑ i ∈ Finset.range l.groups, ws i < 2^w) :
    BoundedRun pub macros assignGroupsNative s m (assignmentTicks l)
      (fun z => l.Ready z ∧ Tables l ws (readings m) l.groups z.mem) := by
  apply (run_loadTeamLayout pub macros s m l fit frame).seq
  rintro u mu ⟨hr,hm⟩
  apply (run_clearTotals pub macros u mu l ws al hr).seq
  rintro v mv ⟨hr',ht⟩
  change readings mu = readings m at hm
  rw [hm] at ht
  exact run_assignmentLoop pub macros v mv l ws (readings m) al hr' ht hw hsum

end Cube.TeamNative

end BorderVNP
end Computability
end OAI
