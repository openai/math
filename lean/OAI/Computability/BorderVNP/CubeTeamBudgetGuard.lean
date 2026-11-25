import OAI.Computability.BorderVNP.CubeTeamBudgetFrame

/-! # Exact native rejection of team schedules exceeding their physical budgets -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cube.TeamBudget

open RoutingISA VPVNP.BurstRAM VPVNP.BurstRAM.PrivateRAM

/-- After testing the current word against both limits, subtract it from the
remaining aggregate allowance and advance to the next team. -/
def row : Code := .block [.binary .add 21 3 0,.load 22 21,
  .ifLt 4 22 .reject (.ifLt 5 22 .reject (.block [.binary .sub 5 5 22,.binary .add 0 0 1]))]

/-- Public, memory-preserving check of all the actual team totals. -/
def check : Code := setup.seq (.whileLt 0 2 row)

/-- Both capacity checks of Section 8.2 in scaled integer units. -/
def Layout.Passes (l : Layout) (m : ℕ → ℕ) : Prop :=
  (∀ i < l.teams, m (l.totals+i) ≤ l.teamLimit) ∧ l.prefix m l.teams ≤ l.totalLimit

private theorem prefix_good {l : Layout} {m : ℕ → ℕ} :
    (∀ i, 0 ≤ i → i < l.teams →
      m (l.totals+i) ≤ l.teamLimit ∧ l.prefix m (i+1) ≤ l.totalLimit) ↔ l.Passes m := by
  constructor
  · intro h
    refine ⟨fun i hi => (h i (by omega) hi).1, ?_⟩
    cases he : l.teams with
    | zero => simp [Layout.prefix]
    | succ r => exact (h r (by omega) (by omega)).2
  · rintro ⟨h,hs⟩ i _ hi
    exact ⟨h i hi,(Finset.sum_le_sum_of_subset (Finset.range_mono hi)).trans hs⟩

private theorem row_test {w : ℕ} (pub : Arg → Word w) (macros : TeamOpcode.Macros w 8)
    (l : Layout) (m : ℕ → ℕ) (frame : ℕ) (fit : l.Fits frame w) (i : ℕ) (hi : i < l.teams)
    (s : Bank w) (mu : Memory w) (h : Prefix l m i (.ofWords s mu)) :
    TestRun pub macros row s mu row.slots
      (m (l.totals+i) ≤ l.teamLimit ∧ l.prefix m (i+1) ≤ l.totalLimit) (Prefix l m (i+1)) := by
  let ok := m (l.totals+i) ≤ l.teamLimit ∧ l.prefix m (i+1) ≤ l.totalLimit
  have r0 : readings s 0 = i := h.cursor
  have r1 : readings s 1 = 1 := h.one
  have r2 : readings s 2 = l.teams := h.teams
  have r3 : readings s 3 = l.totals := h.totals
  have r4 : readings s 4 = l.teamLimit := h.limit
  have r5 : readings s 5 = l.totalLimit-l.prefix m i := h.remaining
  have hm : readings mu = m := h.mem
  have inc : i+1 < 2^w := Nat.lt_of_le_of_lt hi (h.teams ▸ (s 2).isLt)
  have addr := fit.address i hi
  have old := h.within
  have next : l.prefix m (i+1) = l.prefix m i + m (l.totals+i) := Finset.sum_range_succ ..
  have res : TestRun pub macros row s mu row.slots ok (fun z => ok → Prefix l m (i+1) z) := by
    apply CubeLengths.readTest _ _ _ _ _ (by decide)
    · by_cases hp : l.teamLimit < m (l.totals+i) <;>
        by_cases ha : l.totalLimit-l.prefix m i < m (l.totals+i) <;>
        simp (config := {decide := true}) [row,Code.block,Code.relaxReject,Code.safeReadOnly,Code.evalNat,
          addressOp,addressOpFits,r0,r1,r3,r4,r5,hm,addr,inc,hp,ha]
      omega
    · by_cases hp : l.teamLimit < m (l.totals+i) <;>
        by_cases ha : l.totalLimit-l.prefix m i < m (l.totals+i) <;>
        simp (config := {decide := true}) [row,Code.block,Code.safeReadOnly,Code.evalNat,
          addressOp,addressOpFits,r0,r1,r3,r4,r5,hm,addr,inc,hp,ha,ok,next] <;> omega
    · rintro ⟨hp,ha⟩
      have hper := not_lt.mpr hp
      have hrem : ¬ l.totalLimit-l.prefix m i < m (l.totals+i) := by omega
      constructor <;>
        simp (config := {decide := true}) [row,Code.block,Code.evalNat,addressOp,r0,r1,r2,r3,r4,r5,hm,
          hper,hrem,next] <;> omega
  exact ⟨fun good => (res.complete good).mono le_rfl (fun _ h' => h' good),fun r =>
    ⟨(res.sound r).1, (res.sound r).2 (res.sound r).1⟩⟩

/-- The check returns exactly for arrays satisfying the individual and aggregate
limits. A malformed word can be rejected before any budget subtraction. -/
theorem check_test {w : ℕ} (pub : Arg → Word w) (macros : TeamOpcode.Macros w 8)
    (l : Layout) (s : Bank w) (m : Memory w)
    (fields : l.Fields (readings pub 0) (readings m)) (fit : l.Fits (readings pub 0) w) :
    TestRun pub macros check s m (setup.slots+l.teams*(row.slots+1)+1) (l.Passes (readings m))
      (fun z => z.mem = readings m) := by
  let I := Prefix l (readings m)
  let good i := readings m (l.totals+i) ≤ l.teamLimit ∧ l.prefix (readings m) (i+1) ≤ l.totalLimit
  have regs (i : ℕ) (z : NatState) (h : I i z) : z.reg 0 = i ∧ z.reg 2 = l.teams :=
    ⟨h.cursor,h.teams⟩
  have step (i : ℕ) (hi : i < l.teams) (u : Bank w) (mu : Memory w)
      (h : I i (.ofWords u mu)) : TestRun pub macros row u mu row.slots (good i) (I (i+1)) :=
    row_test pub macros l (readings m) _ fit i hi u mu h
  have start := (run_setup pub macros l s m fields fit).asTest (by decide)
  apply (start.seq fun u mu hz => test_counted_loop 0 2 row l.teams (fun _ => row.slots)
    good I regs step 0 (Nat.zero_le _) u mu hz).mono
  · simp [Finset.sum_const,Nat.add_assoc]
  · simpa only [true_and] using (show True ∧ (∀ i, 0 ≤ i → i < l.teams → good i) ↔ _ by
      rw [true_and]; exact prefix_good)
  · exact fun _ hz => hz.mem

/-- The reflected check uses the paper's rational limits on actual word totals. -/
theorem Layout.passes_iff_rational (l : Layout) (m : ℕ → ℕ) :
    l.Passes m ↔ (∀ i < l.teams, TeamNative.unscale (m (l.totals+i)) ≤ (l.X₀ : ℚ)/256) ∧
      TeamNative.unscale (l.prefix m l.teams) ≤ (l.X₀ : ℚ)*l.teams/1024 := by
  simp only [Layout.Passes,l.le_teamLimit,l.le_totalLimit]

end Cube.TeamBudget

end BorderVNP
end Computability
end OAI
