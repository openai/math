import OAI.Computability.BorderVNP.CubeGroupWeightProgram

/-! # Composing the sparse weight pass with native least-load assignment -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cube.GroupWeights

open RoutingISA VPVNP.BurstRAM VPVNP.BurstRAM.PrivateRAM

/-- The fixed group schedule first computes frame 75, then assigns the groups from it. -/
def schedule : Code := program.seq TeamNative.assignGroupsNative

/-- The final physical arrays of the combined schedule. -/
structure ScheduleResult (l : Layout) (teams : TeamNative.Layout) (orig mem : ℕ → ℕ) : Prop where
  /-- Computed joint weights remain available after team assignment. -/
  weights : ∀ s < l.groups, mem (l.weights+s) = l.weight orig s
  /-- Every team holds the exact result of the greedy traversal of these actual weights. -/
  totals : ∀ j : Fin (teams.r+1), mem (teams.totals+j.val) = TeamNative.loads teams.r (l.weight orig) l.groups j
  /-- Every group has the first minimizing team in public order. -/
  owners : ∀ s < l.groups, mem (teams.owners+s) = (TeamNative.owner teams.r (l.weight orig) s).val
  /-- All addresses outside the three output arrays retain their original word. -/
  other : ∀ a, (∀ s < l.groups, a ≠ l.weights+s) → (∀ j : Fin (teams.r+1), a ≠ teams.totals+j.val) →
    (∀ s < l.groups, a ≠ teams.owners+s) → mem a = orig a

/-- The finite schedule reads the actual symbol rows and deliveries, builds each
joint group weight and writes the first-minimum owners and resulting team totals. -/
theorem run_schedule {w : ℕ} (pub : Arg → Word w) (macros : TeamOpcode.Macros w 8)
    (l : Layout) (teams : TeamNative.Layout) (s : Bank w) (m : Memory w) (hf : readings pub 0 = l.frame)
    (fields : l.Fields (readings m)) (room : l.SetupRoom w) (fit : l.Fits w (readings m))
    (al : teams.Allocated w) (frameFit : l.frame+77 < 2^w)
    (frame : teams.Frame l.frame (readings m)) (hg : teams.groups = l.groups)
    (hw : teams.weights = l.weights)
    (sep : ∀ f ∈ ([1,74,75,76,77] : List ℕ), ∀ i < l.groups, l.frame+f ≠ l.weights+i)
    (hsum : ∑ i ∈ Finset.range l.groups, l.weight (readings m) i < 2^w) :
    BoundedRun pub macros schedule s m (ticks l+TeamNative.assignmentTicks teams)
      (fun z => ScheduleResult l teams (readings m) z.mem) := by
  apply (run_program pub macros l s m hf fields room fit).seq
  intro u mu hu
  change Result l (readings m) (readings mu) at hu
  have tf : teams.Frame (readings pub 0) (readings mu) := by
    rw [hf]
    exact ⟨(hu.outside _ (sep 1 (by decide))).trans frame.teamCount,
      (hu.outside _ (sep 74 (by decide))).trans frame.groupCount,
      (hu.outside _ (sep 75 (by decide))).trans frame.weightBase,
      (hu.outside _ (sep 76 (by decide))).trans frame.totalBase,
      (hu.outside _ (sep 77 (by decide))).trans frame.ownerBase⟩
  have run := TeamNative.run_assignGroupsNative pub macros u mu teams (l.weight (readings m))
    al (hf ▸ frameFit) tf (by rw [hg,hw]; exact hu.weights) (hg ▸ hsum)
  apply run.mono le_rfl
  intro z hz
  obtain ⟨_,ht⟩ := hz
  refine ⟨?_,?_,?_,?_⟩
  · intro i hi
    have hi' : i < teams.groups := hg ▸ hi
    exact (ht.other _ (hw ▸ al.weightsTotals i hi') (hw ▸ al.weightsOwners i hi')).trans (hu.weights i hi)
  · rw [← hg]
    exact ht.totals
  · rw [← hg]
    exact ht.owners
  · intro a ha ht' ho
    exact (ht.other a ht' (hg ▸ ho)).trans (hu.outside a ha)

/-- The histogram and least-load scans are entirely deterministic. -/
theorem schedule_deterministic : schedule.deterministic = true := by decide

end Cube.GroupWeights

end BorderVNP
end Computability
end OAI
