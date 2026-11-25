import OAI.Computability.NearSquareRoot.CRTPositionRowCommandRun
import OAI.Computability.NearSquareRoot.CRTPositionEffectiveTable

/-! # Unrestricted correctness of the generated high-row command

A finite physical row stream admits a common step clock even when its size
does not pay the fast space bound. Both the fast and unrestricted contracts
refer to the identical scan and the identical grouped callback.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Controlled.PositionRows.RowCommand
open IntegerMultiplication Code Adic Strip Loom Window.Packets PositionProgram
open NearSquareRoot.Space

noncomputable section

/-- Total correctness on the actual grouped table packets, allowing any finite
clock on each full row. -/
def RawGroupedRuns (core : Cmd) : Prop :=
  ∃ t : Window.Row → ℕ, EffectiveTask.Runs core t RowCommandLow.middleInput RowCommandLow.groupedOut

theorem rawGroupedOfPointwise {core : Cmd}
    (run : ∀ z : Window.Row, ∃ t : ℕ, ∀ env,
      Fits.value env core 0 (RowCommandLow.middleInput z) (RowCommandLow.groupedOut z) t) :
    RawGroupedRuns core := by
  choose t h using run
  exact ⟨t,1,fun z env r => (h z env r).mono (by omega)⟩

/-- The slack-bearing table theorem runs even on a single short low record. -/
theorem rawGroupedTable {c : Cmd} {ρ : ℝ} (positive : 0 ≤ ρ) (dispatch : OpAt c ρ id) :
    RawGroupedRuns (tableCmd c) := by
  obtain ⟨d,uniform⟩ := tableCmd_runs positive dispatch
  have run := uniform (fun z : Window.Row => z.1.mid) (fun z => z.1.perm.symm)
    RowCommandLow.wide RowCommandLow.data
  refine ⟨fun z => ⌈tableRate ρ z.1.mid ((RowCommandLow.wide z).count+(z.1.mid+1)^d)⌉₊,?_⟩
  rw [RowCommandLow.middleInput,RowCommandLow.groupedIn_eq,RowCommandLow.groupedOut_eq]
  exact run

private theorem rawScan {I : Type} {A : I → Type} (s : (i : I) → Series (A i))
    (positive : ∀ i, 0 < (s i).count) (src dst : (i : I) → A i → Tree)
    (cmd : Cmd) (t : Sigma A → ℕ)
    (run : EffectiveTask.Runs cmd t (fun z => src z.1 z.2) (fun z => dst z.1 z.2)) :
    ∃ T S : I → ℕ, EffectiveBoundedTask.Runs (RowCommandScan.scanCmd cmd) T S
      (fun i => stripe (s i) (src i)) (fun i => stripe (s i) (dst i)) := by
  let W i := ((s i).explore.map (fun a => t ⟨i,a⟩)).sum
  let V i := (stripe (s i) (src i)).count + (stripe (s i) (dst i)).count + (s i).count * W i
  have hrow (z : Sigma A) : t z ≤ W z.1 := List.le_sum_of_mem <|
    List.mem_map.mpr ⟨z.2,(s z.1).complete z.2,rfl⟩
  refine ⟨_,_,RowCommandScan.seriesRows cmd s src dst W V (fun _ => 1)
    (run.bound 1 (fun z => by simpa using hrow z)) 1 ?_ ?_ ?_ positive⟩
  all_goals intro i; dsimp only [V]; omega

/-- The full window task terminates for every well-formed split, including
widths below either cutoff of the fast estimate. -/
theorem rawWindow (core : Cmd) (grouped : RawGroupedRuns core) :
    ∃ t s : Window → ℕ, EffectiveBoundedTask.Runs (command core) t s
      (fun x => .fork (Window.regime.header x) (flat x)) result := by
  obtain ⟨t,h⟩ := grouped
  have framed := RowCommandLow.frame_runs_all id core t h
  obtain ⟨clock,space,scan⟩ := rawScan (fun x : Window => line 2 x.hi)
    (fun x => by rw [lineSize]; exact Nat.two_pow_pos _) (fun x a => rowIn ⟨x,a⟩) (fun x a => rowOut ⟨x,a⟩)
    (RowCommandLow.frameCmd core) _ framed
  exact ⟨_,_,PhysicalWalsh.AgendaOps.compose (PhysicalWalsh.AgendaOps.compose allRuns.1 scan) allRuns.2⟩

/-- Restore an arbitrary native payload series at the public table interface.
The positive payload and the range split are the structural hypotheses. -/
theorem rawTableMiddle (core : Cmd) (grouped : RawGroupedRuns core) {I : Type}
    (k lo hi : I → ℕ) (fit : ∀ i, lo i+hi i ≤ k i)
    {U : I → Type} (u : (i : I) → Series (U i)) (pos : ∀ i, 0 < (u i).count)
    (q : (i : I) → Equiv.Perm (Fin (k i-lo i-hi i)))
    (f : (i : I) → Block 2 (k i) → U i → Bead) :
    ∃ t s : I → ℕ, EffectiveBoundedTask.Runs (command core) t s
      (fun i => .fork (send (tally (hi i),tally (k i-lo i-hi i),tally (lo i),Reflections.table (q i)))
        (cloth (fun i => line 2 (k i)) u f i))
      (cloth (fun i => line 2 (k i)) u (fun i a => f i (ReserveTile.lift (fit i) (flatBitPullback (q i)) a))) := by
  obtain ⟨t,s,run⟩ := rawWindow core grouped
  let pick i : Window := ⟨k i,lo i,hi i,(u i).count,pos i,fit i,q i,fun z j => f i z ((u i).follow j)⟩
  have cell (i) (a : Block 2 (k i)) : cells (pick i) a = strip (u i) (f i a) :=
    stripe_natural_follow (u i) (fun j => send (f i a j))
  refine ⟨_,_,PhysicalWalsh.AgendaOps.conform (run.on pick) (fun _ => rfl) (fun _ => rfl) ?_ ?_⟩
  · intro i
    exact congrArg (Tree.fork _) (congrArg (stripe _) (funext (cell i)))
  · intro i
    exact congrArg (stripe _) (funext (fun a => cell i ((pick i).routed a)))

end
end Controlled.PositionRows.RowCommand

end NearSquareRoot
end Computability
end OAI
