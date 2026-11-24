import OAI.Computability.VPVNP.RAMTapeSitePostStartup
import OAI.Computability.VPVNP.RAMTapeSitePostSpec

/-!
# Exact path count for the finite site memory pass

The post-pass starts with the raw padded records, the two successor payloads
and the unread sorting suffix. The one fixed table computes the layout and
executes every sort and predecessor check. Both accepting and rejecting
executions halt within the same budget.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RAMTape.SitePost

open BurstRAM RAMLayout RAMSort RAMBoundary Boundary

/-- Prepare and run the sorting stages, then check boundary records and all accumulated flags. -/
def complete : FiniteRoutine Port := prepareSort.followedBy terminal

/-- Step budget covering sorting initialization, all sorting stages, flag tests, and the final
boundary scan. -/
def budget (d e w nflags : ℕ) :=
  SortStartup.cost d (4*2^e) + SortStages.ticks (2+e) d w +
  (nflags + 2*2^(2+e)*(((2+e)+d+1).choose 2) + 4*d + 96*(2^(2+e)+1)*(w+1) + 7)

variable {d e w : ℕ}

/-- At every time above the explicit cutoff, every continuation sees the same
closed decision, and every computation path has halted. -/
theorem complete_spec (hw : 2 ≤ w) (hc : 2^d*2^e<2^w) (b : SendArrays d (2^e) w) (v : Word d)
    (x : SortReplay.State (2+e) w) (hcanon : SortReplay.CanonicalBlock hw x.1) (prev sent : RawSlot w) :
    let m := (unpackMessages (parseMessages hw hc b)).memory
    let start := prestate v prev sent x ((List.ofFn (RAMLayout.incidentBits b v)).drop (16*w))
    let accepts := x.2.all id = true ∧ SortCanonical hw hc b v ∧ MemoryAt m v (SortReplay.decoded hw x.1)
    ∀ (_hp : (parsedSlot hw prev).record = RAMBoundary.receive m.lastRecords v)
      (_hs : v.val+1 < 2^d → (parsedSlot hw sent).record = RAMBoundary.outgoing m.lastRecords v)
      (_hz : v.val = 0 → (recordBytes prev).all (!·) = true)
      (_hl : 2^d ≤ v.val+1 → (recordBytes sent).all (!·) = true)
      (t : ℕ), budget d e w x.2.length ≤ t →
      (∀ c, complete.body.count c t start = @ite ℕ accepts (Classical.propDecidable _) 1 0) ∧
        (∀ c, complete.body.AllStops c t start) := by
  classical
  intro m start accepts hp hs hz hl t ht
  obtain ⟨ticks, hTicks, y, run, hflags, hsort, hout⟩ := prepareSort_messages hw hc b v prev sent x hcanon
  change prepareSort.Runs ticks start (finalBank v prev sent y) at run
  let k := SiteTerminal.steps d w (2^(2+e)) v y.2
  have hterm := SiteTerminal.steps_le d w (2^(2+e)) v y.2
  change k ≤ _ at hterm
  have hcost : ticks + k ≤ t := by
    unfold budget at ht
    omega
  let extra := t - (ticks + k)
  have heq : t = (extra+k)+ticks := by dsimp [extra]; omega
  let ok := decision (decide (0<v.val)) (decide (v.val+1<2^d)) prev sent (List.ofFn y.1) && y.2.all id
  have iff : ok = true ↔ accepts := decision_iff hw hc b v x y prev sent hsort hout hp hs hz hl
  constructor
  · intro c
    change (prepareSort.body.followedBy terminal.body).count c t start = _
    rw [Routine.count_followedBy, heq, run.count_eq]
    exact (terminal_count v prev sent y c extra).trans (by
      change ok.toNat = _
      by_cases h : accepts
      · rw [ite_eq_left h, iff.mpr h]; rfl
      · have hfalse : ok = false := Bool.eq_false_iff.mpr (fun hg => h (iff.mp hg))
        rw [ite_eq_right h, hfalse]; rfl)
  · intro c
    change (prepareSort.body.followedBy terminal.body).AllStops c t start
    rw [Routine.allStops_followedBy, heq, run.allStops_iff]
    exact terminal_total v prev sent y c extra

end RAMTape.SitePost

end VPVNP
end Computability
end OAI
