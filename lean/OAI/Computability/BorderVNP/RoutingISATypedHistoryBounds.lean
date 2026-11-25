import OAI.Computability.BorderVNP.RoutingISATypedBudget
import OAI.Computability.BorderVNP.RoutingISACompactPath
import OAI.Computability.BorderVNP.TeamContractionPaths
import OAI.Computability.BorderVNP.RoutingISAOrdinaryCost

/-! # Resource bounds for every chronological prepared cell path

All branch choices are made inside a private clocked table. Each owned row probes
its own published length. Preparing the table adds only ordinary RAM instructions.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.TypedBatch

open VPVNP.BurstRAM CellDispatch CellMacro.Generator CompactMachine

private theorem choice_length {Q : Type*} {d : ℕ} {P : TeamPrivateTape.Table Q d}
    {n q t bs out u} (run : TeamPrivateFragment.Run P n q t bs out u) : bs.length ≤ n := by
  induction run with
  | stop => exact le_rfl
  | one _ _ ih => exact Nat.le_succ_of_le ih
  | two _ _ _ ih => exact Nat.succ_le_succ ih

private theorem scan_bounds {w n : ℕ} (gen : Fragment IO) (routines : TeamOpcode.Macros w 8)
    (f : Frame) (m : Memory w) (cap : ∀ i < f.count, (m (f.address i)).val=f.team →
      (m (f.address i+2)).val ≤ TeamScales.width n (1/2)) (i : ℕ) (xs : List (Option Outcome))
    (span : i+xs.length ≤ f.count) (ad : f.Admitted m (install gen n routines) i xs) :
    ∀ e ∈ f.scanTrace m i xs, e.action.extra ≤ TeamScales.width n (1/2) ∧ e.choices.length ≤ n^25 := by
  induction xs generalizing i with
  | nil => simp [Frame.scanTrace,tick,TeamTranscript.Action.extra]
  | cons x xs ih =>
    obtain ⟨valid,rest⟩ := ad
    have hi : i < f.count := by simp at span; omega
    have tail := ih (i+1) (by simp at span; omega) rest
    have head : ∀ e ∈ f.rowTrace m i x, e.action.extra ≤ TeamScales.width n (1/2) ∧ e.choices.length ≤ n^25 := by
      by_cases own : (m (f.address i)).val = f.team
      · rw [Frame.Valid,ite_eq_left own] at valid
        obtain ⟨o,rfl,_,ok⟩ := valid
        rw [install,Function.update_self] at ok
        obtain ⟨p,hp,_⟩ := (execute_iff_unique_path ..).mp ok
        have b : o.1.length ≤ n^25 := by
          rw [← hp.choices]
          exact (choice_length p.run).trans (time_le_of_lt_nativeClock hp.within)
        simp [Frame.rowTrace,tick,loadEvent,Frame.callEvent,Frame.burst,TeamTranscript.Action.extra,b]
        simpa using cap i hi own
      · have empty : x = none := by simpa [Frame.Valid,own] using valid
        subst x
        simp [Frame.rowTrace,tick,loadEvent,TeamTranscript.Action.extra]
    exact fun e he => (List.mem_append.mp he).elim (head e) (tail e)

/-- The full three-word row scan respects the paper's private clock and per-burst cap.
Its charged ticks depend on the true emitted lengths of this team's tasks. -/
theorem directory_within {w table count n : ℕ} {pub : Arg → Word w} {m : Memory w}
    {tasks : ℕ → Task} {cells : ℕ → CellInput} (gen : Fragment IO) (routines : TeamOpcode.Macros w 8)
    (placed : PlacedRows pub m tasks count n cells)
    (layout : Allocated w table count tasks) (room : ∀ i < count, (tasks i).cell.Room w)
    (control : ControlLayout pub m tasks count) :
    let f := Frame.ofMemory pub m
    let mt := written m tasks count
    ∀ es ∈ f.histories pub mt (choices gen n),
      TeamContraction.Within (17+7*f.count+4*(f.ownedRows mt 0 f.count).length +
        ∑ j ∈ Finset.range count, ((tasks j).cell.burst w).length) (TeamScales.width n (1/2)) (n^25) es := by
  classical
  intro f mt es he
  obtain ⟨xs,hx,rfl⟩ := Finset.mem_image.mp he
  obtain ⟨len,ad⟩ := (Frame.mem_rowProducts (mem_choices gen n routines) ..).mp hx
  have costs := f.directory_charge pub mt (install gen n routines) xs ad
  have all : ∀ e ∈ setupTrace pub mt ++ f.scanTrace mt 0 xs,
      e.action.extra ≤ TeamScales.width n (1/2) ∧ e.choices.length ≤ n^25 := by
    have start : ∀ e ∈ setupTrace pub mt,
        e.action.extra ≤ TeamScales.width n (1/2) ∧ e.choices.length ≤ n^25 := by
      simp [setupTrace,tick,loadEvent,TeamTranscript.Action.extra]
    have scan := scan_bounds gen routines f mt (placed.final_cap layout room control) 0 xs (by omega) ad
    exact fun e he => (List.mem_append.mp he).elim (start e) (scan e)
  refine ⟨?_,fun e he => (all e he).1,fun e he => (all e he).2⟩
  change traceCost _ ≤ _
  rw [costs,len]
  exact Nat.add_le_add_left (placed.total_burst_le layout room control) _

/-- Combining the deterministic typed preparation with every accepted cell history
adds precisely its ordinary-prefix cost to the directory tick allowance. -/
theorem prepared_within {w table count n : ℕ} {pub : Arg → Word w} {m : Memory w}
    {tasks : ℕ → Task} {cells : ℕ → CellInput} (gen : Fragment IO) (routines : TeamOpcode.Macros w 8)
    (placed : PlacedRows pub m tasks count n cells)
    (layout : Allocated w table count tasks) (room : ∀ i < count, (tasks i).cell.Room w)
    (control : ControlLayout pub m tasks count) {s t : Bank w} {pre : List (TeamRAM.Event w)}
    (prep : Runs pub (install gen n routines) entry s m pre t (written m tasks count)) :
    let f := Frame.ofMemory pub m
    let mt := written m tasks count
    ∀ es ∈ CompactBatch.preparedHistories pre f pub mt (choices gen n),
      TeamContraction.Within (traceCost pre + (17+7*f.count+4*(f.ownedRows mt 0 f.count).length +
        ∑ j ∈ Finset.range count, ((tasks j).cell.burst w).length)) (TeamScales.width n (1/2)) (n^25) es := by
  intro f mt es he
  obtain ⟨tail,ht,rfl⟩ := Finset.mem_map.mp he
  have bounded := directory_within gen routines placed layout room control tail ht
  have prefixBound (e : TeamRAM.Event w) (he : e ∈ pre) :
      e.action.extra ≤ TeamScales.width n (1/2) ∧ e.choices.length ≤ n^25 := by
    have p := prep.deterministic_extra (by decide) e he
    have bits := (prep.unsigned_events (by decide) e he).1
    rw [bits]
    exact ⟨by omega,Nat.zero_le _⟩
  change TeamContraction.Within _ _ _ (pre++tail)
  refine ⟨?_,fun e he => (List.mem_append.mp he).elim (fun hp => (prefixBound e hp).1) (bounded.length e),
    fun e he => (List.mem_append.mp he).elim (fun hp => (prefixBound e hp).2) (bounded.choices e)⟩
  rw [VPVNP.RAMBuckets.cost_append]
  exact Nat.add_le_add_left bounded.cost _

end RoutingISA.TypedBatch

end BorderVNP
end Computability
end OAI
