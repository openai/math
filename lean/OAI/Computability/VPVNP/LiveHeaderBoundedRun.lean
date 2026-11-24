import OAI.Computability.VPVNP.LiveHeaderBounded
import OAI.Computability.VPVNP.PrimedScheduleRAM
import OAI.Computability.VPVNP.RAMRecords
import Mathlib.Data.ZMod.Defs

/-!
# Completing a bounded native stage

The active calls preserve all source choices and memory effects. A single
extra empty choice list acknowledges the end cursor and produces the
accepting report seen by the linker.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace LiveHeaderBounded

open BurstRAM BurstRAM.PrivateRAM
open scoped Fin.CommRing

variable {w p r k : ℕ}

/-- An active worker's report with the three local cursor-bound instructions prepended. -/
def activeReport (rep : Report w) : Report w := ⟨.tick :: .tick :: .tick :: rep.events, rep.result⟩

/-- The terminal report of the bound check, accepting after its three local instructions. -/
def closedReport (w : ℕ) : Report w := ⟨[.tick,.tick,.tick], none⟩

@[simp] theorem activeReport_probes (rep : Report w) : (activeReport rep).probes = rep.probes := rfl

@[simp] theorem closedReport_probes : (closedReport w).probes = 0 := rfl

@[simp] theorem activeReport_after (m : Memory w) (rep : Report w) :
    after m (activeReport rep).events = after m rep.events := rfl

@[simp] theorem activeReport_choiceBits (rep : Report w) : choiceBits (activeReport rep).events = choiceBits rep.events := rfl

/-- Every source call begins with an active cursor. The result of the last
call may be the bound itself. -/
def Active (bound : Word w) : Option (Word w) → List (Report w) → Prop
  | _, [] => True
  | none, _ :: _ => False
  | some st, x :: xs => st < bound ∧ Active bound x.result xs

theorem endState_activeReports (s : Option (Word w)) (rs : List (Report w)) :
    endState s (rs.map activeReport) = endState s rs := by
  induction rs generalizing s with
  | nil => rfl
  | cons r rs ih => exact ih r.result

theorem after_activeReports (m : Memory w) (rs : List (Report w)) :
    after m (eventLog (rs.map activeReport)) = after m (eventLog rs) := by
  induction rs generalizing m with
  | nil => rfl
  | cons r rs ih =>
    simpa only [eventLog, List.map_cons, List.flatMap_cons, after, List.foldl_append,
      activeReport, List.foldl_cons, update] using ih (after m r.events)

variable (T : Template p r k) (pub : Fin k → Word w) (bound : Word w)

/-- Exact trace equivalence for all the calls below the bound. -/
theorem runSegment_active_iff (fuel : ℕ) (s : Option (Word w)) (m : Memory w)
    (bs : List (List Bool)) (rs : List (Report w)) (h : Active bound s rs) :
    runSegment (machine T pub bound).program (fuel+3) s m bs = some (rs.map activeReport) ↔
    runSegment (T.instantiate w pub).program fuel s m bs = some rs := by
  induction bs generalizing s m rs with
  | nil => cases rs <;> simp [runSegment]
  | cons bits bs ih =>
    cases s with
    | none => simp [runSegment]
    | some st =>
      cases rs with
      | nil =>
        simp only [List.map_nil, runSegment]
        cases execute (machine T pub bound).program (fuel+3) ((machine T pub bound).program.start st) m bits <;>
          cases execute (T.instantiate w pub).program fuel ((T.instantiate w pub).program.start st) m bits <;>
          simp [Option.map_eq_some_iff]
      | cons r rs =>
        obtain ⟨hlt, hrest⟩ := h
        simp only [List.map_cons, runSegment, execute_active T pub bound fuel st hlt]
        cases he : execute (T.instantiate w pub).program fuel ((T.instantiate w pub).program.start st) m bits with
        | none => simp
        | some t =>
          change ((runSegment _ _ t.result (after m t.events) bs).map (activeReport t :: ·)) = _ ↔
            ((runSegment _ _ t.result (after m t.events) bs).map (t :: ·)) = _
          by_cases htr : t = r
          · subst t
            simpa only [Option.map_eq_some_iff, List.cons.injEq, true_and, exists_eq_right] using
              ih r.result (after m r.events) rs hrest
          · have hwrapped : activeReport t ≠ activeReport r := by
              intro hEq
              cases t with | mk es out => cases r with | mk fs val =>
                simp [activeReport] at hEq
                exact htr (by simp [hEq])
            simp [Option.map_eq_some_iff, htr, hwrapped]

/-- Append the closing call to a successful active segment. -/
theorem runSegment_complete {fuel : ℕ} (hfuel : 0 < fuel) (s : Option (Word w)) (m : Memory w)
    (bs : List (List Bool)) (rs : List (Report w)) (st : Word w) (h : Active bound s rs)
    (hsource : runSegment (T.instantiate w pub).program fuel s m bs = some rs)
    (hend : endState s rs = some st) (hclosed : bound ≤ st) :
    runSegment (machine T pub bound).program (fuel+3) s m (bs ++ [[]]) =
      some (rs.map activeReport ++ [closedReport w]) := by
  have ha := (runSegment_active_iff T pub bound fuel s m bs rs h).mpr hsource
  rw [PrimedSchedule.runSegment_append, ha]
  simp only [Option.bind_some, endState_activeReports, hend, runSegment]
  have hc := execute_closed T pub bound (fuel-1) st hclosed (after m (eventLog (rs.map activeReport))) []
  rw [show fuel-1+4 = fuel+3 by omega] at hc
  simp only [ite_true] at hc
  rw [hc]
  rfl

/-- For a table advancing its cursor by one on every successful call, every
prefix of an in-bounds source scan satisfies the guard. -/
theorem active_of_cursor_run (fuel start : ℕ) (m : Memory w)
    (bs : List (List Bool)) (rs : List (Report w)) (hsize : start + bs.length ≤ bound.val)
    (hrun : runSegment (T.instantiate w pub).program fuel (some (start : Word w)) m bs = some rs)
    (hnext : ∀ i < bound.val, ∀ mem bits rep,
      execute (T.instantiate w pub).program fuel ((T.instantiate w pub).program.start (i : Word w)) mem bits = some rep →
        rep.result = some ((i+1 : ℕ) : Word w)) :
    Active bound (some (start : Word w)) rs ∧
      endState (some (start : Word w)) rs = some ((start+bs.length : ℕ) : Word w) := by
  induction bs generalizing start m rs with
  | nil =>
    simp only [runSegment, Option.some.injEq] at hrun
    subst rs
    simp [Active, endState]
  | cons bits bs ih =>
    have hi : start < bound.val := by simp only [List.length_cons] at hsize; omega
    have hword : (start : Word w) < bound := by
      change start % (2^w) < bound.val
      rwa [Nat.mod_eq_of_lt (hi.trans bound.isLt)]
    simp only [runSegment] at hrun
    cases he : execute (T.instantiate w pub).program fuel
        ((T.instantiate w pub).program.start (start : Word w)) m bits with
    | none => simp [he] at hrun
    | some r =>
      simp only [he, Option.map_eq_some_iff] at hrun
      obtain ⟨rest, htail, rfl⟩ := hrun
      have hres := hnext start hi m bits r he
      rw [hres] at htail
      obtain ⟨ha, hs⟩ := ih (start+1) (after m r.events) rest
        (by simp only [List.length_cons] at hsize; omega) htail
      refine ⟨⟨hword, hres ▸ ha⟩, ?_⟩
      simpa only [endState, hres, List.length_cons, Nat.add_right_comm start 1 bs.length, Nat.add_assoc] using hs

/-- Finish a complete cursor scan without requiring a separate prefix proof
for its concrete report list. -/
theorem runSegment_cursor_complete {fuel : ℕ} (hfuel : 0 < fuel) (start : ℕ) (m : Memory w)
    (bs : List (List Bool)) (rs : List (Report w)) (hsize : start + bs.length = bound.val)
    (hrun : runSegment (T.instantiate w pub).program fuel (some (start : Word w)) m bs = some rs)
    (hnext : ∀ i < bound.val, ∀ mem bits rep,
      execute (T.instantiate w pub).program fuel ((T.instantiate w pub).program.start (i : Word w)) mem bits = some rep →
        rep.result = some ((i+1 : ℕ) : Word w)) :
    runSegment (machine T pub bound).program (fuel+3) (some (start : Word w)) m (bs ++ [[]]) =
      some (rs.map activeReport ++ [closedReport w]) := by
  obtain ⟨ha, hs⟩ := active_of_cursor_run T pub bound fuel start m bs rs hsize.le hrun hnext
  have hcast : (bound.val : Word w) = bound := Fin.ext (Nat.mod_eq_of_lt bound.isLt)
  rw [hsize, hcast] at hs
  exact runSegment_complete T pub bound hfuel _ m bs rs bound ha hrun hs le_rfl

end LiveHeaderBounded

end VPVNP
end Computability
end OAI
