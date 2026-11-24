import OAI.Computability.VPVNP.PairSimulationTerminalReports

/-!
# Projecting a native terminal call onto its original worker

The linked table spends the entry trace before the worker and, when needed,
writes the two header cells after the worker. A successful call determines
the worker's native report at the remaining cap, including the same choice
stream. Conversely a worker run with room for the controller yields exactly
the linked report.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.TerminalLink

open BurstRAM PrivateRAM LiveProgram

variable {w : ℕ}
variable (workers : Stage → PairTable) (pub : Fin 11 → Word w)

/-- Execute one original worker with the common eleven public operands. -/
abbrev source (workers : Stage → PairTable) (s : Stage) (pub : Fin 11 → Word w) :=
  ((workers s).table.instantiate w pub).program

/-- The full linked RAM program instantiated with the same public operands. -/
abbrev program := ((table workers).table.instantiate w pub).program

/-- Projected execution at the cap left by the entry prefix. Its exit fits
exactly when the worker's report and the optional header writes fit. -/
def localCall (cap : ℕ) (e : Entry w) (m : Memory w) (bs : List Bool) : Option (Report w) :=
  let addr := header pub
  let fuel := cap - (e.prefixEvents addr).length
  let S := source workers e.stage pub
  ((execute S fuel (S.start e.state) m bs).bind (boundedExit addr e.stage fuel)).map
    (LiveStageLink.prependLog (e.prefixEvents addr))

private theorem execute_original (s : Stage) (f : ℕ) (state : Word w) (m : Memory w) (bs : List Bool) :
    let L := ((component workers s).instantiate w pub).program
    let S := source workers s pub
    execute L f (L.start state) m bs = execute S f (S.start state) m bs :=
  LiveStageLink.execute_widen_start (workers s).table (embedding workers s) id pub f state m bs

private theorem execute_prefix (e : Entry w) (f : ℕ) (m : Memory w) (bs : List Bool)
    (hfit : 5 ≤ 2^w) (valid : e.Valid (header pub) m) :
    let L := program workers pub
    let S := source workers e.stage pub
    let es := e.prefixEvents (header pub)
    execute L (f+es.length) (L.start e.marker) m bs =
      ((execute S f (S.start e.state) m bs).bind (boundedExit (header pub) e.stage f)).map
        (LiveStageLink.prependLog es) := by
  change execute (machine (component workers) pub).program (f+(e.prefixEvents (header pub)).length)
    ((machine (component workers) pub).program.start e.marker) m bs = _
  cases e with
  | initial =>
    simp only [Entry.prefixEvents,Entry.marker,Entry.stage,Entry.state]
    rw [enter_initial (component workers) pub,execute_body,execute_original]
  | resume s x =>
    simp only [Entry.prefixEvents,Entry.marker,Entry.stage,Entry.state]
    rw [enter_resume (component workers) pub s hfit x f m valid.1 valid.2 bs,execute_body,execute_original]

/-- Every choice stream has the same outcome as the original worker followed
by the bounded exit, with the entry events prepended. -/
theorem execute_entry (cap : ℕ) (e : Entry w) (m : Memory w) (bs : List Bool)
    (hfit : 5 ≤ 2^w) (hcap : 26 ≤ cap) (valid : e.Valid (header pub) m) :
    let L := program workers pub
    execute L cap (L.start e.marker) m bs = localCall workers pub cap e m bs := by
  have hp := (prefix_length_le (header pub) e).trans hcap
  simpa only [Nat.sub_add_cancel hp,localCall] using
    execute_prefix workers pub e (cap-(e.prefixEvents (header pub)).length) m bs hfit valid

/-- Invert a successful call into its actual worker report, its exact cap
test and its complete controller trace. -/
theorem recover_call (cap : ℕ) (e : Entry w) (m : Memory w) (bs : List Bool)
    (hfit : 5 ≤ 2^w) (hcap : 26 ≤ cap) (valid : e.Valid (header pub) m) (out : Report w) :
    let L := program workers pub
    let S := source workers e.stage pub
    let f := cap - (e.prefixEvents (header pub)).length
    execute L cap (L.start e.marker) m bs = some out ↔
      ∃ raw, execute S f (S.start e.state) m bs = some raw ∧
        (exitReport (header pub) e.stage raw).events.length < f ∧ out = report (header pub) e raw := by
  dsimp only
  rw [execute_entry workers pub cap e m bs hfit hcap valid]
  unfold localCall
  dsimp only
  cases hr : execute (source workers e.stage pub) (cap - (e.prefixEvents (header pub)).length)
    ((source workers e.stage pub).start e.state) m bs with
  | none => simp
  | some raw =>
    by_cases hf : (exitReport (header pub) e.stage raw).events.length < cap - (e.prefixEvents (header pub)).length
    · simp [boundedExit,hf,report,eq_comm]
    · simp [boundedExit,hf]

/-- Attach the genuine prefix and exit to a worker execution that passes
the exact exit-cap test. -/
theorem call_ok (cap : ℕ) (e : Entry w) (m : Memory w) (bs : List Bool)
    (hfit : 5 ≤ 2^w) (hcap : 26 ≤ cap) (valid : e.Valid (header pub) m) (raw : Report w)
    (hr : execute (source workers e.stage pub) (cap - (e.prefixEvents (header pub)).length)
      ((source workers e.stage pub).start e.state) m bs = some raw)
    (hf : (exitReport (header pub) e.stage raw).events.length < cap - (e.prefixEvents (header pub)).length) :
    let L := program workers pub
    execute L cap (L.start e.marker) m bs = some (report (header pub) e raw) :=
  (recover_call workers pub cap e m bs hfit hcap valid _).mpr ⟨raw,hr,hf,rfl⟩

/-- Thirty spare dispatches suffice uniformly for a successful worker, including
all five comparisons and a continuing exit. -/
theorem call_of_room (cap : ℕ) (e : Entry w) (m : Memory w) (bs : List Bool)
    (hfit : 5 ≤ 2^w) (valid : e.Valid (header pub) m) (f : ℕ) (raw : Report w)
    (hr : execute (source workers e.stage pub) f ((source workers e.stage pub).start e.state) m bs = some raw)
    (room : f+30 ≤ cap) :
    let L := program workers pub
    execute L cap (L.start e.marker) m bs = some (report (header pub) e raw) := by
  have hp := prefix_length_le (header pub) e
  have small := (execute_spec hr).1.length_lt
  have hl := report_length_le (header pub) e raw
  change ((e.prefixEvents (header pub)) ++ (exitReport (header pub) e.stage raw).events).length ≤ _ at hl
  rw [List.length_append] at hl
  have run := execute_extend hr (cap-(e.prefixEvents (header pub)).length-f)
  rw [show f + (cap-(e.prefixEvents (header pub)).length-f) = cap-(e.prefixEvents (header pub)).length by omega] at run
  exact call_ok workers pub cap e m bs hfit (by omega) valid raw run (by omega)

/-- A successful call supplies a valid source entry even when its marker and
header were given as arbitrary input words. -/
theorem entry_of_success (cap : ℕ) (host : Word w) (m : Memory w) (bs : List Bool)
    (hfit : 5 ≤ 2^w) (out : Report w)
    (hr : execute (program workers pub) cap ((program workers pub).start host) m bs = some out) :
    ∃ e : Entry w, e.marker = host ∧ e.Valid (header pub) m := by
  by_cases hz : host = 0
  · exact ⟨.initial,hz.symm,trivial⟩
  by_cases ho : host = 1
  · subst host
    by_cases ht : ∃ s : Stage, m (header pub).val = tagWord w s
    · obtain ⟨s,hs⟩ := ht
      exact ⟨.resume s (m (header pub+31).val),rfl,hs,rfl⟩
    · have bad := enter_bad_tag (component workers) pub hfit cap m (fun s h => ht ⟨s,h⟩) bs
      exact (Option.some_ne_none _ (hr.symm.trans bad)).elim
  · have bad := enter_bad_marker (component workers) pub host hz ho cap m bs
    exact (Option.some_ne_none _ (hr.symm.trans bad)).elim

end PairSimulation.TerminalLink

end VPVNP
end Computability
end OAI
