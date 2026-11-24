import OAI.Computability.VPVNP.PairTraversalControllerStep
import OAI.Computability.VPVNP.PairTraversalControllerReference

/-!
# Every reference job occupies the online dispatcher's selected layer

The tag and row lists have one entry for each physical state level. Their
concatenation is exactly the phase-level schedule decoded from the persistent
word, including both passes over the last state.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.TraversalControllerInputs

open BurstRAM TraversalController TraversalRoles TraversalRows DirectoryRun
open scoped Fin.CommRing

variable {w : ℕ} {pub : Fin 11 → Word w} {m : Memory w} {offset cap base : ℕ}
variable {tags : List TaggedLayer} {rows : List (Worker w)}

theorem Schedule.located (h : Schedule pub m offset cap base tags rows)
    (p : Fin (tagJobs w offset cap base tags ++ rows.map rowJob).length) :
    let jobs := tagJobs w offset cap base tags ++ rows.map rowJob
    (jobs[p]).Located pub m tags.length p.val := by
  intro jobs
  have length : jobs.length = 2 * tags.length := by simp [jobs, h.jobs_length]; omega
  have bound : p.val < 2 * tags.length := p.isLt.trans_eq length
  by_cases first : p.val < tags.length
  · let j : Fin tags.length := ⟨p.val, first⟩
    obtain ⟨count, fields, _⟩ := h.lookup j
    have entry := tagJobs_at w offset cap base tags j
    have htag : p.val < (tagJobs w offset cap base tags).length := by simpa using first
    have hp : jobs[p] = .tag (TraversalRoles.Native.params offset cap
        (layerBase cap base tags j.val) (tags[j].role.code : Word w)) tags[j].layer.count := by
      change (tagJobs w offset cap base tags ++ rows.map rowJob)[p.val] = _
      rw [List.getElem_append_left htag]
      exact Option.some.inj ((List.getElem?_eq_getElem htag).symm.trans entry)
    rw [hp]
    change p.val < tags.length ∧ tagParams pub m (p.val % tags.length) = _ ∧
      (siteCount pub m (p.val % tags.length)).val = _
    rw [Nat.mod_eq_of_lt first]
    exact ⟨first, fields, count⟩
  · have lo : tags.length ≤ p.val := Nat.le_of_not_lt first
    let j : Fin tags.length := ⟨p.val - tags.length, by omega⟩
    have modEq : p.val % tags.length = j.val := by
      have add : p.val = tags.length + j.val := by dsimp [j]; omega
      rw [add, Nat.add_mod_left, Nat.mod_eq_of_lt j.isLt]
    have hj : j.val < rows.length := h.jobs_length.symm ▸ j.isLt
    obtain ⟨_, _, row⟩ := h.lookup j
    have hp : jobs[p] = rowJob (rows[j.val]'hj) := by
      change (tagJobs w offset cap base tags ++ rows.map rowJob)[p.val] = _
      rw [List.getElem_append_right (by simpa using lo), List.getElem_map]
      simp only [tagJobs_length, j]
    rw [hp]
    generalize eqn : rows[j.val] = worker at row ⊢
    cases worker with
    | leaf capacity layer n =>
      obtain ⟨zero, count, params⟩ := row
      exact ⟨lo, modEq.trans zero, params, modEq ▸ count⟩
    | fiber params capacity previous layer n =>
      obtain ⟨i, succ, count, vals⟩ := row
      have positive : p.val % tags.length ≠ 0 := by omega
      have pred : p.val % tags.length - 1 = i := by omega
      exact ⟨lo, positive, pred ▸ vals, modEq ▸ count⟩

/-- Both passes use precisely the actual count of the represented state level. -/
theorem Schedule.pass_count (h : Schedule pub m offset cap base tags rows)
    (p : Fin (tagJobs w offset cap base tags ++ rows.map rowJob).length) :
    let jobs := tagJobs w offset cap base tags ++ rows.map rowJob
    (jobs[p]).count = (siteCount pub m (p.val % tags.length)).val := by
  intro jobs
  let job := jobs[p]
  have loc : job.Located pub m tags.length p.val := h.located p
  change job.count = _
  cases eqn : job with
  | tag fields n => rw [eqn] at loc; exact loc.2.2.symm
  | leaf fields n => rw [eqn] at loc; exact loc.2.2.2.symm
  | fiber fields c n => rw [eqn] at loc; exact loc.2.2.2.symm

end PairSimulation.TraversalControllerInputs

end VPVNP
end Computability
end OAI
