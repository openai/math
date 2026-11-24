import OAI.Computability.VPVNP.PairTraversalControllerBody
import OAI.Computability.VPVNP.PairTraversalRoleExecution
import OAI.Computability.VPVNP.PairTraversalDirectoryRun

/-!
# Chronological traversal passes and their reset-entry calls

The reference jobs write one layer of role tags at a time, then the leaf
and each successive fiber layer. A site's call uses exactly the memory
left by earlier sites of its own pass and all preceding passes.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.TraversalController

open BurstRAM BurstRAM.PrivateRAM TraversalRows
open scoped Fin.CommRing

variable {w : ℕ}

/-- Role jobs advance the descriptor base after every layer. -/
def tagJobs (w offset cap base : ℕ) : List TraversalRoles.TaggedLayer → List (Pass w)
  | [] => []
  | l :: ls => .tag (TraversalRoles.Native.params offset cap base (l.role.code : Word w)) l.layer.count ::
      tagJobs w offset cap (endPos cap base l.layer) ls

@[simp] theorem tagJobs_length (w offset cap base : ℕ) (ls : List TraversalRoles.TaggedLayer) :
    (tagJobs w offset cap base ls).length = ls.length := by
  induction ls generalizing base with
  | nil => rfl
  | cons l ls ih => simp only [tagJobs, List.length_cons, ih]

/-- The indexed job uses the same descriptor base as the controller's
tag-parameter lookup. -/
theorem tagJobs_at (w offset cap base : ℕ) (ls : List TraversalRoles.TaggedLayer) (i : Fin ls.length) :
    (tagJobs w offset cap base ls)[i.val]? = some (.tag (TraversalRoles.Native.params offset cap
      (TraversalRoles.layerBase cap base ls i.val) (ls[i.val].role.code : Word w)) ls[i.val].layer.count) := by
  induction ls generalizing base with
  | nil => exact i.elim0
  | cons l ls ih =>
    induction i using Fin.cases with
    | zero => simp only [tagJobs, Fin.val_zero, List.getElem?_cons_zero, List.getElem_cons_zero,
        TraversalRoles.layerBase_zero]
    | succ j => simpa only [tagJobs, Fin.val_succ, List.getElem?_cons_succ, List.getElem_cons_succ,
        TraversalRoles.layerBase_cons] using ih (endPos cap base l.layer) j

/-- The row job uses the exact public directory of its original worker. -/
def rowJob : DirectoryRun.Worker w → Pass w
  | .leaf cap base count => .leaf (LeafWorker.directory w cap base) count
  | .fiber pub cap previous base count => .fiber (workerData pub cap previous base) cap count

/-- Consecutive passes start at ordinal zero and retain external memory. -/
inductive Reference : List (Pass w) → Memory w → List (Report w) → Prop
  | nil (m : Memory w) : Reference [] m []
  | cons {P : Pass w} {tail : List (Pass w)} {m : Memory w} {rs ss : List (Report w)}
      (run : P.Run m rs) (rest : Reference tail (after m (eventLog rs)) ss) :
      Reference (P :: tail) m (rs ++ ss)

private theorem append_memory (m : Memory w) (rs ss : List (Report w)) :
    after m (eventLog (rs ++ ss)) = after (after m (eventLog rs)) (eventLog ss) := by
  simp only [eventLog, List.flatMap_append, after, List.foldl_append]

theorem Reference.append {xs ys : List (Pass w)} {m : Memory w} {rs ss : List (Report w)}
    (first : Reference xs m rs) (second : Reference ys (after m (eventLog rs)) ss) :
    Reference (xs ++ ys) m (rs ++ ss) := by
  induction first with
  | nil m => exact second
  | @cons P tail m localRs rest hr ht ih =>
    rw [append_memory] at second
    simpa only [List.cons_append, List.append_assoc] using Reference.cons hr (ih second)

theorem Reference.of_tags {offset cap base : ℕ} {ls : List TraversalRoles.TaggedLayer}
    {m : Memory w} {rs : List (Report w)} (h : TraversalRoles.RolePasses offset cap base ls m rs) :
    Reference (tagJobs w offset cap base ls) m rs := by
  induction h with
  | nil => exact .nil _
  | cons hr _ ih => exact .cons hr ih

theorem Reference.of_rows {xs : List (DirectoryRun.Worker w)} {m : Memory w} {rs : List (Report w)}
    (h : DirectoryRun.Segments xs m rs) : Reference (xs.map rowJob) m rs := by
  induction h with
  | nil => exact .nil _
  | @cons head tail m rs ss hr ht ih =>
    apply Reference.cons _ ih
    cases head <;> exact hr

theorem Reference.of_passes {offset cap base : ℕ} {ls : List TraversalRoles.TaggedLayer}
    {xs : List (DirectoryRun.Worker w)} {m : Memory w} {tags rows : List (Report w)}
    (ht : TraversalRoles.RolePasses offset cap base ls m tags)
    (hr : DirectoryRun.Segments xs (after m (eventLog tags)) rows) :
    Reference (tagJobs w offset cap base ls ++ xs.map rowJob) m (tags ++ rows) :=
  (of_tags ht).append (of_rows hr)

namespace Pass

variable {P : Pass w} {m : Memory w} {rs : List (Report w)}

theorem Run.branchPaths (h : P.Run m rs) : BurstRAM.branchPaths rs = List.replicate P.count [] :=
  ((runSegment_iff ..).mp h).2.2

theorem Run.length (h : P.Run m rs) : rs.length = P.count := by
  simpa only [BurstRAM.branchPaths, List.length_map, List.length_replicate] using
    congrArg List.length h.branchPaths

/-- Each step retains its full trace and uses the incremented site ordinal. -/
inductive Sites (P : Pass w) : Word w → Memory w → List (Report w) → Prop
  | nil (site : Word w) (m : Memory w) : Sites P site m []
  | cons {site : Word w} {m : Memory w} {r : Report w} {rs : List (Report w)}
      (step : P.At site m r) (rest : Sites P (site+1) (after m r.events) rs) :
      Sites P site m (r :: rs)

private theorem sites_from {site : Word w} {n : ℕ}
    (run : runSegment P.spec.2 P.clock (some site) m (List.replicate n []) = some rs) :
    Sites P site m rs := by
  induction n generalizing site m rs with
  | zero =>
    have : rs = [] := Option.some.inj run.symm
    subst rs
    exact .nil _ _
  | succ n ih =>
    rw [List.replicate_succ, runSegment] at run
    cases he : execute P.spec.2 P.clock (P.spec.2.start site) m [] with
    | none => simp only [he, reduceCtorEq] at run
    | some r =>
      rw [he] at run
      obtain ⟨ss,hs,rfl⟩ := Option.map_eq_some_iff.mp run
      have step : P.At site m r := he
      rw [Pass.next step] at hs
      exact .cons step (ih hs)

theorem Run.sites (h : P.Run m rs) : Sites P 0 m rs := sites_from h

private theorem Sites.atSite {site : Word w} (h : Sites P site m rs) (i : Fin rs.length) :
    P.At (site + (i.val : Word w)) (after m (eventLog (rs.take i.val))) rs[i.val] := by
  induction h with
  | nil => exact i.elim0
  | @cons site m r rs step _ ih =>
    induction i using Fin.cases with
    | zero =>
      change P.At (site + ((0 : ℕ) : Word w)) m r
      simpa only [Nat.cast_zero, add_zero] using step
    | succ j =>
      have mem : after m (eventLog ((r :: rs).take (j.val + 1))) =
          after (after m r.events) (eventLog (rs.take j.val)) := by
        simp only [List.take_succ_cons, eventLog, List.flatMap_cons, after, List.foldl_append]
      simpa only [Fin.val_succ, mem, List.getElem_cons_succ, Nat.cast_add, Nat.cast_one,
        add_assoc, add_comm (1 : Word w)] using ih j

theorem Run.atSite (h : P.Run m rs) (i : Fin rs.length) :
    P.At (i.val : Word w) (after m (eventLog (rs.take i.val))) rs[i.val] := by
  simpa only [zero_add] using h.sites.atSite i

theorem Run.atSite_next (h : P.Run m rs) (i : Fin rs.length) :
    rs[i.val].result = some ((i.val + 1 : ℕ) : Word w) := by
  simpa only [Nat.cast_add, Nat.cast_one] using Pass.next (h.atSite i)

end Pass

theorem Reference.length {xs : List (Pass w)} {m : Memory w} {rs : List (Report w)}
    (h : Reference xs m rs) : rs.length = (xs.map Pass.count).sum := by
  induction h with
  | nil => rfl
  | cons hr _ ih => simp only [List.length_append, hr.length, ih, List.map_cons, List.sum_cons]

theorem Reference.branchPaths {xs : List (Pass w)} {m : Memory w} {rs : List (Report w)}
    (h : Reference xs m rs) : BurstRAM.branchPaths rs = List.replicate (xs.map Pass.count).sum [] := by
  induction h with
  | nil => rfl
  | @cons P tail m rs ss hr _ ih =>
    rw [show BurstRAM.branchPaths (rs ++ ss) = BurstRAM.branchPaths rs ++ BurstRAM.branchPaths ss
      from List.map_append, hr.branchPaths, ih]
    simp only [List.map_cons, List.sum_cons, List.replicate_add]

end PairSimulation.TraversalController

end VPVNP
end Computability
end OAI
