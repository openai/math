import OAI.Computability.VPVNP.PairSimulationResidentMapLoopExact

/-!
# Acceptance of a finite row of deterministic resident maps

Even though each successful map changes the scratch passed to the next,
the scan's success bit depends only on the acceptance predicate of each
occurrence when that predicate holds for all starting scratch values.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.ResidentMapLoop.Exact

open BurstRAM DFS

variable {w endAddr n : ℕ}

/-- Once each occurrence's success bit is determined by its typed input,
the whole scratch-dependent loop succeeds exactly when every occurrence does. -/
theorem scan_ofFn_iff (node : Word w) (rows : Fin n → Action w endAddr) (accepts : Fin n → Prop)
    (spec : ∀ i s, (rows i node s).isSome ↔ accepts i) (saved : Scratch w endAddr) :
    (scan node (List.ofFn rows) saved).isSome ↔ ∀ i, accepts i := by
  induction n generalizing saved with
  | zero => simp [scan]
  | succ n ih =>
    rw [List.ofFn_succ, Fin.forall_fin_succ]
    cases head : rows 0 node saved with
    | none =>
      have no : ¬ accepts 0 := fun h => by simpa [head] using (spec 0 saved).mpr h
      simp [scan, head, no]
    | some pair =>
      obtain ⟨es, mid⟩ := pair
      have yes := (spec 0 saved).mp (by simp [head])
      have next := ih (fun i => rows i.succ) (fun i => accepts i.succ)
        (fun i => spec i.succ) mid
      cases rest : scan node (List.ofFn fun i => rows i.succ) mid with
      | none => simpa only [scan, head, rest, true_and, yes] using next
      | some pair =>
        obtain ⟨tail, final⟩ := pair
        simpa only [scan, head, rest, true_and, yes, Option.isSome_some] using next

/-- On a successful scan, any coordinate updated additively by each
occurrence receives the sum of the actual updates in row order. -/
theorem scan_ofFn_add {β : Type*} [AddCommMonoid β] (node : Word w)
    (rows : Fin n → Action w endAddr) (coord : Scratch w endAddr → β) (delta : Fin n → β)
    (step : ∀ j s es out, rows j node s = some (es, out) → coord out = coord s + delta j)
    {saved out : Scratch w endAddr} {es : List (Event w)}
    (run : scan node (List.ofFn rows) saved = some (es, out)) :
    coord out = coord saved + ∑ j, delta j := by
  induction n generalizing saved out es with
  | zero =>
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj run)
    simp
  | succ n ih =>
    rw [List.ofFn_succ] at run
    cases head : rows 0 node saved with
    | none => simp [scan, head] at run
    | some pair =>
      obtain ⟨first, mid⟩ := pair
      cases rest : scan node (List.ofFn fun j => rows j.succ) mid with
      | none => simp [scan, head, rest] at run
      | some pair =>
        obtain ⟨tail, last⟩ := pair
        simp only [scan, head, rest, Option.some.injEq, Prod.mk.injEq] at run
        rw [← run.2, ih (fun j => rows j.succ) (fun j => delta j.succ) (fun j => step j.succ) rest,
          step 0 saved first mid head, Fin.sum_univ_succ, add_assoc]

end PairSimulation.ResidentMapLoop.Exact

end VPVNP
end Computability
end OAI
