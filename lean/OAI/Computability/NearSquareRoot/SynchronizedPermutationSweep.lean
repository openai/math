import OAI.Computability.NearSquareRoot.BoundedIndexedSweep
import OAI.Computability.NearSquareRoot.CRTControlledBenesParallel
import OAI.Computability.NearSquareRoot.BoundedProduct

/-! # Physical directory sweeps acting on one permuted array

The directory is consumed in its original order. Each switch acts on the array in
place in the sense of the bounded register interface. The space estimate charges one
live array, the remaining directory and the largest single-stage workspace.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace PermutationSweep
open IntegerMultiplication IntegerMultiplication.Code
open Space Benes

variable {S D V : Type*}

/-- The address of an element after the first `j` records of the directory. -/
def before (xs : List S) (stage : S → Equiv.Perm D) (j : ℕ) : Equiv.Perm D :=
  (xs.take j).foldl (fun p s => p.trans (stage s)) (Equiv.refl D)

theorem before_succ (xs : List S) (stage : S → Equiv.Perm D) (j : ℕ) (hj : j < xs.length) :
    before xs stage (j+1) = (before xs stage j).trans (stage xs[j]) := by
  unfold before
  rw [List.take_succ_eq_append_getElem hj,List.foldl_append]
  rfl

theorem scatter_trans (p q : Equiv.Perm D) (v : D → V) :
    scatter (p.trans q) v = scatter q (scatter p v) := rfl

private theorem scatter_from (stage : S → Equiv.Perm D) (xs : List S) (p : Equiv.Perm D) (v : D → V) :
    scatter (xs.foldl (fun z s => z.trans (stage s)) p) v =
      xs.foldl (fun h s => scatter (stage s) h) (scatter p v) := by
  induction xs generalizing p with
  | nil => rfl
  | cons s t ih => exact ih _

theorem scatter_all (stage : S → Equiv.Perm D) (xs : List S) (v : D → V) :
    scatter (before xs stage xs.length) v = xs.foldl (fun h s => scatter (stage s) h) v := by
  simp only [before,List.take_length]
  exact scatter_from stage xs _ v

private theorem forest_range {S : Type*} [Inhabited S] (xs : List S) (key : S → Tree) :
    Task.forest (fun j => key (xs.getD j default)) (List.range xs.length) = Task.forest key xs := by
  rw [← Task.forest_map]
  congr 1
  apply List.ext_getElem
  · simp
  · intro j hj hk
    simp [List.getElem?_eq_getElem hk]

variable {X : Type*} {Address Payload : X → Type*} {Stage : Type*} [Inhabited Stage]

/-- The actual register command for a directory of array permutations. The one-step
contract admits every reordering of the original array, so an input-dependent size
bound can reuse the preserved set of records at all prefixes. -/
theorem run (jobs : X → List Stage) (stage : (x : X) → Stage → Equiv.Perm (Address x))
    (key : X → Stage → Tree) (array : (x : X) → (Address x → Payload x) → Tree)
    (input : (x : X) → Address x → Payload x) (tick volume work : X → ℕ)
    (step : BoundedTask
      (fun z : (x : X) × {a // a ∈ jobs x} × Equiv.Perm (Address x) => tick z.1)
      (fun z => work z.1)
      (fun z => .fork (key z.1 z.2.1) (array z.1 (scatter z.2.2 (input z.1))))
      (fun z => array z.1 (scatter (stage z.1 z.2.1) (scatter z.2.2 (input z.1)))))
    (directoryFits : ∀ x, (Task.forest (key x) (jobs x)).count ≤ volume x)
    (arrayFits : ∀ x (p : Equiv.Perm (Address x)), (array x (scatter p (input x))).count ≤ volume x) :
    BoundedTask (fun x => (jobs x).length * tick x + volume x) (fun x => volume x + work x)
      (fun x => .fork (Task.forest (key x) (jobs x)) (array x (input x)))
      (fun x => array x ((jobs x).foldl (fun v s => scatter (stage x s) v) (input x))) := by
  let table x j := key x ((jobs x).getD j default)
  let state x j := array x (scatter (before (jobs x) (stage x) j) (input x))
  let index (z : (x : X) × Fin (jobs x).length) :
      (x : X) × {a // a ∈ jobs x} × Equiv.Perm (Address x) :=
    ⟨z.1, ⟨(jobs z.1)[z.2.val],List.getElem_mem _⟩,before (jobs z.1) (stage z.1) z.2.val⟩
  have next := (step.on index).conform (fun _ => rfl) (fun _ => rfl)
    (input' := fun z => .fork (table z.1 z.2.val) (state z.1 z.2.val))
    (output' := fun z => state z.1 (z.2.val+1))
    (fun z => by simp [table,state,index])
    (fun z => by simp [state,index,before_succ _ _ _ z.2.isLt,scatter_trans])
  have exec := BoundedTask.indexedSweep (fun x => (jobs x).length) table state tick volume work next
    (fun x => by simpa only [table,forest_range] using directoryFits x)
    (fun x j _ => arrayFits x _)
  exact exec.conform (fun _ => rfl) (fun _ => rfl)
    (fun x => by
      rw [show Task.forest (table x) (List.range (jobs x).length) = Task.forest (key x) (jobs x) from
        forest_range (jobs x) (key x)]
      rfl)
    (fun x => congrArg (array x) (scatter_all (stage x) (jobs x) (input x)))

end PermutationSweep

end NearSquareRoot
end Computability
end OAI
