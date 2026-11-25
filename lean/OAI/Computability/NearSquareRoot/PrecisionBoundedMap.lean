import OAI.Computability.NearSquareRoot.PrecisionGridPassSpace
import OAI.Computability.IntegerMultiplication.Code.List
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-! # Peak space of framed record maps -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Space

open IntegerMultiplication Code

private theorem size_reverse {α : Type*} [Codec α] (s : List α) : size s.reverse = size s := by
  rw [← costSum_le_length_size, ← costSum_le_length_size s]
  simp [costSum]

private theorem map_take_le {α β : Type*} [Codec β] (s : List α) (f : α → β) (j : ℕ) :
    size ((s.take j).map f) ≤ size (s.map f) := by
  have eq := size_append_right ((s.take j).map f) ((s.drop j).map f)
  rw [← List.map_append, List.take_append_drop] at eq
  have := size_pos ((s.drop j).map f)
  omega

private theorem map_range_getD {α : Type*} [Inhabited α] (s : List α) :
    (List.range s.length).map (fun j => s[j]?.getD default) = s := by
  apply List.ext_getElem
  · simp
  · intro i h₁ h₂
    simp [h₂]

/-- Map into a reversed output forest. The cost of the parked accumulator
enters only the space bound, since the child command acts on the first
component of the pair. -/
private theorem BoundedTask.map_reversed {I α β : Type*} [Inhabited α] [Codec α] [Codec β]
    (s : I → List α) (f : α → β) (V W : I → ℕ)
    (call : Task (fun u : (i : I) × Fin (s i).length => W u.1)
      (fun u => send ((s u.1)[u.2.val])) (fun u => send (f ((s u.1)[u.2.val]))))
    (hin : ∀ i, size (s i) ≤ V i) (hout : ∀ i, size ((s i).map f) ≤ V i)
    (hword : ∀ i x, x ∈ s i → size x ≤ W i) :
    BoundedTask (fun i => 2 * (s i).length * (W i + 1) + 1)
      (fun i => 2*(V i + W i + 1))
      (fun i => send ((s i), ([] : List β)))
      (fun i => send ((s i).map f).reverse) := by
  let d i := (s i).length
  let x i (j : ℕ) := (s i)[j]?.getD default
  let table i j := send (x i j)
  let a i j := (((s i).take j).map f).reverse
  let state i j := send (a i j)
  let X := (i : I) × Fin (d i)
  have xeq (v : X) : x v.1 v.2.val = (s v.1)[v.2.val] := by
    have hj : v.2.val < (s v.1).length := v.2.isLt
    simp [x, hj]
  have next (v : X) : state v.1 (v.2.val+1) = Tree.fork (send (f (x v.1 v.2.val)))
      (state v.1 v.2.val) := by
    simp only [state, a, List.take_succ_eq_append_getElem v.2.isLt, List.map_append,
      List.map_singleton, List.reverse_append, List.reverse_singleton,
      List.singleton_append, send_cons, xeq]
  have loc := call.left (fun v : X => state v.1 v.2.val)
  have loc' : Task (fun v : X => W v.1)
      (fun v => Tree.fork (table v.1 v.2.val) (state v.1 v.2.val))
      (fun v => state v.1 (v.2.val+1)) := loc.conform (fun _ => rfl)
        (fun v => congrArg (fun z => Tree.fork (send z) _) (xeq v).symm)
        (fun v => by rw [next v, xeq v])
  have step := BoundedTask.of_time loc'
  let space i j := (Tree.fork (table i j) (state i j)).count + W i
  have tab_eq (i : I) : Task.forest (table i) (List.range (d i)) = send (s i) := by
    calc
      _ = send ((List.range (d i)).map (x i)) := by rw [← Task.forest_send, Task.forest_map]
      _ = _ := congrArg send (map_range_getD (s i))
  have hs (i : I) (j : ℕ) : (state i j).count ≤ V i := by
    change size (((s i).take j).map f).reverse ≤ _
    rw [size_reverse]
    exact (map_take_le (s i) f j).trans (hout i)
  have hword' (i : I) (j : ℕ) (hj : j < d i) : (table i j).count ≤ W i := by
    change size (x i j) ≤ _
    rw [xeq ⟨i,⟨j,hj⟩⟩]
    exact hword i _ (List.getElem_mem _)
  have run := BoundedTask.indexedPasses d table state (fun i _ => W i) space
    (fun i => 2*(V i + W i + 1)) step
    (fun i => by rw [tab_eq]; change size _ ≤ _; have := hin i; omega)
    (fun i j _ => by have := hs i j; omega)
    (fun i j hj => by
      have ht := hword' i j hj
      have hp := hs i j
      simp only [space, Tree.count]
      omega)
  have cost (i : I) :
      (∑ j ∈ Finset.range (d i), (W i + (table i j).count + 1)) + 1 ≤
        2 * (s i).length * (W i+1) + 1 := by
    have hh : ∑ j ∈ Finset.range (d i), (W i + (table i j).count + 1) ≤
        ∑ _j ∈ Finset.range (d i), (2*(W i+1)) :=
      Finset.sum_le_sum (fun j hj => by have := hword' i j (Finset.mem_range.mp hj); omega)
    simp only [Finset.sum_const, Finset.card_range, Nat.nsmul_eq_mul, d] at hh
    rw [Nat.mul_left_comm, ← Nat.mul_assoc] at hh
    exact Nat.add_le_add_right hh 1
  apply (run.mono cost (fun _ => le_rfl)).conform (fun _ => rfl) (fun _ => rfl)
  · intro i
    rw [tab_eq]
    rfl
  · intro i
    simp only [state, a, d, List.take_length]

/-- Map framed record calls over a stream in tape order. The answer has a
separate peak bound for resident input/output and the temporary storage of a
single invocation. Calls may have unbounded work as the word length grows. -/
theorem BoundedTask.mapping {I α β : Type*} [Inhabited α] [Codec α] [Codec β]
    (s : I → List α) (f : α → β) (V W : I → ℕ)
    (call : Task (fun u : (i : I) × Fin (s i).length => W u.1)
      (fun u => send ((s u.1)[u.2.val])) (fun u => send (f ((s u.1)[u.2.val]))))
    (hin : ∀ i, size (s i) ≤ V i) (hout : ∀ i, size ((s i).map f) ≤ V i)
    (hword : ∀ i x, x ∈ s i → size x ≤ W i) :
    BoundedTask (fun i => V i + (s i).length * (W i + 1))
      (fun i => V i + W i) (fun i => send (s i)) (fun i => send ((s i).map f)) := by
  have put : Easy (fun l : List α => (l, ([] : List β))) := Easy.identity.pair (Easy.const _)
  have start := BoundedTask.of_time (put.on s)
  have loop := BoundedTask.map_reversed s f V W call hin hout hword
  have finish := BoundedTask.of_time (Easy.reverse.on (fun i => ((s i).map f).reverse))
  have chain := (start.compose loop).compose finish
  apply (chain.conform (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
    (fun i => by change send ((s i).map f).reverse.reverse = send ((s i).map f); simp)).bound 3 3
  · intro i
    have h := hin i
    have g := hout i
    change size (s i) + (2*(s i).length*(W i+1)+1) + size ((s i).map f).reverse + 1 ≤ _
    rw [size_reverse, Nat.mul_assoc]
    omega
  · intro i
    have h := hin i
    have g := hout i
    change max (max (size (s i) + size (s i)) (2*(V i+W i+1)))
      (size ((s i).map f).reverse + size ((s i).map f).reverse) + 1 ≤ _
    rw [size_reverse]
    omega

end Space

end NearSquareRoot
end Computability
end OAI
