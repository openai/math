import OAI.Computability.VPVNP.PairSimulationDFS

/-!
# Native depth-first visits of an ordered placement tree

A node stores the absolute address of its descriptor and the address of
its ordered child list. Visiting a forest pushes the listed children ahead
of the pending suffix. The total number of child reads is the number of
non-root nodes in the forest, even if some addresses recur.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.DFS

open BurstRAM BurstRAM.PrivateRAM
open scoped Fin.CommRing
open private headerEvents from OAI.Computability.VPVNP.PairSimulationDFS

variable {w : ℕ}

/-- One node of an actual local expansion, with its ordered placement fiber. -/
inductive VertexTree where
  | node (address src count : ℕ) (children : Fin count → VertexTree)

namespace VertexTree

/-- The absolute DFS node address stored at the root of this selected vertex tree. -/
def address : VertexTree → ℕ
  | .node addr _ _ _ => addr

/-- All descriptor addresses in the order visited by the downward-growing stack. -/
def preorder : VertexTree → List ℕ
  | .node addr _ _ kids => addr :: (List.ofFn fun i => preorder (kids i)).flatten

theorem preorder_nonempty (t : VertexTree) : 1 ≤ t.preorder.length := by
  cases t
  simp [preorder]

/-- Contents of the native descriptor table, including the pointer and
count of an empty child list at each leaf. -/
def rows (w : ℕ) (m : Memory w) : VertexTree → Prop
  | .node addr src _ kids =>
    addr < 2^w ∧ Row m addr src (List.ofFn fun i => ((kids i).address : Word w)) ∧
      ∀ i, rows w m (kids i)

private theorem forest_length (trees : List VertexTree) :
    trees.length ≤ (trees.flatMap preorder).length := by
  induction trees with
  | nil => rfl
  | cons t tail ih =>
    simp only [List.length_cons, List.flatMap_cons, List.length_append]
    have := preorder_nonempty t
    omega

private def CanPrepend (m : Memory w) (top : ℕ) (t : VertexTree) : Prop :=
  ∀ (pending nodes : List (Word w)) (es : List (Event w)), Visits m top pending nodes es →
    t.preorder.length + pending.length ≤ top →
    ∃ out, Visits m top ((t.address : Word w) :: pending)
      (t.preorder.map (fun n : ℕ => (n : Word w)) ++ nodes) out

private theorem prepend_forest {m : Memory w} {top : ℕ} (trees : List VertexTree)
    (h : ∀ t ∈ trees, CanPrepend m top t) {pending nodes : List (Word w)} {es : List (Event w)}
    (v : Visits m top pending nodes es)
    (hsize : (trees.flatMap preorder).length + pending.length ≤ top) :
    ∃ out, Visits m top (trees.map (fun t => (t.address : Word w)) ++ pending)
      ((trees.flatMap preorder).map (fun n : ℕ => (n : Word w)) ++ nodes) out := by
  induction trees with
  | nil => exact ⟨es, v⟩
  | cons t tail ih =>
    have hsum : t.preorder.length + (tail.flatMap preorder).length + pending.length ≤ top := by
      simpa only [List.flatMap_cons, List.length_append] using hsize
    obtain ⟨log, run⟩ := ih (fun t ht => h t (List.mem_cons_of_mem _ ht)) (by omega)
    have hrest := forest_length tail
    have hspace : t.preorder.length +
        (tail.map (fun t => (t.address : Word w)) ++ pending).length ≤ top := by
      simp only [List.length_append, List.length_map]
      omega
    obtain ⟨out, run'⟩ := h t List.mem_cons_self _ _ _ run hspace
    exact ⟨out, by simpa only [List.map_cons, List.cons_append, List.flatMap_cons,
      List.map_append, List.append_assoc] using run'⟩

private theorem prepend (t : VertexTree) (m : Memory w) (top : ℕ) (h : rows w m t) :
    CanPrepend m top t := by
  induction t with
  | node addr src count kids ih =>
    intro pending nodes es old space
    obtain ⟨ha, hr, hk⟩ := h
    let ts := List.ofFn kids
    have hm : ts.flatMap preorder = (List.ofFn fun i => preorder (kids i)).flatten := by
      rw [List.flatMap_def, List.map_ofFn]
      rfl
    have hsum : (ts.flatMap preorder).length + pending.length < top := by
      simpa only [preorder, List.length_cons, hm, Nat.succ_add, Nat.succ_le_iff] using space
    have hchildren : ∀ child ∈ ts, CanPrepend m top child := by
      intro child hc
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hc
      exact ih i (hk i)
    obtain ⟨log, run⟩ := prepend_forest ts hchildren old hsum.le
    have hfit : (ts.map (fun t => (t.address : Word w))).length + pending.length ≤ top := by
      rw [List.length_map]
      exact (Nat.add_le_add_right (forest_length ts) _).trans hsum.le
    have hr' : Row m (addr : Word w).val src (ts.map fun t => (t.address : Word w)) := by
      simpa only [Fin.val_natCast, Nat.mod_eq_of_lt ha, ts, List.map_ofFn,
        Function.comp_def] using hr
    exact ⟨_, by simpa only [address, preorder, ← hm, List.map_cons, List.cons_append] using
      (Visits.cons hr' hfit run)⟩

/-- The fixed native traversal executes the serialized placement tree, in
the selected order, in a stack with one word per node. -/
theorem visits {m : Memory w} (t : VertexTree) (top : ℕ) (hrows : rows w m t)
    (hsize : t.preorder.length ≤ top) :
    ∃ es, Visits m top [(t.address : Word w)] (t.preorder.map (fun n : ℕ => (n : Word w))) es := by
  obtain ⟨es, hv⟩ := prepend t m top hrows [] [] _ Visits.nil (by simpa using hsize)
  exact ⟨es, by simpa using hv⟩

end VertexTree

/-- The DFS control code reads two header words per visit and one word
per child. Its event length also includes the pop, loop, and stack-copy
instructions, and the final empty-stack test. -/
theorem Visits.cost {m : Memory w} {top : ℕ} {pending nodes : List (Word w)} {es : List (Event w)}
    (h : Visits m top pending nodes es) :
    countProbes es + pending.length = 3 * nodes.length ∧
      es.length + 5 * pending.length = 15 * nodes.length + 1 := by
  have append (xs ys : List (Event w)) :
      countProbes (xs ++ ys) = countProbes xs + countProbes ys := by
    induction xs with
    | nil => simp [countProbes]
    | cons x xs ih => cases x <;> simp [countProbes, ih, Nat.add_comm, Nat.add_left_comm]
  have len (src n : ℕ) : (EndpointBits.events m src n).length = 5*n+1 := by
    induction n generalizing src with
    | zero => rfl
    | succ n ih => simp [EndpointBits.events, ih]; omega
  induction h with
  | nil => exact ⟨rfl, rfl⟩
  | @cons node pending kids nodes src es row fits rest ih =>
    obtain ⟨hp, hl⟩ := ih
    rw [List.length_append] at hp hl
    simp only [append, List.length_append, List.length_cons, List.length_nil, len]
    have hhead : countProbes (headerEvents w node.val src kids.length) = 2 := rfl
    have hzero : countProbes ([.tick,.tick,.tick] : List (Event w)) = 0 := rfl
    rw [hzero, hhead, EndpointBits.probes]
    change _ ∧ 3 + 6 + (5*kids.length+1) + es.length + 5*(pending.length+1) =
      15*(nodes.length+1)+1
    omega

end PairSimulation.DFS

end VPVNP
end Computability
end OAI
