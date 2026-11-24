import OAI.Computability.VPVNP.PairTraversalCost
import OAI.Computability.VPVNP.PairSimulationAssemblyBounds

/-!
# Placement histories in the native descriptor traversal

On each selected shrinking or refresh term, the children of an output
vertex are exactly the placed old vertices, in the actual reader's order.
The following construction retains these vertices recursively down to
the routed cursor input. The depth-first code visits the resulting tree
in that order, using the stored row addresses of the selected stages.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.LocalHistory

open NetworkKernel CompressorRecords Compression BurstRAM BurstRAM.PrivateRAM DFS
open scoped Fin.CommRing

variable {A : Type*} [CommRing A] {L : Type} [Fintype L] {κ : L → A} {N Y : Network}

/-- The header address and child-list pointer at each stage of a chosen history. -/
def RowPointers {N Y : Network} : TermChain A N Y → Type
  | .done _ => PUnit
  | .more t _ tail => (t.output.Site → ℕ × ℕ) × RowPointers tail

/-- Child IDs in the stored order, with their absolute addresses in the preceding layer. -/
def rowsAt {N Y : Network} {w : ℕ} (c : TermChain A N Y) (r : ChainParsers κ c)
    (ptr : RowPointers c) (m : Memory w) (previous : N.Site → ℕ) : Prop :=
  match c with
  | .done _ => True
  | .more _ _ tail =>
    (∀ v, (ptr.1 v).1 < 2 ^ w ∧ Row m (ptr.1 v).1 (ptr.1 v).2
      (List.ofFn fun j => (previous ((r.1.order.children v).entries j).val : Word w))) ∧
    rowsAt tail r.2 ptr.2 m (fun v => (ptr.1 v).1)

/-- A cursor leaf tree with the supplied node and source pointers and an empty family of
children. -/
def leafTree (ptr : ℕ × ℕ) : VertexTree :=
  .node ptr.1 ptr.2 0 Fin.elim0

private def addTree {t : Term A N} (r : TermParsers κ t) (p : t.output.Site → ℕ × ℕ)
    (input : N.Site → VertexTree) (v : t.output.Site) : VertexTree :=
  let order := r.order.children v
  .node (p v).1 (p v).2 order.length fun j => input (order.entries j).val

/-- Build the selected final vertex tree by following each term's actual
finite placement fibers. The initial vertices may already carry subtrees. -/
def chainTrees {N Y : Network} (c : TermChain A N Y) (r : ChainParsers κ c) (ptr : RowPointers c)
    (input : N.Site → VertexTree) : Y.Site → VertexTree :=
  match c with
  | .done _ => input
  | .more _ _ tail => chainTrees tail r.2 ptr.2 (addTree r.1 ptr.1 input)

open scoped Classical in
private theorem addTree_length {t : Term A N} (r : TermParsers κ t) (p : t.output.Site → ℕ × ℕ)
    (input : N.Site → VertexTree) (v : t.output.Site) :
    (addTree r p input v).preorder.length =
      1 + ∑ u : t.Preimage v, (input u.val).preorder.length := by
  let o := r.order.children v
  change ((p v).1 :: (List.ofFn fun i : Fin o.length =>
    (input (o.entries i).val).preorder).flatten).length = _
  rw [List.length_cons, List.length_flatten, List.map_ofFn, List.sum_ofFn]
  rw [Nat.add_comm 1]
  congr 1
  exact o.entries.sum_comp (fun u => (input u.val).preorder.length)

/-- Every visit consumes one of the vertex occurrences counted in
Theorem 7.1. Field and map occurrences may increase that count further. -/
theorem chainTrees_length (c : TermChain A N Y) (r : ChainParsers κ c) (ptr : RowPointers c)
    (input : N.Site → VertexTree) (counts : N.Site → ℕ)
    (hc : ∀ v, (input v).preorder.length ≤ counts v) :
    ∀ v, (chainTrees c r ptr input v).preorder.length ≤ c.occurrences counts v := by
  classical
  induction c with
  | done => exact hc
  | more t rec tail ih =>
    apply ih r.2 ptr.2 _ (t.pushHistorySize rec counts)
    intro v
    rw [addTree_length, Term.pushHistorySize]
    exact Nat.add_le_add (by unfold SiteRecords.count; omega)
      (Finset.sum_le_sum fun u _ => hc u.val)

theorem chainTrees_rows {w : ℕ} (c : TermChain A N Y) (r : ChainParsers κ c) (ptr : RowPointers c)
    (m : Memory w) (input : N.Site → VertexTree) (hs : ∀ v, (input v).rows w m)
    (hr : rowsAt c r ptr m (fun v => (input v).address)) :
    ∀ v, (chainTrees c r ptr input v).rows w m := by
  induction c with
  | done => exact hs
  | more t rec tail ih =>
    exact ih r.2 ptr.2 (addTree r.1 ptr.1 input) (fun v =>
      ⟨(hr.1 v).1, (hr.1 v).2, fun i => hs _⟩) hr.2

/-- The cursor leaves have an empty list in the first descriptor layer. -/
theorem leafTree_rows {w : ℕ} {m : Memory w} {p : ℕ × ℕ} (hp : p.1 < 2 ^ w)
    (h : Row m p.1 p.2 []) : (leafTree p).rows w m :=
  ⟨hp, by simpa only [List.ofFn_zero] using h, fun i => i.elim0⟩

/-- On every selected branch, the native DFS log reads at most three
words and uses at most fifteen word instructions per vertex occurrence,
plus the empty-stack test. The ordered node sequence is the actual
placement tree of that branch. -/
theorem selectedTraversal {k : Type*} [Field k] {S : BlockSchedule k}
    (B : S.Templates) (f : B.Entry → A) (hf : B.IsSolution f) {lanes : ℕ}
    (T : ℕ) (hT : T * S.laneBits ≤ lanes) (X : State (S.degreeExponent 0) lanes)
    (z : (B.execute f hf T hT X).Choices)
    (ptr : RowPointers ((B.execute f hf T hT X).termChain (B.records f hf T hT X) z))
    (leaves : X.network.Site → ℕ × ℕ) {w : ℕ} (m : Memory w)
    (hl : ∀ v, (leaves v).1 < 2 ^ w ∧ Row m (leaves v).1 (leaves v).2 [])
    (hr : rowsAt _ (selectedParsers B f hf T hT X z) ptr m (fun v => (leaves v).1)) :
    let c := (B.execute f hf T hT X).termChain (B.records f hf T hT X) z
    let trees := chainTrees c (selectedParsers B f hf T hT X z) ptr (fun v => leafTree (leaves v))
    ∀ v, ∃ es, Visits m (B.growthConstant^T) [((trees v).address : Word w)]
      ((trees v).preorder.map (fun n : ℕ => (n : Word w))) es ∧
      countProbes es < 3 * c.occurrences (fun _ => 1) v ∧
      es.length ≤ 15 * c.occurrences (fun _ => 1) v + 1 := by
  intro c trees v
  have len := chainTrees_length c (selectedParsers B f hf T hT X z) ptr
    (fun u => leafTree (leaves u)) (fun _ => 1) (fun _ => le_rfl) v
  have rows := chainTrees_rows c (selectedParsers B f hf T hT X z) ptr m
    (fun u => leafTree (leaves u)) (fun u => leafTree_rows (hl u).1 (hl u).2) hr v
  have bound := (B.branch_bounds f hf T hT X z).2.2.2.1 v
  obtain ⟨es, visit⟩ := (trees v).visits (B.growthConstant^T) rows (len.trans bound)
  obtain ⟨probes, ticks⟩ := visit.cost
  simp only [List.length_map, List.length_cons, List.length_nil] at probes ticks
  change (trees v).preorder.length ≤ c.occurrences (fun _ => 1) v at len
  exact ⟨es, visit, by omega, by omega⟩

end PairSimulation.LocalHistory

end VPVNP
end Computability
end OAI
