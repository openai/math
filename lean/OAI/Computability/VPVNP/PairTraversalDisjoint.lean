import OAI.Computability.VPVNP.PairTraversalRows
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.OfFn

/-!
# Distinct argument frames in a selected vertex history

Every old site is placed at a single new site. Distinct placement fibers
therefore contribute disjoint old subtrees, and their new headers occupy
the next row layer. As a result each node address occurs only once during
the traversal, and the pending siblings use distinct argument intervals.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.TraversalRows

open LocalHistory NetworkKernel Compression DFS
open private addTree from OAI.Computability.VPVNP.PairTraversalHistory

variable {A : Type*} [CommRing A] {L : Type} [Fintype L] {κ : L → A} {N Y : Network}

/-- Each selected tree's preorder has distinct addresses, different roots have disjoint
preorders, and all visited addresses lie below the stated bound. -/
structure ForestBelow {I : Type} (bound : ℕ) (trees : I → VertexTree) : Prop where
  unique : ∀ u, (trees u).preorder.Nodup
  owner : ∀ u v x, x ∈ (trees u).preorder → x ∈ (trees v).preorder → u = v
  below : ∀ u x, x ∈ (trees u).preorder → x < bound

private theorem ptr_injective {I : Type} (o : Order I) (cap base : ℕ) :
    Function.Injective (fun v => (sitePointers cap base o v).1) := by
  intro u v h
  change base + (cap+2)*(o.entries.symm u).val = base + (cap+2)*(o.entries.symm v).val at h
  exact o.entries.symm.injective
    (Fin.ext (Nat.eq_of_mul_eq_mul_left (by omega) (Nat.add_left_cancel h)))

private theorem ptr_bounds {I : Type} (o : Order I) (cap base : ℕ) (u : I) :
    base ≤ (sitePointers cap base o u).1 ∧
      (sitePointers cap base o u).1 < address cap base o.length := by
  exact ⟨Nat.le_add_right _ _, Nat.add_lt_add_left (Nat.mul_lt_mul_of_pos_left
    (o.entries.symm u).isLt (by omega)) _⟩

private theorem leafBelow {I : Type} (o : Order I) (cap base : ℕ) :
    ForestBelow (address cap base o.length) (fun u => leafTree (sitePointers cap base o u)) := by
  have eqn u : (leafTree (sitePointers cap base o u)).preorder =
      [(sitePointers cap base o u).1] := rfl
  refine ⟨fun u => by simp [eqn], fun u v x hu hv => ?_, fun u x hx => ?_⟩
  · rw [eqn, List.mem_singleton] at hu hv
    exact ptr_injective o cap base (hu.symm.trans hv)
  · rw [eqn, List.mem_singleton] at hx
    exact hx ▸ (ptr_bounds o cap base u).2

private theorem pushBelow {t : Term A N} (r : TermParsers κ t) (cap base : ℕ)
    (o : Order t.output.Site) (trees : N.Site → VertexTree) (old : ForestBelow base trees) :
    ForestBelow (address cap base o.length) (addTree r (sitePointers cap base o) trees) := by
  let kids v := List.ofFn fun i => (trees ((r.order.children v).entries i).val).preorder
  let root v := (sitePointers cap base o v).1
  have pre v : (addTree r (sitePointers cap base o) trees v).preorder =
      root v :: (kids v).flatten := rfl
  have mem {v x} : x ∈ (kids v).flatten ↔ ∃ u : t.Preimage v, x ∈ (trees u.val).preorder := by
    rw [List.mem_flatten]
    constructor
    · rintro ⟨xs, hs, hx⟩
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hs
      exact ⟨_, hx⟩
    · rintro ⟨u, hx⟩
      exact ⟨_, List.mem_ofFn.mpr ⟨(r.order.children v).entries.symm u, by simp⟩, hx⟩
  have low {v x} (hx : x ∈ (kids v).flatten) : x < base := by
    obtain ⟨u, hu⟩ := mem.mp hx
    exact old.below _ _ hu
  have separated (v) : (kids v).Pairwise List.Disjoint := by
    apply List.pairwise_ofFn.mpr
    intro i j hij x hi hj
    have eqn := old.owner _ _ x hi hj
    exact hij.ne ((r.order.children v).entries.injective (Subtype.ext eqn))
  refine ⟨fun v => ?_, fun u v x hu hv => ?_, fun v x hx => ?_⟩
  · rw [pre, List.nodup_cons, List.nodup_flatten]
    refine ⟨fun h => (low h).not_ge (ptr_bounds o cap base v).1, ?_, separated v⟩
    intro xs hxs
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hxs
    exact old.unique _
  · rw [pre, List.mem_cons] at hu hv
    rcases hu with h | h <;> rcases hv with h' | h'
    · exact ptr_injective o cap base (h.symm.trans h')
    · exact False.elim ((low h').not_ge (h ▸ (ptr_bounds o cap base u).1))
    · exact False.elim ((low h).not_ge (h' ▸ (ptr_bounds o cap base v).1))
    · obtain ⟨p, hp⟩ := mem.mp h
      obtain ⟨q, hq⟩ := mem.mp h'
      exact p.property.trans ((congrArg t.place (old.owner _ _ x hp hq)).trans q.property.symm)
  · rw [pre, List.mem_cons] at hx
    rcases hx with h | h
    · exact h ▸ (ptr_bounds o cap base v).2
    · exact (low h).trans_le (Nat.le_add_right _ _)

/-- Appending every selected stage preserves the partition into disjoint
trees and the absence of repeated addresses within each tree. -/
theorem chainTrees_unique (cap : ℕ) (c : TermChain A N Y) (r : ChainParsers κ c)
    (ords : ChainOrders c) (base : ℕ) (trees : N.Site → VertexTree) (old : ForestBelow base trees) :
    ∃ bound, ForestBelow bound (chainTrees c r (chainPointers cap c ords base) trees) := by
  induction c generalizing base with
  | done => exact ⟨base,old⟩
  | more t rec tail ih =>
    exact ih r.2 ords.2 (address cap base ords.1.length) _
      (pushBelow r.1 cap base ords.1 trees old)

/-- No two simultaneous child or sibling argument buffers of a selected
cursor branch can refer to the same row. Each final vertex visits every
descendant once and distinct final vertices visit disjoint descendants. -/
theorem selected_preorders {k : Type*} [Field k] {S : BlockSchedule k}
    (B : S.Templates) (f : B.Entry → A) (hf : B.IsSolution f) {lanes : ℕ}
    (T : ℕ) (hT : T * S.laneBits ≤ lanes) (X : State (S.degreeExponent 0) lanes)
    (z : (B.execute f hf T hT X).Choices) (base : ℕ) :
    let E := B.execute f hf T hT X
    let data := B.records f hf T hT X
    let c := E.termChain data z
    let ptr := chainPointers B.recordLimit c (branchOrders E data z)
      (address B.recordLimit base (siteOrder X).length)
    let trees := chainTrees c (selectedParsers B f hf T hT X z) ptr
      (fun v => leafTree (sitePointers B.recordLimit base (siteOrder X) v))
    (∀ v, (trees v).preorder.Nodup) ∧
      ∀ u v j, j ∈ (trees u).preorder → j ∈ (trees v).preorder → u = v := by
  intro E data c ptr trees
  obtain ⟨_, ok⟩ := chainTrees_unique B.recordLimit c (selectedParsers B f hf T hT X z)
    (branchOrders E data z) _ _ (leafBelow (siteOrder X) B.recordLimit base)
  exact ⟨ok.unique, ok.owner⟩

end PairSimulation.TraversalRows

end VPVNP
end Computability
end OAI
