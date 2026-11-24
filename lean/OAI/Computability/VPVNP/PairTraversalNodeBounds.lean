import OAI.Computability.VPVNP.PairTraversalDisjoint
import Mathlib.Data.List.Chain

/-!
# Addresses of the selected placement trees

The leaf and intermediate layers occupy consecutive row intervals in increasing
stage order. Every header read in a final vertex's preorder lies below the end
of these layers. A stored child pointer recovers the exact address of its row
in the preceding layer when the table fits in memory.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.TraversalRows

open LocalHistory NetworkKernel Compression DFS BurstRAM
open scoped Fin.CommRing
open private leafBelow pushBelow from OAI.Computability.VPVNP.PairTraversalDisjoint

variable {A : Type*} [CommRing A] {L : Type} [Fintype L] {κ : L → A} {N Y : Network}

/-- Advancing the base through the same rows as the builder gives the sum
of the preceding layer sizes. -/
theorem endPos_fold (cap start : ℕ) (layers : List Layer) :
    layers.foldl (endPos cap) start = start + words cap layers := by
  induction layers generalizing start with
  | nil => simp [words]
  | cons l ls ih => simp [ih, endPos, address, words, Nat.mul_add, Nat.add_assoc]

/-- Every row in a layer after the preceding layers has its header inside the
allocated descriptor interval. -/
theorem layerNode_bounds (cap start : ℕ) (before : List Layer) (l : Layer)
    (suffix : List Layer) (i : Fin l.count) :
    start ≤ address cap (start + words cap before) i.val ∧
      address cap (start + words cap before) i.val <
        start + words cap (before ++ l :: suffix) := by
  have hi := Nat.mul_lt_mul_of_pos_left i.isLt (by omega : 0 < cap + 2)
  simp only [address, words, List.map_append, List.sum_append, List.map_cons, List.sum_cons,
    Nat.mul_add]
  omega

/-- The site identifiers of the later layer are row indices in the earlier layer. -/
def Layer.ChildrenIn (previous next : Layer) : Prop :=
  ∀ i, ∀ j ∈ next.ids i, j < previous.count

private theorem stepLayers_childrenIn (c : TermChain A N Y) (r : ChainParsers κ c)
    (ords : ChainOrders c) (initial : Order N.Site) (previous : Layer)
    (hcount : previous.count = initial.length) :
    (previous :: stepLayers c r ords initial).IsChain Layer.ChildrenIn := by
  induction c generalizing previous with
  | done => exact List.IsChain.singleton _
  | more t data tail ih =>
    apply List.isChain_cons_cons.mpr
    exact ⟨fun i j hj => hcount ▸ stepLayer_ids_lt initial ords.1 r.1 i j hj,
      ih r.2 ords.2 ords.1 _ rfl⟩

/-- The child-index range property holds at every pair of consecutive selected layers. -/
theorem chainLayers_childrenIn (c : TermChain A N Y) (r : ChainParsers κ c)
    (ords : ChainOrders c) (initial : Order N.Site) :
    (chainLayers c r ords initial).IsChain Layer.ChildrenIn :=
  stepLayers_childrenIn c r ords initial _ rfl

/-- Reading a row's child pointer words gives exactly the preceding-layer
row addresses in order, including when the row has no children. -/
theorem childWords_val (cap start : ℕ) {w : ℕ} (before : List Layer) (previous next : Layer)
    (suffix : List Layer) (i : Fin next.count) (hids : previous.ChildrenIn next)
    (fit : start + words cap (before ++ previous :: next :: suffix) ≤ 2 ^ w) :
    (childWords w cap (start + words cap before) next i).map Fin.val =
      (next.ids i).map (address cap (start + words cap before)) := by
  simp only [childWords, List.map_map]
  apply List.map_congr_left
  intro j hj
  have hn := (layerNode_bounds cap start before previous (next :: suffix)
    ⟨j, hids i j hj⟩).2
  exact Nat.mod_eq_of_lt (hn.trans_le fit)

/-- Specialize exact child pointer decoding to any consecutive layers in
the actual parser chain, without assuming a bound on the raw child indices. -/
theorem chain_childWords_val (c : TermChain A N Y) (r : ChainParsers κ c)
    (ords : ChainOrders c) (initial : Order N.Site) (cap start : ℕ) {w : ℕ}
    {before suffix : List Layer} {previous next : Layer}
    (h : chainLayers c r ords initial = before ++ previous :: next :: suffix)
    (fit : start + words cap (chainLayers c r ords initial) ≤ 2 ^ w) (i : Fin next.count) :
    (childWords w cap (start + words cap before) next i).map Fin.val =
      (next.ids i).map (address cap (start + words cap before)) :=
  childWords_val cap start before previous next suffix i
    (List.isChain_iff_forall_rel_of_append_cons_cons.mp (chainLayers_childrenIn c r ords initial)
      h) (h ▸ fit)

/-- The precise upper end of the forest after storing the remaining stages. -/
theorem chainTrees_below (cap : ℕ) (c : TermChain A N Y) (r : ChainParsers κ c)
    (ords : ChainOrders c) (initial : Order N.Site) (base : ℕ) (trees : N.Site → VertexTree)
    (old : ForestBelow base trees) :
    ForestBelow (base + words cap (stepLayers c r ords initial))
      (chainTrees c r (chainPointers cap c ords base) trees) := by
  induction c generalizing base with
  | done => simpa [stepLayers, words, chainTrees] using old
  | more t data tail ih =>
    have h := ih r.2 ords.2 ords.1 (address cap base ords.1.length) _
      (pushBelow r.1 cap base ords.1 trees old)
    simpa only [stepLayers, stepLayer, words, List.map_cons, List.sum_cons, Nat.mul_add,
      address, Nat.add_assoc, chainTrees, chainPointers] using h

/-- Start the forest with one leaf at each actual initial site. -/
theorem chainForest_below (cap : ℕ) (c : TermChain A N Y) (r : ChainParsers κ c)
    (ords : ChainOrders c) (initial : Order N.Site) (base : ℕ) :
    ForestBelow (base + words cap (chainLayers c r ords initial))
      (chainTrees c r (chainPointers cap c ords (address cap base initial.length))
        (fun u => leafTree (sitePointers cap base initial u))) := by
  simpa only [chainLayers, leafLayer, words, List.map_cons, List.sum_cons, Nat.mul_add,
    address, Nat.add_assoc] using
    chainTrees_below cap c r ords initial _ _ (leafBelow initial cap base)

section Selected

variable {k : Type*} [Field k] {S : BlockSchedule k} (B : S.Templates)
variable (f : B.Entry → A) (hf : B.IsSolution f) {lanes : ℕ} (T : ℕ)
variable (hT : T * S.laneBits ≤ lanes) (X : State (S.degreeExponent 0) lanes)
variable (z : (B.execute f hf T hT X).Choices) (base : ℕ)

/-- Actual placement trees visited after building this branch's row directory. -/
noncomputable abbrev selectedTrees :
    ((B.execute f hf T hT X).finalState z).network.Site → VertexTree :=
  let E := B.execute f hf T hT X
  let data := B.records f hf T hT X
  let c := E.termChain data z
  let ptr := chainPointers B.recordLimit c (branchOrders E data z)
    (address B.recordLimit base (siteOrder X).length)
  chainTrees c (selectedParsers B f hf T hT X z) ptr
    (fun u => leafTree (sitePointers B.recordLimit base (siteOrder X) u))

/-- Every visited node lies strictly below the exclusive end of the actual
descriptor region of the selected branch. -/
theorem selectedTrees_below (v : ((B.execute f hf T hT X).finalState z).network.Site)
    {node : ℕ} (hn : node ∈ (selectedTrees B f hf T hT X z base v).preorder) :
    node < base + words B.recordLimit (selectedLayers B f hf T hT X z) :=
  (chainForest_below B.recordLimit _ (selectedParsers B f hf T hT X z) _ (siteOrder X)
    base).below v node hn

end Selected

end PairSimulation.TraversalRows

end VPVNP
end Computability
end OAI
