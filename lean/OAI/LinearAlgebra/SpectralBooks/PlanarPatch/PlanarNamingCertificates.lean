import OAI.LinearAlgebra.SpectralBooks.PlanarPatch.PlanarPortParents
import OAI.LinearAlgebra.SpectralBooks.PlanarPreorderIntervals
import OAI.LinearAlgebra.SpectralBooks.PortGraph.PortPinning

/-! # Unique locally certified vertex names

These are the tree-based records in the proof of the map-labels lemma. The
numbered ports determine the parent map from reported distances alone, so
the size and preorder tests can use the children recognized at each vertex.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

namespace PlanarPatch

variable {V E : Type*} (G : PortGraph V E) (r : V)

/-- Reachability in a rooted port graph gives connectivity of its underlying
simple graph. Loop steps in a walk can be discarded. -/
theorem underlying_connected_of_connectedFrom (h : G.ConnectedFrom r) :
    (underlying G.tail G.head).Connected := by
  apply (underlying G.tail G.head).connected_iff_exists_forall_reachable.mpr
  refine ⟨r, fun v => ?_⟩
  induction h v with
  | refl => exact .rfl
  | @tail x y hxy hstep ih =>
    by_cases he : x = y
    · simpa [← he] using ih
    obtain ⟨e, b, h₁, h₂⟩ := hstep
    apply ih.trans (SimpleGraph.Adj.reachable ?_)
    refine ⟨he, e, ?_⟩
    cases b with
    | false => exact Or.inl ⟨h₁, h₂⟩
    | true => exact Or.inr ⟨h₂, h₁⟩

variable [Fintype V] [DecidableEq V]
variable (portNum : (v : V) → G.Port v → ℕ) (hinj : ∀ v, Function.Injective (portNum v))

/-- The integers each vertex supplies to the tree tests. -/
structure TreeNameRecord (V : Type*) where
  distance : V → ℕ
  size : V → ℕ
  name : V → ℕ

/-- Check the distance locally, choose the least closer port, then check both
the subtree sizes and one-based preorder names by their local equations. -/
structure TreeNameChecks (rec : TreeNameRecord V) : Prop where
  distances : DistanceChecks (underlying G.tail G.head) r rec.distance
  sizes : SubtreeTotals r (canonicalParent G portNum hinj distances) (fun _ => 1) rec.size
  names : PreorderNames r (canonicalParent G portNum hinj distances)
    (canonicalSiblingSlot G portNum hinj distances) rec.size rec.name

/-- Every connected rooted port graph admits exactly one passing set of tree records. -/
theorem existsUnique_treeNameRecord (hconn : G.ConnectedFrom r) :
    ∃! rec, TreeNameChecks G r portNum hinj rec := by
  let d := fun v => (underlying G.tail G.head).dist v r
  have hd : DistanceChecks (underlying G.tail G.head) r d :=
    distanceChecks_dist (underlying_connected_of_connectedFrom G r hconn) r
  let parent := canonicalParent G portNum hinj hd
  let slot := canonicalSiblingSlot G portNum hinj hd
  have hdepth (v : V) (hv : v ≠ r) : d (parent v) < d v := canonicalParent_depth_lt _ _ _ _ v hv
  obtain ⟨size, hs, hsu⟩ := existsUnique_subtreeTotals r parent d (fun _ => 1) hdepth
  obtain ⟨name, hn, hnu⟩ := existsUnique_preorderNames r parent d slot size hdepth
  refine ⟨⟨d, size, name⟩, ⟨hd, hs, hn⟩, ?_⟩
  rintro ⟨d', size', name'⟩ ⟨h₁, h₂, h₃⟩
  obtain rfl : d' = d := h₁.eq_dist
  obtain rfl : size' = size := hsu _ h₂
  obtain rfl : name' = name := hnu _ h₃
  rfl

variable {G r portNum hinj} {rec : TreeNameRecord V} (h : TreeNameChecks G r portNum hinj rec)

include h in
theorem TreeNameChecks.size_root : rec.size r = Fintype.card V := root_subtreeSize_eq_card h.sizes

include h in
private theorem TreeNameChecks.slot_injOn (v : V) :
    Set.InjOn (canonicalSiblingSlot G portNum hinj h.distances)
      ↑(treeChildren r (canonicalParent G portNum hinj h.distances) v) := by
  intro a ha b hb he
  obtain ⟨ha₁, ha₂⟩ := (Finset.mem_filter.mp ha).2
  obtain ⟨hb₁, hb₂⟩ := (Finset.mem_filter.mp hb).2
  exact canonicalSiblingSlot_injective _ _ _ _ ha₁ hb₁ (ha₂.trans hb₂.symm) he

include h in
/-- The verified preorder name supplies an injective key for the patch ordering. -/
theorem TreeNameChecks.name_injective : Function.Injective rec.name :=
  preorderName_injective r _ _ _ _ h.slot_injOn h.sizes h.size_root h.names.1 h.names.2

include h in
/-- Exactly the integer names one through the vertex count occur. -/
theorem TreeNameChecks.image_names :
    Finset.univ.image rec.name = Finset.Ico 1 (1 + Fintype.card V) :=
  preorderName_image_eq r _ _ _ _ h.slot_injOn h.sizes h.size_root h.names.1 h.names.2

include h in
theorem TreeNameChecks.name_le_card (v : V) : rec.name v ≤ Fintype.card V := by
  have hv := Finset.mem_image_of_mem rec.name (Finset.mem_univ v)
  rw [h.image_names] at hv
  have := (Finset.mem_Ico.mp hv).2
  omega

include h in
theorem TreeNameChecks.distance_lt_card (hconn : G.ConnectedFrom r) (v : V) :
    rec.distance v < Fintype.card V := by
  obtain ⟨p, hp, heq⟩ :=
    (underlying_connected_of_connectedFrom G r hconn).exists_path_of_dist v r
  simpa only [h.distances.eq_dist, ← heq] using hp.length_lt

end PlanarPatch

end SpectralBooks
end LinearAlgebra
end OAI
