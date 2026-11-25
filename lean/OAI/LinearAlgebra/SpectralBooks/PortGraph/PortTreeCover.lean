import OAI.LinearAlgebra.SpectralBooks.PortGraph.PortPinning

/-! # Recognition of a replacement tree from its local port roles

Orienting each tree edge toward a root gives one parent edge for every other
vertex. A local covering lifts this edge uniquely. Following lifted parent
edges to their root assigns a root preimage to each vertex of the cover.
Both ends of an edge have the same assigned root, so the assignment is
constant on each connected component.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

namespace PortGraph

variable {V E W D : Type*} {G : PortGraph V E} {H : PortGraph W D} {r : W}

/-- Rooted description of an internally wired tree with arbitrary original
edge orientations. The edge at each nonroot vertex joins it to a vertex of
smaller depth, and these parent edges exhaust the internal wires exactly once. -/
structure RootedTreeData (H : PortGraph W D) (r : W) where
  edge : {w : W // w ≠ r} ≃ D
  side : {w : W // w ≠ r} → Bool
  at_child : ∀ w, H.vertex (edge w) (side w) = w.val
  depth : W → ℕ
  toward_root : ∀ w, depth (H.vertex (edge w) (!(side w))) < depth w.val

namespace RootedTreeData

/-- A parent-edge descent connects the root to every role of the tree. -/
theorem connected (T : RootedTreeData H r) : H.ConnectedFrom r := by
  intro w
  induction w using (measure T.depth).wf.induction with
  | h w ih =>
    by_cases hw : w = r
    · subst w
      exact .refl
    let s : {w : W // w ≠ r} := ⟨w, hw⟩
    refine (ih _ (T.toward_root s)).tail ⟨T.edge s, !(T.side s), rfl, ?_⟩
    simpa only [Bool.not_not] using T.at_child s

end RootedTreeData

/-- Vertices in the component containing a given internal tree vertex. -/
abbrev ComponentVertex (G : PortGraph V E) (v₀ : V) :=
  {v : V // Relation.ReflTransGen G.Adj v₀ v}

/-- A wire lies in the component exactly when its tail does. -/
abbrev ComponentEdge (G : PortGraph V E) (v₀ : V) :=
  {e : E // Relation.ReflTransGen G.Adj v₀ (G.tail e)}

private theorem component_tail_iff {v₀ : V} (e : E) (b : Bool) :
    Relation.ReflTransGen G.Adj v₀ (G.tail e) ↔ Relation.ReflTransGen G.Adj v₀ (G.vertex e b) := by
  cases b
  · exact Iff.rfl
  · exact ⟨fun h => h.tail ⟨e, false, rfl, rfl⟩, fun h => h.tail ⟨e, true, rfl, rfl⟩⟩

/-- The port graph of one connected component, retaining both endpoint directions. -/
def component (G : PortGraph V E) (v₀ : V) : PortGraph (G.ComponentVertex v₀) (G.ComponentEdge v₀) where
  tail e := ⟨G.tail e.val, e.property⟩
  head e := ⟨G.head e.val, (component_tail_iff e.val true).mp e.property⟩

@[simp] theorem component_vertex_val {v₀ : V} (e : G.ComponentEdge v₀) (b : Bool) :
    ((G.component v₀).vertex e b).val = G.vertex e.val b := by cases b <;> rfl

/-- Any lifted walk from the chosen vertex stays in its internal component. -/
theorem component_connected (G : PortGraph V E) (v₀ : V) :
    (G.component v₀).ConnectedFrom ⟨v₀, .refl⟩ := by
  rintro ⟨x, hx⟩
  induction hx with
  | refl => exact .refl
  | tail h hstep ih =>
    obtain ⟨e, b, h₁, h₂⟩ := hstep
    let e' : G.ComponentEdge v₀ := ⟨e, (component_tail_iff e b).mpr (h₁.symm ▸ h)⟩
    exact ih.tail ⟨e', b, Subtype.ext ((component_vertex_val _ _).trans h₁),
      Subtype.ext ((component_vertex_val _ _).trans h₂)⟩

namespace Covering

noncomputable section
open scoped Classical

variable (f : Covering G H) (T : RootedTreeData H r)

private def upEdge (v : V) (h : f.vertexName v ≠ r) : E :=
  let s := (⟨f.vertexName v, h⟩ : {w : W // w ≠ r})
  (f.lift (T.edge s) (T.side s) v (T.at_child s).symm).exists.choose

private theorem upEdge_spec (v : V) (h : f.vertexName v ≠ r) :
    let s := (⟨f.vertexName v, h⟩ : {w : W // w ≠ r})
    G.vertex (f.upEdge T v h) (T.side s) = v ∧ f.edgeName (f.upEdge T v h) = T.edge s :=
  (f.lift _ _ v (T.at_child ⟨f.vertexName v, h⟩).symm).exists.choose_spec

private def upVertex (v : V) (h : f.vertexName v ≠ r) : V :=
  G.vertex (f.upEdge T v h) (!(T.side ⟨f.vertexName v, h⟩))

private theorem upVertex_depth (v : V) (h : f.vertexName v ≠ r) :
    T.depth (f.vertexName (f.upVertex T v h)) < T.depth (f.vertexName v) := by
  rw [upVertex, f.incidence, (f.upEdge_spec T v h).2]
  exact T.toward_root _

/-- End of the unique lift of the parent path from a vertex to the root role. -/
private def rootLift (v : V) : V :=
  if h : f.vertexName v = r then v else rootLift (f.upVertex T v h)
termination_by T.depth (f.vertexName v)
decreasing_by exact f.upVertex_depth T v h

private theorem rootLift_name (v : V) : f.vertexName (f.rootLift T v) = r := by
  induction v using (measure (T.depth ∘ f.vertexName)).wf.induction with
  | h v ih =>
    rw [rootLift]
    split_ifs with hv
    · exact hv
    · exact ih _ (f.upVertex_depth T v hv)

private theorem rootLift_edge (e : E) :
    f.rootLift T (G.vertex e false) = f.rootLift T (G.vertex e true) := by
  let s := T.edge.symm (f.edgeName e)
  have he : T.edge s = f.edgeName e := T.edge.apply_symm_apply _
  let b := T.side s
  have hv : f.vertexName (G.vertex e b) = s.val := by rw [f.incidence, ← he]; exact T.at_child s
  have hn : f.vertexName (G.vertex e b) ≠ r := hv ▸ s.property
  have hs : (⟨f.vertexName (G.vertex e b), hn⟩ : {w : W // w ≠ r}) = s := Subtype.ext hv
  have hu : f.upEdge T (G.vertex e b) hn = e := by
    apply (f.lift (T.edge s) b (G.vertex e b) (hv.trans (T.at_child s).symm)).unique
    · simpa only [hs] using f.upEdge_spec T (G.vertex e b) hn
    · exact ⟨rfl, he.symm⟩
  have h : f.rootLift T (G.vertex e b) = f.rootLift T (G.vertex e (!b)) := by
    rw [rootLift, dite_eq_right hn, upVertex, hu, hs]
  cases hb : b
  · simpa only [hb, Bool.not_false] using h
  · simpa only [hb, Bool.not_true] using h.symm

include T

/-- On a connected component of a port cover of a tree, exactly one vertex
carries the root role. The connected source may be based at any vertex. -/
theorem unique_root_of_tree {v₀ : V} (hc : G.ConnectedFrom v₀) :
    ∃! v, f.vertexName v = r := by
  have same (v : V) : f.rootLift T v₀ = f.rootLift T v := by
    induction hc v with
    | refl => rfl
    | tail _ hadj ih =>
      obtain ⟨e, b, rfl, rfl⟩ := hadj
      apply ih.trans
      cases b
      · exact f.rootLift_edge T e
      · exact (f.rootLift_edge T e).symm
  refine ⟨f.rootLift T v₀, f.rootLift_name T _, fun v hv => ?_⟩
  simpa only [rootLift.eq_def f T v, dite_eq_left hv] using (same v).symm

/-- A locally bijective role assignment identifies a whole connected
internal component with one copy of its designated tree, on vertices and
on labelled edges. No pinned root in the component is required. -/
theorem bijective_names_of_tree {v₀ : V} (hc : G.ConnectedFrom v₀) :
    Function.Bijective f.vertexName ∧ Function.Bijective f.edgeName :=
  f.bijective_names T.connected (f.unique_root_of_tree T hc)

/-- Restrict the local role map to the connected component of one actual
vertex. Every lift of a port used here belongs to that component. -/
def onComponent (v₀ : V) : Covering (G.component v₀) H where
  vertexName x := f.vertexName x.val
  edgeName e := f.edgeName e.val
  incidence e b := by rw [component_vertex_val, f.incidence]
  lift d b x h := by
    obtain ⟨e, he, hu⟩ := f.lift d b x.val h
    let e' : G.ComponentEdge v₀ := ⟨e, (component_tail_iff e b).mpr (he.1.symm ▸ x.property)⟩
    refine ⟨e', ⟨Subtype.ext ((component_vertex_val _ _).trans he.1), he.2⟩, ?_⟩
    intro y hy
    exact Subtype.ext (hu _ ⟨(component_vertex_val y b).symm.trans (congrArg Subtype.val hy.1), hy.2⟩)

/-- Even when the internal-edge graph is disconnected, each of its components
contains precisely one vertex of every role and one copy of every internal
tree edge. -/
theorem bijective_component_names_of_tree (v₀ : V) :
    Function.Bijective (fun x : G.ComponentVertex v₀ => f.vertexName x.val) ∧
    Function.Bijective (fun e : G.ComponentEdge v₀ => f.edgeName e.val) :=
  (f.onComponent v₀).bijective_names_of_tree T (G.component_connected v₀)

end
end Covering
end PortGraph

end SpectralBooks
end LinearAlgebra
end OAI
