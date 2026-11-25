import OAI.LinearAlgebra.SpectralBooks.PlanarPatch.PlanarPatchPartition
import OAI.LinearAlgebra.SpectralBooks.PortNetwork
import Mathlib.Combinatorics.SimpleGraph.Metric

/-! # Canonical rooted tree certificates for planar port graphs

This is the distance-and-naming step of the proof of the map-labels lemma.
The distance tests force the graph distance. The least port leading closer
to the root determines one parent edge, even in the presence of parallel edges.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

namespace PlanarPatch

variable {V E : Type*}

/-- A zero test, a unit difference bound on edges, and descent at every nonroot. -/
structure DistanceChecks (G : SimpleGraph V) (r : V) (d : V → ℕ) : Prop where
  zero : ∀ v, d v = 0 ↔ v = r
  step : ∀ ⦃v w⦄, G.Adj v w → d v ≤ d w + 1
  descend : ∀ v, v ≠ r → ∃ w, G.Adj v w ∧ d w < d v

/-- True graph distances satisfy all three local tests on a connected graph. -/
theorem distanceChecks_dist {G : SimpleGraph V} (hG : G.Connected) (r : V) :
    DistanceChecks G r (fun v => G.dist v r) := by
  refine ⟨fun v => hG.dist_eq_zero_iff, ?_, ?_⟩
  · intro v w hvw
    simpa only [SimpleGraph.dist_eq_one_iff_adj.mpr hvw, add_comm] using
      hG.dist_triangle (u := v) (v := w) (w := r)
  · intro v hne
    obtain ⟨p, hp⟩ := hG.exists_walk_length_eq_dist v r
    cases p with
    | nil => exact False.elim (hne rfl)
    | cons e p =>
      exact ⟨_, e, (G.dist_le p).trans_lt (by simp [← hp])⟩

/-- Local descent provides a path to the root, and successive edge bounds
bound the recorded distance by the length of every such path. -/
theorem DistanceChecks.eq_dist {G : SimpleGraph V} {r : V} {d : V → ℕ} (h : DistanceChecks G r d) :
    d = fun v => G.dist v r := by
  have path_le {v w : V} (p : G.Walk v w) : d v ≤ p.length + d w := by
    induction p with
    | nil => simp
    | cons e p ih =>
      have := h.step e
      simp only [SimpleGraph.Walk.length_cons]
      omega
  have descend (v : V) : ∃ p : G.Walk v r, p.length ≤ d v := by
    induction v using (measure d).wf.induction with
    | h v ih =>
      by_cases he : v = r
      · subst v; exact ⟨.nil, Nat.zero_le _⟩
      obtain ⟨w, e, hw⟩ := h.descend v he
      obtain ⟨p, hp⟩ := ih _ hw
      exact ⟨p.cons e, by simpa only [SimpleGraph.Walk.length_cons] using (by omega : p.length + 1 ≤ d v)⟩
  funext v
  obtain ⟨p,hp⟩ := descend v
  obtain ⟨q,hq⟩ := p.reachable.exists_walk_length_eq_dist
  exact le_antisymm (by simpa [hq, (h.zero r).mpr rfl] using path_le q) ((G.dist_le p).trans hp)

/-- The far endpoint of a port's oriented wire. -/
def otherEnd (G : PortGraph V E) {v : V} (p : G.Port v) : V := G.vertex p.1.1 (!p.1.2)

private theorem exists_port_of_adj (G : PortGraph V E) {v w : V}
    (h : (underlying G.tail G.head).Adj v w) : ∃ p : G.Port v, otherEnd G p = w := by
  obtain ⟨_, e, ⟨ht, hh⟩ | ⟨hh, ht⟩⟩ := h
  · exact ⟨⟨(e, false), ht⟩, hh⟩
  · exact ⟨⟨(e, true), ht⟩, hh⟩

/-- The selected parent port leads closer and has the least local number among
all ports doing so. -/
def IsParentPort (G : PortGraph V E) (portNum : (v : V) → G.Port v → ℕ) (d : V → ℕ)
    (v : V) (p : G.Port v) : Prop :=
  d (otherEnd G p) < d v ∧ ∀ q : G.Port v, d (otherEnd G q) < d v → portNum v p ≤ portNum v q

theorem existsUnique_parentPort (G : PortGraph V E) (portNum : (v : V) → G.Port v → ℕ)
    (hinj : ∀ v, Function.Injective (portNum v)) {r : V} {d : V → ℕ}
    (hd : DistanceChecks (underlying G.tail G.head) r d) (v : V) (hne : v ≠ r) :
    ∃! p, IsParentPort G portNum d v p := by
  classical
  obtain ⟨w, h, hw⟩ := hd.descend v hne
  obtain ⟨p, hp⟩ := exists_port_of_adj G h
  let desc := fun (n : ℕ) => ∃ q : G.Port v, portNum v q = n ∧ d (otherEnd G q) < d v
  have hex : ∃ n, desc n := ⟨_, p, rfl, hp ▸ hw⟩
  obtain ⟨q, hq, hlt⟩ := Nat.find_spec hex
  have hmin : IsParentPort G portNum d v q :=
    ⟨hlt, fun q' hq' => hq ▸ Nat.find_min' hex ⟨q', rfl, hq'⟩⟩
  exact ⟨q, hmin, fun q' hq' => hinj v (le_antisymm (hq'.2 q hlt) (hmin.2 q' hq'.1))⟩

end PlanarPatch

end SpectralBooks
end LinearAlgebra
end OAI
