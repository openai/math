import OAI.LinearAlgebra.SpectralBooks.PortGraph.ReplacementPartition
import OAI.LinearAlgebra.SpectralBooks.PortGraph.RootedMap

/-!
# Connectivity and size of a patch replacement

Contracting each patch to a point gives the graph of occurrences with one
edge per paired wire. Walks in the old map project to this graph. They lift
to the replacement by walking inside a connected piece between successive
stubs. In a connected graph with more than one occurrence each occurrence
has a stub, so the local vertex estimates sum to at most twice the cut size.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

noncomputable section
open scoped Classical BigOperators

namespace PortGraph

universe u
variable {V E J : Type u} {S : J → Type u}

private theorem reverse_walk (G : PortGraph V E) {x y : V}
    (h : Relation.ReflTransGen G.Adj x y) : Relation.ReflTransGen G.Adj y x := by
  induction h with
  | refl => exact .refl
  | tail _ h ih =>
    obtain ⟨e,b,rfl,rfl⟩ := h
    exact ih.head ⟨e,!b,rfl,by simp⟩

namespace StubPairing

variable (C : StubPairing S)

/-- Graph on occurrences with one edge for each exterior wire. -/
def occurrenceGraph : PortGraph J C.Wire :=
  ⟨fun e => (C.ends (e,false)).1, fun e => (C.ends (e,true)).1⟩

@[simp] theorem occurrenceGraph_vertex (e : C.Wire) (b : Bool) :
    C.occurrenceGraph.vertex e b = (C.ends (e,b)).1 := by cases b <;> rfl

variable (P : ∀ j, OpenPiece (S j))

/-- Contract an assembled walk onto its sequence of occurrences, dropping
the steps on internal wires. -/
theorem project_walk {x y : Vertex P}
    (h : Relation.ReflTransGen (C.assemble P).Adj x y) :
    Relation.ReflTransGen C.occurrenceGraph.Adj x.1 y.1 := by
  induction h with
  | refl => exact .refl
  | tail _ h ih =>
    obtain ⟨(e | ⟨j,e⟩),b,rfl,rfl⟩ := h
    · exact ih.tail ⟨e,b,by cases b <;> rfl,by cases b <;> rfl⟩
    · simpa only [vertex_internal] using ih

/-- Connectivity of a decoded assembly implies connectivity of its
occurrences, because each occurrence supplies a role. -/
theorem occurrence_connected {x : Vertex P} (h : (C.assemble P).ConnectedFrom x)
    (represented : ∀ j, Nonempty (P j).Vertex) : C.occurrenceGraph.ConnectedFrom x.1 := by
  intro j
  exact C.project_walk P (h ⟨j,(represented j).some⟩)

/-- Walks inside a replacement tree remain walks after gluing. -/
theorem lift_piece_walk (j : J) {v w : (P j).Vertex}
    (h : Relation.ReflTransGen (P j).graph.Adj v w) :
    Relation.ReflTransGen (C.assemble P).Adj ⟨j,v⟩ ⟨j,w⟩ := by
  induction h with
  | refl => exact .refl
  | tail _ h ih =>
    obtain ⟨e,b,rfl,rfl⟩ := h
    exact ih.tail ⟨.inr ⟨j,e⟩,b,C.vertex_internal P j e b,C.vertex_internal P j e (!b)⟩

/-- Given connected replacements, any chosen role in the root occurrence
connects the assembled graph. -/
theorem assemble_connected {j₀ : J} (v₀ : (P j₀).Vertex)
    (hocc : C.occurrenceGraph.ConnectedFrom j₀)
    (hpiece : ∀ j, ∃ r, (P j).graph.ConnectedFrom r) :
    (C.assemble P).ConnectedFrom ⟨j₀,v₀⟩ := by
  have inside (j : J) (x y : (P j).Vertex) :
      Relation.ReflTransGen (C.assemble P).Adj ⟨j,x⟩ ⟨j,y⟩ := by
    obtain ⟨r,hr⟩ := hpiece j
    exact C.lift_piece_walk P j ((reverse_walk _ (hr x)).trans (hr y))
  rintro ⟨j,w⟩
  induction hocc j with
  | refl => exact inside _ _ _
  | tail _ h ih =>
    obtain ⟨e,b,rfl,rfl⟩ := h
    have step : (C.assemble P).Adj (C.outside P e b) (C.outside P e (!b)) :=
      ⟨.inl e,b,C.vertex_exterior P e b,C.vertex_exterior P e (!b)⟩
    cases b <;> exact ((ih _).tail step).trans (inside _ _ _)

include C in
/-- A single occurrence has no exterior wires. -/
theorem isEmpty_stub_of_subsingleton [Subsingleton J] (j : J) : IsEmpty (S j) := by
  constructor
  intro s
  let e := (C.ends.symm ⟨j,s⟩).1
  exact C.cross e (Subsingleton.elim _ _)

/-- Every occurrence in a connected graph with at least two occurrences
meets an exterior wire. -/
theorem nonempty_stub [Nontrivial J] {j₀ : J}
    (hocc : C.occurrenceGraph.ConnectedFrom j₀) (j : J) : Nonempty (S j) := by
  obtain ⟨k,hk⟩ := exists_ne j
  have h := (reverse_walk _ (hocc j)).trans (hocc k)
  rcases h.cases_head with heq | ⟨l,⟨e,b,he,_⟩,_⟩
  · exact (hk heq.symm).elim
  · rw [occurrenceGraph_vertex] at he
    exact he ▸ ⟨(C.ends (e,b)).2⟩

/-- The old root occurrence marks precisely its chosen replacement role. -/
theorem existsUnique_marked {j₀ : J} (role : ∀ j, (P j).Vertex) :
    ∃! x : Vertex P, x.1 = j₀ ∧ x.2 = role x.1 := by
  refine ⟨⟨j₀,role j₀⟩, ⟨rfl,rfl⟩, ?_⟩
  rintro ⟨j,v⟩ ⟨hj,hv⟩
  change j = j₀ at hj
  subst j₀
  exact congrArg (Sigma.mk j) hv

variable [Fintype J] [∀ j, Fintype (S j)]

/-- The number of vertices after replacement satisfies the bound of the
compression step, including the single scalar patch. -/
theorem card_assemble_le {a N : ℕ} (ha : 0 < a) {j₀ : J}
    (hocc : C.occurrenceGraph.ConnectedFrom j₀)
    (localSize : ∀ j, Fintype.card (P j).Vertex ≤ max 1 (Fintype.card (S j)))
    (cutSize : Fintype.card C.Wire * (2*a) ≤ N) :
    Fintype.card (Vertex P) ≤ max 1 (N/a) := by
  rw [Fintype.card_sigma]
  rcases subsingleton_or_nontrivial J with hs | hn
  · let : Unique J := ⟨⟨j₀⟩,fun _ => Subsingleton.elim _ _⟩
    have := C.isEmpty_stub_of_subsingleton j₀
    have h : Fintype.card (P j₀).Vertex ≤ 1 := by simpa using localSize j₀
    rw [Fintype.sum_unique]
    exact h.trans (le_max_left _ _)
  · apply le_trans _ (le_max_right _ _)
    apply (Nat.le_div_iff_mul_le ha).2
    have hsum : (∑ j, Fintype.card (P j).Vertex) ≤ ∑ j, Fintype.card (S j) := by
      apply Finset.sum_le_sum
      intro j _
      have := C.nonempty_stub hocc j
      have hpos : 1 ≤ Fintype.card (S j) := Fintype.card_pos
      simpa only [max_eq_right hpos] using localSize j
    have hcard := Fintype.card_congr C.ends
    rw [Fintype.card_prod, Fintype.card_bool, Fintype.card_sigma] at hcard
    calc
      _ ≤ (∑ j, Fintype.card (S j)) * a := Nat.mul_le_mul_right a hsum
      _ = Fintype.card C.Wire * (2*a) := by rw [← hcard, Nat.mul_assoc]
      _ ≤ N := cutSize

/-- Real-valued separator budgets with ε = 1/(2a) give the integral
floor bound on the assembled vertex set. -/
theorem card_assemble_le_of_cut_budget {a N n : ℕ} (ha : 0 < a) (hn : n ≤ N) {j₀ : J}
    (hocc : C.occurrenceGraph.ConnectedFrom j₀)
    (localSize : ∀ j, Fintype.card (P j).Vertex ≤ max 1 (Fintype.card (S j)))
    (cutSize : (Fintype.card C.Wire : ℝ) ≤ 1 / (2 * (a : ℝ)) * n) :
    Fintype.card (Vertex P) ≤ max 1 (N/a) := by
  apply C.card_assemble_le P ha hocc localSize
  rw [one_div, inv_mul_eq_div] at cutSize
  have h := (le_div_iff₀ (show (0 : ℝ) < 2 * a by positivity)).mp cutSize
  exact le_trans (by exact_mod_cast h : Fintype.card C.Wire * (2*a) ≤ n) hn

/-- At each vertex, the chosen consecutive numbering is a numbering of its
local internal darts and attached stubs. -/
abbrev LocalPort (j : J) (v : (P j).Vertex) :=
  (P j).graph.Port v ⊕ {s : S j // (P j).attach s = v}

theorem card_assemble_port (j : J) (v : (P j).Vertex) :
    Fintype.card ((C.assemble P).Port ⟨j,v⟩) = Fintype.card (LocalPort P j v) :=
  Fintype.card_congr (C.portEquiv P j v)

/-- Any degree bound on the local port set holds at the assembled vertex. -/
theorem assemble_degree_le {d : ℕ} (deg : ∀ j v, Fintype.card (LocalPort P j v) ≤ d)
    (x : Vertex P) : Fintype.card ((C.assemble P).Port x) ≤ d :=
  (C.card_assemble_port P x.1 x.2).le.trans (deg x.1 x.2)

/-- Transport the piece port orders, including the exterior stubs. -/
def assembleNumbering
    (num : ∀ j v, LocalPort P j v ≃ Fin (Fintype.card (LocalPort P j v))) :
    (C.assemble P).Numbering := fun ⟨j,v⟩ =>
  ((C.portEquiv P j v).trans (num j v)).trans (finCongr (C.card_assemble_port P j v).symm)

/-- The global port number at a role is the local number of its dart or stub. -/
@[simp] theorem assembleNumbering_val
    (num : ∀ j v, LocalPort P j v ≃ Fin (Fintype.card (LocalPort P j v)))
    (j : J) (v : (P j).Vertex) (d : (C.assemble P).Port ⟨j,v⟩) :
    (C.assembleNumbering P num ⟨j,v⟩ d).val = (num j v (C.portEquiv P j v d)).val := rfl

/-- The connected numbered replacement with its marked role in the old root
occurrence as the distinguished vertex. -/
def rootedAssembly {j₀ : J} (v₀ : (P j₀).Vertex)
    (hocc : C.occurrenceGraph.ConnectedFrom j₀)
    (hpiece : ∀ j, ∃ r, (P j).graph.ConnectedFrom r)
    (num : ∀ j v, LocalPort P j v ≃ Fin (Fintype.card (LocalPort P j v)))
    (deg : ∀ j v, Fintype.card (LocalPort P j v) ≤ 4) :
    RootedMap (Vertex P) (C.Edge P) where
  graph := C.assemble P
  root := ⟨j₀,v₀⟩
  num := C.assembleNumbering P num
  degree := fun ⟨j,v⟩ => (C.card_assemble_port P j v).le.trans (deg j v)
  connected := C.assemble_connected P v₀ hocc hpiece

end StubPairing

/-- A walk in the original graph projects to a walk in the occurrence
graph after dropping steps internal to a patch. -/
theorem boundaryPairing_connected (G : PortGraph V E) [Fintype E] (p : V → J)
    (hp : Function.Surjective p) {r : V} (hG : G.ConnectedFrom r) :
    (G.boundaryPairing p).occurrenceGraph.ConnectedFrom (p r) := by
  intro j
  obtain ⟨v,rfl⟩ := hp j
  induction hG v with
  | refl => exact .refl
  | tail _ h ih =>
    obtain ⟨e,b,rfl,rfl⟩ := h
    by_cases he : p (G.tail e) = p (G.head e)
    · cases b <;> simpa [vertex,he] using ih
    · exact ih.tail ⟨⟨e,he⟩,b,by cases b <;> rfl,by cases b <;> rfl⟩

/-- Replace a partition of a rooted map by connected pieces with trivalent
or smaller local port sets. The marked role belongs to the occurrence of
the original root. -/
def rootedReplacement {V E J : Type u} [Fintype V] [Fintype E] [DecidableEq V] [Fintype J]
    (M : RootedMap V E) (p : V → J) (hp : Function.Surjective p)
    (P : ∀ j, OpenPiece (M.graph.PatchBoundary p j)) (mark : (P (p M.root)).Vertex)
    (hpiece : ∀ j, ∃ r, (P j).graph.ConnectedFrom r)
    (num : ∀ j v, StubPairing.LocalPort P j v ≃ Fin (Fintype.card (StubPairing.LocalPort P j v)))
    (deg : ∀ j v, Fintype.card (StubPairing.LocalPort P j v) ≤ 3) :
    RootedMap (StubPairing.Vertex P) ((M.graph.boundaryPairing p).Edge P) :=
  (M.graph.boundaryPairing p).rootedAssembly P mark
    (M.graph.boundaryPairing_connected p hp M.connected) hpiece num
    (fun j v => (deg j v).trans (by decide))

end PortGraph

namespace PlanarPatch.Peeling

open PortGraph

universe u
variable {V E : Type u} [Fintype V] [DecidableEq V] [Fintype E]
    {tail head : E → V} {K : ℕ} {ε : ℝ} {blocks : Finset (Finset V)}
    (h : Peeling tail head K ε Finset.univ blocks)

include h in
private theorem exists_block (v : V) : ∃ j : blocks, v ∈ j.val := by
  obtain ⟨Q,hQ,hv⟩ := Finset.mem_biUnion.mp (h.partition.1.symm ▸ Finset.mem_univ v)
  exact ⟨⟨Q,hQ⟩,hv⟩

/-- Occurrence containing a vertex of the canonical partition. -/
def blockOf (v : V) : blocks := (h.exists_block v).choose

theorem mem_blockOf (v : V) : v ∈ (h.blockOf v).val := (h.exists_block v).choose_spec

theorem blockOf_eq_iff (v : V) (j : blocks) : h.blockOf v = j ↔ v ∈ j.val := by
  refine ⟨fun he => he ▸ h.mem_blockOf v, fun hv => Subtype.ext ?_⟩
  apply h.partition.2.1.elim (h.blockOf v).property j.property
  exact fun hd => Finset.disjoint_left.mp hd (h.mem_blockOf v) hv

theorem blockOf_surjective : Function.Surjective h.blockOf := by
  intro j
  obtain ⟨v,hv⟩ := (h.partition.2.2.1 j j.property).1
  exact ⟨v,(h.blockOf_eq_iff v j).mpr hv⟩

variable {G : PortGraph V E} (h : Peeling G.tail G.head K ε Finset.univ blocks)

/-- Crossing edges in the separator estimate are exactly the wire names
of the boundary pairing. -/
def crossEquiv : G.CrossEdge h.blockOf ≃ crossing G.tail G.head Finset.univ blocks :=
  Equiv.subtypeEquivRight fun e => by
    simp only [crossing, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro hne ⟨Q,hQ,ht,hh⟩
      exact hne (((h.blockOf_eq_iff _ ⟨Q,hQ⟩).mpr ht).trans
        ((h.blockOf_eq_iff _ ⟨Q,hQ⟩).mpr hh).symm)
    · intro hsep he
      exact hsep ⟨_,(h.blockOf (G.head e)).property,
        (h.blockOf_eq_iff _ _).mp he,h.mem_blockOf _⟩

/-- The separator cut budget applies to the actual finite type of exterior wires. -/
theorem cut_budget : (Fintype.card (G.boundaryPairing h.blockOf).Wire : ℝ) ≤ ε * Fintype.card V := by
  let e : (G.boundaryPairing h.blockOf).Wire ≃ crossing G.tail G.head Finset.univ blocks :=
    h.crossEquiv
  rw [Fintype.card_congr e, Fintype.card_coe]
  simpa using h.partition.2.2.2

/-- The original piece has one vertex per member of the peeled block. -/
def oldVertexEquiv (j : blocks) : (G.originalPiece h.blockOf j).Vertex ≃ j.val :=
  Equiv.subtypeEquivRight (fun v => h.blockOf_eq_iff v j)

/-- Each old open piece meets the uniform size bound in the separator lemma. -/
theorem oldVertex_bound (j : blocks) : Fintype.card (G.originalPiece h.blockOf j).Vertex ≤ K := by
  rw [Fintype.card_congr (h.oldVertexEquiv j), Fintype.card_coe]
  exact (h.partition.2.2.1 j j.property).2.2

/-- The induced connectivity of the peeled block supplies paths on its
actual internal port graph, before replacing the block. -/
theorem oldPiece_connected (j : blocks) (r : (G.originalPiece h.blockOf j).Vertex) :
    (G.originalPiece h.blockOf j).graph.ConnectedFrom r := by
  let a := h.oldVertexEquiv j
  let L := (underlying G.tail G.head).induce (j.val : Set V)
  have conn : L.Connected := (h.partition.2.2.1 j j.property).2.1
  intro v
  have hw := (L.reachable_iff_reflTransGen (a r) (a v)).mp (conn.preconnected _ _)
  rw [← a.symm_apply_apply r, ← a.symm_apply_apply v]
  apply Relation.ReflTransGen.lift a.symm _ _ _ hw
  intro x y hadj
  obtain ⟨_,e,⟨ht,hh⟩ | ⟨ht,hh⟩⟩ := (SimpleGraph.induce_adj.mp hadj)
  · let d : G.PatchInternal h.blockOf j :=
      ⟨e,(congrArg h.blockOf ht).trans (a.symm x).property,
        (congrArg h.blockOf hh).trans (a.symm y).property⟩
    exact ⟨d,false,Subtype.ext ht,Subtype.ext hh⟩
  · let d : G.PatchInternal h.blockOf j :=
      ⟨e,(congrArg h.blockOf ht).trans (a.symm y).property,
        (congrArg h.blockOf hh).trans (a.symm x).property⟩
    exact ⟨d,true,Subtype.ext hh,Subtype.ext ht⟩

/-- The actual replacement of the chosen partition satisfies the vertex bound
for one compression step. -/
theorem replacement_size {a N : ℕ} (ha : 0 < a) (hN : Fintype.card V ≤ N)
    (h : Peeling G.tail G.head K (1 / (2 * (a : ℝ))) Finset.univ blocks)
    {r : V} (hconn : G.ConnectedFrom r)
    (P : ∀ j, OpenPiece (G.PatchBoundary h.blockOf j))
    (localSize : ∀ j, Fintype.card (P j).Vertex ≤ max 1 (Fintype.card (G.PatchBoundary h.blockOf j))) :
    Fintype.card (StubPairing.Vertex P) ≤ max 1 (N/a) :=
  (G.boundaryPairing h.blockOf).card_assemble_le_of_cut_budget P ha hN
    (G.boundaryPairing_connected h.blockOf h.blockOf_surjective hconn) localSize h.cut_budget

end PlanarPatch.Peeling

end

end SpectralBooks
end LinearAlgebra
end OAI
