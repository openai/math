import OAI.LinearAlgebra.SpectralBooks.PortGraph.PlanarPatchRecordChecks
import OAI.LinearAlgebra.SpectralBooks.PortGraph.ReplacementOldMap
import OAI.LinearAlgebra.SpectralBooks.PortGraph.RootedMapRelabel

/-! # The original map recovered from its extracted records

The names of the two stubs of a cut wire are recovered from its two numbered
darts. Thus reassembly preserves both the original incidence and the original
port number, also for parallel edges and internal loops.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

noncomputable section
open scoped Classical

namespace PortGraph.PatchRecord
variable {V E A J : Type} [Fintype V] [Fintype E] [DecidableEq V] {K : ℕ}

/-- Nonempty bounded blocks indexed by an occurrence of each vertex. -/
structure Partition (V J : Type) [Fintype V] (K : ℕ) where
  part : V → J
  block : J → Finset V
  mem_block : ∀ j v, v ∈ block j ↔ part v = j
  nonempty : ∀ j, (block j).Nonempty
  bounded : ∀ j, (block j).card ≤ K

namespace Partition
variable (P : Partition V J K) (M : RootedMap V E) (z : V → A) (name : V ↪ ℕ)
include P

abbrev record (j : J) := extract M z (P.block j) name (P.nonempty j) (P.bounded j)
abbrev vertexAt (j : J) := slots (P.block j) name

omit [DecidableEq V] in
theorem owns (j : J) (i : Fin (P.block j).card) : P.part (P.vertexAt name j i) = j :=
  (P.mem_block j _).mp ((slotOrder (P.block j) name i).property)

omit [DecidableEq V] in
private theorem slot_range (j : J) (v : V) : (∃ i, P.vertexAt name j i = v) ↔ P.part v = j :=
  (mem_slots_iff (P.block j) name v).trans (P.mem_block j v)

/-- The occurrence and its sorted vertex number give every original vertex
exactly once. -/
def oldVertex : vertices (P.record M z name) ≃ V :=
  Equiv.ofBijective (fun q => P.vertexAt name q.1 q.2) <| by
    constructor
    · rintro ⟨i,u⟩ ⟨j,v⟩ h
      change P.vertexAt name i u = P.vertexAt name j v at h
      obtain rfl : i = j := ((P.owns name i u).symm.trans (congrArg P.part h)).trans (P.owns name j v)
      exact congrArg (Sigma.mk i) ((P.vertexAt name i).injective h)
    · intro v
      obtain ⟨i,hi⟩ := (P.slot_range name (P.part v) v).mpr rfl
      exact ⟨⟨_,i⟩,hi⟩

abbrev oldDart (j : J) (p : (P.record M z name j).shape.Dart) : E × Bool :=
  actual M (P.vertexAt name j) p

theorem owner_dart (j : J) (p : (P.record M z name j).shape.Dart) :
    P.part (M.graph.vertex (P.oldDart M z name j p).1 (P.oldDart M z name j p).2) = j :=
  (congrArg P.part (actual_owner M _ p)).trans (P.owns name j p.1)

theorem isStub (j : J) (p : (P.record M z name j).shape.Dart) :
    (P.record M z name j).shape.opposite p = p ↔
    P.part (M.graph.vertex (P.oldDart M z name j p).1 (!(P.oldDart M z name j p).2)) ≠ j :=
  (extract_stub_iff M z (P.block j) name _ _ p).trans (not_congr (P.mem_block j _))

omit P [Fintype V] [Fintype E] [DecidableEq V] in
private theorem cross_of_side (G : PortGraph V E) (p : V → J) (j : J) (q : E × Bool)
    (h : p (G.vertex q.1 (!q.2)) ≠ j) (ho : p (G.vertex q.1 q.2) = j) :
    p (G.tail q.1) ≠ p (G.head q.1) := by
  obtain ⟨e,(_|_)⟩ := q
  · exact fun eq => h (eq.symm.trans ho)
  · exact fun eq => h (eq.trans ho)

/-- Reading the two endpoints of the named cut edges amounts exactly to
listing all fixed ports of all canonical records. -/
def cutDarts : (Σ j, (P.record M z name j).shape.Stub) ≃ M.graph.CrossEdge P.part × Bool :=
  Equiv.ofBijective (fun ⟨j,s⟩ =>
    let q := P.oldDart M z name j s.val
    have h := (P.isStub M z name j s.val).mp s.property
    have ho := P.owner_dart M z name j s.val
    (⟨q.1,by
      exact cross_of_side M.graph P.part j q h ho⟩, q.2)) <| by
    constructor
    · rintro ⟨j,s⟩ ⟨k,t⟩ h
      have hd : P.oldDart M z name j s.val = P.oldDart M z name k t.val :=
        Prod.ext (congrArg (fun d => d.1.val) h) (congrArg (fun d : M.graph.CrossEdge P.part × Bool => d.2) h)
      obtain rfl : j = k := ((P.owner_dart M z name j s.val).symm.trans
        (congrArg (fun q : E × Bool => P.part (M.graph.vertex q.1 q.2)) hd)).trans (P.owner_dart M z name k t.val)
      exact congrArg (Sigma.mk j) (Subtype.ext (actual_injective M _ hd))
    · rintro ⟨e,b⟩
      let j := P.part (M.graph.vertex e.val b)
      obtain ⟨p,hp⟩ := (actual_range M (P.vertexAt name j) (e.val,b)).mpr ((P.slot_range name _ _).mpr rfl)
      have hs : (P.record M z name j).shape.opposite p = p := by
        apply (P.isStub M z name j p).mpr
        change P.part (M.graph.vertex (actual M _ p).1 (!(actual M _ p).2)) ≠ j
        rw [hp]
        cases b
        · exact e.property.symm
        · exact e.property
      exact ⟨⟨j,p,hs⟩,Prod.ext (Subtype.ext (congrArg Prod.fst hp)) (congrArg (fun d : E × Bool => d.2) hp)⟩

theorem cutDarts_read (j : J) (s : (P.record M z name j).shape.Stub) :
    ((P.cutDarts M z name ⟨j,s⟩).1.val,(P.cutDarts M z name ⟨j,s⟩).2) = P.oldDart M z name j s.val := rfl

theorem stubDart (q : M.graph.CrossEdge P.part × Bool) :
    P.oldDart M z name ((P.cutDarts M z name).symm q).1 ((P.cutDarts M z name).symm q).2.val =
      (q.1.val,q.2) :=
  (P.cutDarts_read M z name _ _).symm.trans
    (congrArg (fun d : M.graph.CrossEdge P.part × Bool => (d.1.val,d.2)) ((P.cutDarts M z name).apply_symm_apply q))

/-- Pair the actual old stubs along their original wires. -/
def pairing : StubPairing (fun j => (P.record M z name j).shape.Stub) where
  Wire := M.graph.CrossEdge P.part
  ends := (P.cutDarts M z name).symm
  cross e h := e.property <| by
    have ho (b : Bool) : P.part (M.graph.vertex e.val b) = ((P.cutDarts M z name).symm (e,b)).1 :=
      (congrArg (fun q : E × Bool => P.part (M.graph.vertex q.1 q.2)) (P.stubDart M z name (e,b))).symm.trans
        (P.owner_dart M z name _ _)
    exact ((ho false).trans h).trans (ho true).symm

theorem orient (e : (P.pairing M z name).Wire) (b : Bool) : ((P.pairing M z name).ends (e,b)).2.val.side = b :=
  congrArg Prod.snd (P.stubDart M z name (e,b))

/-- A record wire is exactly one internal old wire. -/
def wireEquiv (j : J) : (P.record M z name j).shape.Wire ≃ M.graph.PatchInternal P.part j :=
  Equiv.ofBijective (fun w =>
    let f := P.vertexAt name j
    let i := (Finset.card_pos.mpr (P.nonempty j))
    let h (b : Bool) := (congrArg P.part (wire_incidence M f z i (P.bounded j) w b)).trans (P.owns name j _)
    ⟨originalEdge M f z i (P.bounded j) w, h false, h true⟩) <| by
    constructor
    · intro u v h
      have hh := congrArg Subtype.val h
      change originalEdge M (P.vertexAt name j) z _ _ u = originalEdge M _ z _ _ v at hh
      apply Subtype.ext
      apply actual_injective M (P.vertexAt name j)
      exact (wire_darts M _ z _ _ u false).trans (by rw [hh]; exact (wire_darts M _ z _ _ v false).symm)
    · rintro ⟨e,ht,hh⟩
      obtain ⟨w,hw,_⟩ := existsUnique_wire M (P.vertexAt name j) z (Finset.card_pos.mpr (P.nonempty j))
        (P.bounded j) e ((P.slot_range name j _).mpr ht) ((P.slot_range name j _).mpr hh)
      exact ⟨w, Subtype.ext hw⟩

/-- After replacing each record's original internal edge names and each
cut wire by its actual old wire, all edges of the original map occur once. -/
def oldEdge : (P.pairing M z name).Edge (pieces (P.record M z name)) ≃ E :=
  ((Equiv.refl _).sumCongr (Equiv.sigmaCongrRight (P.wireEquiv M z name))).trans
    (M.graph.originalEdgeEquiv P.part)

/-- Reading a dart through its old vertex and slot returns its original
wire and side. -/
theorem read_wire (e : (P.pairing M z name).Edge (pieces (P.record M z name))) (b : Bool) :
    let d := namedDarts (P.record M z name) (P.pairing M z name) (e,b)
    P.oldDart M z name d.1.1 ⟨d.1.2,d.2⟩ = (P.oldEdge M z name e,b) := by
  rcases e with e | ⟨i,u⟩
  · exact P.stubDart M z name (e,b)
  · exact wire_darts M (P.vertexAt name i) z _ _ u b

theorem old_incidence (e : (P.pairing M z name).Edge (pieces (P.record M z name))) (b : Bool) :
    P.oldVertex M z name ((graph (P.record M z name) (P.pairing M z name)).vertex e b) =
      M.graph.vertex (P.oldEdge M z name e) b := by
  let d := namedDarts (P.record M z name) (P.pairing M z name) (e,b)
  rw [← namedDarts_owner (P.record M z name) (P.pairing M z name) (e,b)]
  exact (actual_owner M (P.vertexAt name d.1.1) ⟨d.1.2,d.2⟩).symm.trans
    (congrArg (fun q : E × Bool => M.graph.vertex q.1 q.2) (P.read_wire M z name e b))

variable [Fintype J]

def root := (P.oldVertex M z name).symm M.root

omit [Fintype J] in
theorem connected : (graph (P.record M z name) (P.pairing M z name)).ConnectedFrom (P.root M z name) := by
  let f := P.oldVertex M z name
  let g := P.oldEdge M z name
  intro v
  rw [← f.symm_apply_apply v]
  apply Relation.ReflTransGen.lift f.symm _ _ _ (M.connected _)
  rintro x y ⟨e,b,rfl,rfl⟩
  have hv (b : Bool) : f.symm (M.graph.vertex e b) =
      (graph (P.record M z name) (P.pairing M z name)).vertex (g.symm e) b := by
    apply f.injective
    rw [f.apply_symm_apply, P.old_incidence]
    exact congrArg (M.graph.vertex · b) (g.apply_symm_apply e).symm
  exact ⟨g.symm e,b,(hv b).symm,(hv (!b)).symm⟩

/-- Gluing all canonical old records recovers the original rooted, oriented,
port-numbered map. -/
def oldIso :
    (asMap (P.record M z name) (P.pairing M z name) (P.root M z name) (P.connected M z name)).Iso M where
  vertex := P.oldVertex M z name
  edge := P.oldEdge M z name
  incidence := P.old_incidence M z name
  root := (P.oldVertex M z name).apply_symm_apply _
  number e b := by
    let d := namedDarts (P.record M z name) (P.pairing M z name) (e,b)
    have hd := P.read_wire M z name e b
    have hs := actual_slot M (P.vertexAt name d.1.1) ⟨d.1.2,d.2⟩
    rw [asMap_portNumber]
    exact hs.symm.trans (congrArg (fun q : E × Bool => M.portNumber q.1 q.2) hd)

theorem oldIso_label (v) :
    labels (P.record M z name) v = z ((P.oldIso M z name).vertex v) := rfl

end Partition
end PortGraph.PatchRecord

end

end SpectralBooks
end LinearAlgebra
end OAI
