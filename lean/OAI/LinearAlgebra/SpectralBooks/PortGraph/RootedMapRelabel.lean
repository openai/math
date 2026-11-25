import OAI.LinearAlgebra.SpectralBooks.PortGraph.RootedMap
import OAI.Geometry.HyperbolicGroups.IndexedFillingValue

/-! # Relabelling a rooted spherical map

Bijections of the vertex and edge names transport the whole map, including
the rotations induced by its ordered ports. In particular any finite spherical
map on arbitrary types has a representative in the finite sum.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

noncomputable section
namespace PortGraph

variable {V E W D : Type*}

/-- Restrict bijective vertex and edge names to the ports incident to a vertex. -/
def incidentEquiv {G : PortGraph V E} {H : PortGraph W D} (a : V ≃ W) (b : E ≃ D)
    (inc : ∀ e t, a (G.vertex e t) = H.vertex (b e) t) (v : V) :
    G.Port v ≃ H.Port (a v) where
  toFun p := ⟨(b p.val.1, p.val.2), (inc _ _).symm.trans (congrArg a p.property)⟩
  invFun p := ⟨(b.symm p.val.1, p.val.2), a.injective (by simpa only [inc, b.apply_symm_apply] using p.property)⟩
  left_inv p := Subtype.ext (Prod.ext (b.symm_apply_apply _) rfl)
  right_inv p := Subtype.ext (Prod.ext (b.apply_symm_apply _) rfl)

namespace RootedMap

variable [Fintype V] [Fintype E] [DecidableEq V]
variable [Fintype W] [Fintype D] [DecidableEq W]

omit [Fintype W] in
private theorem slot_val_eq {G : PortGraph W D} (n : G.Numbering) {v w : W}
      (p : G.Port v) (q : G.Port w) (h : p.val = q.val) : (n v p).val = (n w q).val := by
    rcases p with ⟨p,rfl⟩
    rcases q with ⟨q,rfl⟩
    change p = q at h
    subst q
    rfl

namespace Iso

variable {M : RootedMap V E} {H : RootedMap W D} (f : M.Iso H)

abbrev portEquiv (v : V) : M.graph.Port v ≃ H.graph.Port (f.vertex v) :=
  incidentEquiv f.vertex f.edge f.incidence v

/-- A corresponding port retains its number. -/
theorem map_num (v : V) (p : M.graph.Port v) :
    (M.num v p).val = (H.num _ (f.portEquiv v p)).val := by
  rcases p with ⟨⟨e,t⟩,rfl⟩
  calc
    _ = H.portNumber (f.edge e) t := f.number e t
    _ = _ := slot_val_eq H.num ⟨_,rfl⟩ (f.portEquiv _ ⟨(e,t),rfl⟩) rfl
/-- The edge-name bijection commutes with cyclic successor on ports. -/
theorem turn (p : E × Bool) :
    (f.edge.prodCongr (Equiv.refl Bool)) (M.num.turn p) =
      H.num.turn ((f.edge.prodCongr (Equiv.refl Bool)) p) := by
  let v := M.graph.vertex p.1 p.2
  let q : M.graph.Port v := ⟨p,rfl⟩
  have hsucc : f.portEquiv v (M.num.successor v q) =
      H.num.successor _ (f.portEquiv v q) := by
    apply (H.num _).injective
    apply Fin.ext
    rw [← f.map_num, Numbering.successor, Numbering.successor]
    simp only [Equiv.permCongr_apply, Equiv.symm_symm, Equiv.apply_symm_apply]
    exact rotate_eq (Fintype.card_congr (f.portEquiv v)) (f.map_num v q)
  have h := congrArg Subtype.val hsucc
  rw [M.num.turn_port q]
  exact h.trans (H.num.turn_port (f.portEquiv v q)).symm
where
  rotate_eq {n m : ℕ} (h : n = m) {i : Fin n} {j : Fin m} (hij : i.val = j.val) :
      (finRotate n i).val = (finRotate m j).val := by
    subst m
    rw [Fin.ext hij]

include f in
/-- An isomorphism intertwines both cross and turn, so it preserves genus. -/
theorem spherical_iff [DecidableEq E] [DecidableEq D] : M.Spherical ↔ H.Spherical := by
  apply HyperbolicObstruction.PictureSwitch.PictureMap.genusZero_equiv _ _
    (f.edge.prodCongr (Equiv.refl Bool))
  · intro p
    exact f.turn (cross p)
  · exact fun _ => rfl

end Iso

variable (M : RootedMap V E) (a : V ≃ W) (b : E ≃ D)

/-- Transport of the two endpoint functions along names. -/
def relabelGraph : PortGraph W D where
  tail d := a (M.graph.tail (b.symm d))
  head d := a (M.graph.head (b.symm d))

omit [Fintype W] [Fintype D] [DecidableEq W] in
theorem relabelGraph_vertex (d : D) (t : Bool) :
    (M.relabelGraph a b).vertex d t = a (M.graph.vertex (b.symm d) t) := by
  cases t <;> rfl

private def originalPorts (w : W) : (M.relabelGraph a b).Port w ≃ M.graph.Port (a.symm w) :=
  incidentEquiv a.symm b.symm (by intro d t; rw [M.relabelGraph_vertex, a.symm_apply_apply]) w

/-- Give the relabelled ports their original consecutive numbers. -/
def relabel (M : RootedMap V E) (a : V ≃ W) (b : E ≃ D) : RootedMap W D where
  graph := M.relabelGraph a b
  root := a M.root
  num w := ((M.originalPorts a b w).trans (M.num _)).trans
    (finCongr (Fintype.card_congr (M.originalPorts a b w)).symm)
  degree w := (Fintype.card_congr (M.originalPorts a b w)).trans_le (M.degree _)
  connected w := by
    rw [← a.apply_symm_apply w]
    apply Relation.ReflTransGen.lift a _ _ _ (M.connected _)
    rintro x y ⟨e,t,rfl,rfl⟩
    exact ⟨b e,t,by simp [M.relabelGraph_vertex],by simp [M.relabelGraph_vertex]⟩

/-- Relabelling is a map isomorphism. -/
def relabelIso : M.Iso (M.relabel a b) where
  vertex := a
  edge := b
  incidence e t := by
    change _ = (M.relabelGraph a b).vertex _ _
    rw [M.relabelGraph_vertex, b.symm_apply_apply]
  root := rfl
  number e t := by
    change (M.num _ ⟨(e,t),rfl⟩).val =
      (M.num _ ((M.originalPorts a b _) ⟨(b e,t),rfl⟩)).val
    exact slot_val_eq M.num _ _ (Prod.ext (b.symm_apply_apply e).symm rfl)

/-- Every finite spherical map within the vertex cap has a named representative
in the quotient. The edge cap follows by counting the two ports of each wire. -/
def toRep [DecidableEq E] {N : ℕ} (hN : Fintype.card V ≤ N) (hs : M.Spherical) : MapRep N where
  vertexCount := ⟨_, Nat.lt_succ_of_le hN⟩
  edgeCount := ⟨_, Nat.lt_succ_of_le (PlanarCertSize.card_edges_le _ hN M.degree)⟩
  map := M.relabel (Fintype.equivFin V) (Fintype.equivFin E)
  spherical := (M.relabelIso _ _).spherical_iff.mp hs

/-- The presentation on integer names is isomorphic to the original map. -/
def toRepIso [DecidableEq E] {N : ℕ} (hN : Fintype.card V ≤ N) (hs : M.Spherical) :
    M.Iso (M.toRep hN hs).map := M.relabelIso _ _

/-- The isomorphism class of an arbitrary finite spherical map. -/
def toClass [DecidableEq E] {N : ℕ} (hN : Fintype.card V ≤ N) (hs : M.Spherical) : MapClass N :=
  Quotient.mk _ (M.toRep hN hs)

variable {M}
/-- Passing to the finite set of classes identifies precisely the isomorphic
maps, even when their vertex and edge types differ. -/
theorem toClass_eq_iff [DecidableEq E] [DecidableEq D] {H : RootedMap W D} {N : ℕ}
    (hM : Fintype.card V ≤ N) (sM : M.Spherical) (hH : Fintype.card W ≤ N) (sH : H.Spherical) :
    M.toClass hM sM = H.toClass hH sH ↔ Nonempty (M.Iso H) := by
  rw [toClass, toClass, MapClass.eq_iff_iso]
  constructor
  · rintro ⟨f⟩
    exact ⟨((M.toRepIso hM sM).trans f).trans (H.toRepIso hH sH).symm⟩
  · rintro ⟨f⟩
    exact ⟨((M.toRepIso hM sM).symm.trans f).trans (H.toRepIso hH sH)⟩

end RootedMap
end PortGraph

end

end SpectralBooks
end LinearAlgebra
end OAI
