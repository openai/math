import OAI.LinearAlgebra.SpectralBooks.PortGraph.CompleteMapLabelsCore

/-! # The bounded numeric alphabet of simultaneous map records -/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

noncomputable section

namespace PortGraph.RootedMap

open PlanarPatch PlanarCertSize

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]
variable (M : RootedMap V E) {N K : ℕ} {ε : ℝ} {c : Certificate V E}

/-- A zero parent field at the root and the one-based parent port elsewhere. -/
def parentField (ht : M.NameChecks c.toTreeNameRecord) (v : V) : ℕ :=
  if h : v = M.root then 0 else
    M.slotNat v (canonicalParentPort M.graph M.slotNat M.slotNat_injective ht.distances v h) + 1

/-- The exact eight coordinates recorded once at each vertex. -/
def vertexField (ht : M.NameChecks c.toTreeNameRecord) (v : V) : VertexField → ℕ
  | .distance => c.distance v
  | .parentPort => M.parentField ht v
  | .subtreeSize => c.size v
  | .preorderName => c.name v
  | .subtreeEdges => c.edges v
  | .subtreeFaces => c.faces v
  | .removalRound => (c.patch v).1
  | .patchName => (c.patch v).2

/-- The three fields at a slot, with the all-zero report on unused positions. -/
def portField (v : V) (i : Fin 4) : PortField → ℕ :=
  let z := slotFace M.graph M.slots c.name c.face v i
  fun f => match f with
    | .minimumVertex => z.1
    | .minimumPort => z.2.1
    | .forwardDistance => z.2.2

theorem vertexField_le (hN : 1 ≤ N) (h : M.CertificateChecks N K ε c) (v : V) (i : VertexField) :
    M.vertexField h.tree v i ≤ 4*N := by
  have hcard : Fintype.card V ≤ N := h.tree.size_root ▸ h.cap
  have hd := canonicalParent_depth_lt M.graph M.slotNat M.slotNat_injective h.tree.distances
  have hkey (w : V) : c.name w ≤ N := (h.tree.name_le_card w).trans hcard
  have hpatch := patchRecord_le ⟨c.name,h.tree.name_injective⟩ _ hkey h.patches (Finset.mem_univ v)
  let := M.graph.namedPortOrder ⟨c.name,h.tree.name_injective⟩ M.slots
  cases i with
  | distance => exact (h.tree.distance_lt_card M.connected v).le.trans (by omega)
  | parentPort =>
    change M.parentField h.tree v ≤ _
    unfold parentField
    split
    · omega
    · rename_i hn
      have hslot := (M.num v (canonicalParentPort M.graph M.slotNat M.slotNat_injective h.tree.distances v hn)).isLt
      change (M.num v _).val + 1 ≤ _
      have := M.degree v
      omega
  | subtreeSize => exact (subtreeSize_le_card hd h.tree.sizes v).trans (by omega)
  | preorderName => exact (hkey v).trans (by omega)
  | subtreeEdges =>
    exact (edgeTotal_le_card M.graph hd h.edges v).trans
        ((card_edges_le M.graph hcard M.degree).trans (by omega))
  | subtreeFaces =>
    exact (rawFaceTotal_le_card M.graph _ hd h.faces v).trans
        (card_ports_le M.graph hcard M.degree)
  | removalRound => exact hpatch.1.trans (by omega)
  | patchName => exact hpatch.2.trans (by omega)

theorem portField_le (hN : 1 ≤ N) (h : M.CertificateChecks N K ε c) (v : V) (i : Fin 4)
    (j : PortField) : M.portField (c := c) v i j ≤ 4*N := by
  classical
  have hcard : Fintype.card V ≤ N := h.tree.size_root ▸ h.cap
  by_cases hi : ∃ p, M.slots v p = i
  · obtain ⟨p,rfl⟩ := hi
    let := M.graph.namedPortOrder ⟨c.name,h.tree.name_injective⟩ M.slots
    cases j with
    | minimumVertex =>
      simp only [portField, slotFace_port, dartCode]
      exact (h.tree.name_le_card _).trans (by omega)
    | minimumPort =>
      simp only [portField, slotFace_port, dartCode]
      have := (M.slots _ ⟨(c.face p.val).1,rfl⟩).isLt
      omega
    | forwardDistance =>
      simp only [portField, slotFace_port]
      exact faceDistance_le _ hcard M.degree _ h.face _
  · cases j <;> simp [portField, slotFace_none _ _ _ _ _ _ hi]

/-- The type is copied at each walk endpoint. Vacant slots carry no direction. -/
def paddedDirection (θ : MapType) (i : Fin 4) : Option Bool :=
  if h : i.val < θ.degree.val then some (θ.direction ⟨i.val,h⟩) else none

/-- Pack the record into the single polynomial-size alphabet used at all maps. -/
def encodeBase (hN : 1 ≤ N) (h : M.CertificateChecks N K ε c) (v : V) : BaseAlphabet N :=
  ((M.typeAt v).root, paddedDirection (M.typeAt v), fun f => match f with
    | .inl s => ⟨M.vertexField h.tree v s, Nat.lt_succ_of_le (M.vertexField_le hN h v s)⟩
    | .inr (i,j) => ⟨M.portField (c := c) v i j, Nat.lt_succ_of_le (M.portField_le hN h v i j)⟩)

end PortGraph.RootedMap

end

end SpectralBooks
end LinearAlgebra
end OAI
