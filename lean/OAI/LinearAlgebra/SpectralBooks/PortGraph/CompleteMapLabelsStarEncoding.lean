import OAI.LinearAlgebra.SpectralBooks.PortGraph.CompleteMapLabelsStar

/-! # Completeness of the tree, face, and Euler checks on encoded records -/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

noncomputable section

namespace PortGraph.MapLabels

open PlanarPatch PlanarCertSize

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] (M : RootedMap V E)
variable {N K : ℕ} {ε : ℝ} {c : RootedMap.Certificate V E}

/-- A simultaneous certificate satisfies every one-step vertex test after its
named darts and tree fields have been packed in the common bounded alphabet. -/
theorem encode_starTest (hN : 1 ≤ N) (h : M.CertificateChecks N K ε c) (v : V) :
    starTest (PortView.actual M.slots (M.encodeBase hN h) 1 v) := by
  let b := M.encodeBase hN h
  have ht : TypesAgree M b := fun _ => ⟨rfl,rfl⟩
  have hn : M.NameChecks (treeRecord b) := h.tree
  have hp (w : V) : vertexVal (b w) .parentPort = parentCode M _ hn.distances w := rfl
  have tree := (treeTest_iff M b (fun w => (ht w).1)).mpr ⟨hn,hp,h.cap⟩
  let := M.graph.namedPortOrder ⟨c.name,h.tree.name_injective⟩ M.slots
  have ho := selfKey_strictMono M b hn.name_injective
  have hclaim (d : E × Bool) : atDart M b faceKey d = atDart M b selfKey (c.face d).1 := by
    change toLex (M.portField (c := c) _ _ .minimumVertex, M.portField (c := c) _ _ .minimumPort) = _
    simp only [RootedMap.portField,slotFace_port]
    rfl
  have hdist (d : E × Bool) :
      atDart M b (fun x i => portVal x i .forwardDistance) d = (c.face d).2 := by
    change M.portField (c := c) _ _ .forwardDistance = _
    simp only [RootedMap.portField,slotFace_port]
  have face : ∀ w, faceTest (PortView.actual M.slots b 1 w) := by
    apply (faceTest_iff M b (fun w => (ht w).2)).mpr
    refine ⟨?_,?_⟩
    · rw [funext hclaim,funext hdist]
      exact codedFaceEquations_of_valid _ _ ho h.face
    · intro w i hi f
      change M.portField (c := c) w i f = 0
      cases f <;> simp [RootedMap.portField,slotFace_none _ _ _ _ _ _ hi]
  have edgeWeights := tailCount_eq M b (fun w => (ht w).2)
  have faceWeights := markedCount_eq M b (fun w => (ht w).2) ho.injective hclaim
  refine ⟨tree v,face v,?_,?_,?_⟩
  · change subtreeTest .subtreeEdges (tailCount (b v)) (PortView.actual M.slots b 1 v)
    rw [edgeWeights]
    exact (subtreeTest_iff M b hn.distances hp .subtreeEdges (edgeWeight M.graph)).mpr h.edges v
  · change subtreeTest .subtreeFaces (markedCount (b v)) (PortView.actual M.slots b 1 v)
    rw [faceWeights]
    exact (subtreeTest_iff M b hn.distances hp .subtreeFaces (faceWeight M.graph c.face)).mpr h.faces v
  · intro hr
    have hroot : v = M.root := decide_eq_true_iff.mp hr
    subst v
    change (c.size M.root : ℤ) - c.edges M.root +
      (if baseDegree (b M.root) = 0 then 1 else c.faces M.root : ℕ) = 2
    rw [baseDegree_eq _ _ (ht _).2]
    exact h.euler

end PortGraph.MapLabels

end

end SpectralBooks
end LinearAlgebra
end OAI
