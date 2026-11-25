import OAI.LinearAlgebra.SpectralBooks.PortGraph.CompleteMapLabelsDecode
import OAI.LinearAlgebra.SpectralBooks.PortGraph.CompleteMapLabelsTree

/-! # The tree and Euler part of the uniform vertex table -/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

noncomputable section

namespace PortGraph.MapLabels

open PlanarPatch PlanarCertSize
open RootedMap (Certificate)

variable {N : ℕ}

/-- Euler's integer equation, read on the root label. The one-vertex map has
one exterior face. -/
def eulerTest (x : BaseAlphabet N) : Prop :=
  x.1 = true → (vertexVal x .subtreeSize : ℤ) - vertexVal x .subtreeEdges +
    (if baseDegree x = 0 then 1 else vertexVal x .subtreeFaces : ℕ) = 2

/-- The tests which use only the centered one-step view. -/
def starTest (z : PortView (BaseAlphabet N) 1) : Prop :=
  treeTest z ∧ faceTest z ∧ subtreeTest .subtreeEdges (tailCount z.1) z ∧
    subtreeTest .subtreeFaces (markedCount z.1) z ∧ eulerTest z.1

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] (M : RootedMap V E)
variable {K : ℕ} {ε : ℝ} (b : V → BaseAlphabet N)

/-- Unpack all numerical fields. Walking to a claimed minimum is defined for
any input, and the face tests ensure that it reaches the claimed coordinates. -/
def unpack : Certificate V E where
  toTreeNameRecord := treeRecord b
  face := decodeFace M.num.rotation.picture.face (atDart M b (fun x i => portVal x i .forwardDistance))
  edges v := vertexVal (b v) .subtreeEdges
  faces v := vertexVal (b v) .subtreeFaces
  patch v := (vertexVal (b v) .removalRound,vertexVal (b v) .patchName)

def TypesAgree : Prop :=
  ∀ v, (b v).1 = (M.typeAt v).root ∧ (b v).2.1 = RootedMap.paddedDirection (M.typeAt v)

/-- Decoding valid star records leaves only the bounded-neighborhood patch
predicate to complete the certificate. -/
theorem unpack_checked (ht : TypesAgree M b)
    (hs : ∀ v, starTest (PortView.actual M.slots b 1 v)) :
    ∃ hn : M.NameChecks (treeRecord b),
      ∀ K ε, RecordsValid ⟨_,hn.name_injective⟩ (candidatesOn M.graph.tail M.graph.head K ε)
        Finset.univ N (unpack M b).patch → M.CertificateChecks N K ε (unpack M b) := by
  obtain ⟨hn,hp,hcap⟩ := (treeTest_iff M b (fun v => (ht v).1)).mp (fun v => (hs v).1)
  refine ⟨hn, fun K ε patch => ?_⟩
  obtain ⟨hf,-⟩ := (faceTest_iff M b (fun v => (ht v).2)).mp (fun v => (hs v).2.1)
  let := M.graph.namedPortOrder ⟨_,hn.name_injective⟩ M.slots
  have ho := selfKey_strictMono M b hn.name_injective
  have valid := decodeFace_valid _ _ _ _ ho hf
  have he (v : V) := tailCount_eq M b (fun w => (ht w).2) v
  have hm (v : V) := markedCount_eq M b (fun w => (ht w).2) ho.injective
    (f := (unpack M b).face) (fun p => (hf.hit _ _ _ _ p).symm) v
  have hE := (subtreeTest_iff M b hn.distances hp .subtreeEdges _).mp (fun v => (hs v).2.2.1)
  have hF := (subtreeTest_iff M b hn.distances hp .subtreeFaces _).mp (fun v => (hs v).2.2.2.1)
  have hr : (b M.root).1 = true := by rw [(ht _).1]; simp [RootedMap.typeAt]
  have heu := (hs M.root).2.2.2.2 hr
  refine ⟨hn,hcap,valid,?_,?_,?_,patch⟩
  · intro v
    simpa only [PortView.actual,he,unpack] using hE v
  · intro v
    simpa only [PortView.actual,hm,unpack] using hF v
  · change (vertexVal (b M.root) .subtreeSize : ℤ) - vertexVal (b M.root) .subtreeEdges +
      (if Fintype.card (M.graph.Port M.root) = 0 then 1 else vertexVal (b M.root) .subtreeFaces : ℕ) = 2
    change (vertexVal (b M.root) .subtreeSize : ℤ) - vertexVal (b M.root) .subtreeEdges +
      (if baseDegree (b M.root) = 0 then 1 else vertexVal (b M.root) .subtreeFaces : ℕ) = 2 at heu
    rwa [baseDegree_eq _ _ (ht _).2] at heu

/-- Packing after a successful decode reproduces every field, including the
three padded zeros at each vacant slot. -/
theorem encode_unpack_eq (hN : 1 ≤ N) (ht : TypesAgree M b)
    (hs : ∀ v, starTest (PortView.actual M.slots b 1 v))
    (h : M.CertificateChecks N K ε (unpack M b)) : M.encodeBase hN h = b := by
  obtain ⟨_,hp,_⟩ := (treeTest_iff M b (fun v => (ht v).1)).mp (fun v => (hs v).1)
  obtain ⟨hf,hvac⟩ := (faceTest_iff M b (fun v => (ht v).2)).mp (fun v => (hs v).2.1)
  funext v
  apply Prod.ext (ht v).1.symm
  apply Prod.ext (ht v).2.symm
  funext f
  apply Fin.ext
  cases f with
  | inl s =>
    cases s with
    | parentPort => exact (hp v).symm
    | _ => rfl
  | inr s =>
    rcases s with ⟨i,j⟩
    change M.portField (c := unpack M b) v i j = portVal (b v) i j
    by_cases hi : ∃ p, M.slots v p = i
    · obtain ⟨p,rfl⟩ := hi
      rcases p with ⟨d,rfl⟩
      have he := hf.hit _ _ _ _ d
      cases j with
      | minimumVertex =>
        simpa [RootedMap.portField, slotFace_port, dartCode, unpack, decodeFace,
          atDart, selfKey, faceKey, treeRecord] using congrArg (fun k : FaceKey => (ofLex k).1) he
      | minimumPort =>
        simp only [RootedMap.portField, slotFace_port]
        exact congrArg (fun k : FaceKey => (ofLex k).2) he
      | forwardDistance =>
        simp only [RootedMap.portField, slotFace_port, unpack, decodeFace]
        rfl
    · cases j <;> simp [RootedMap.portField, slotFace_none _ _ _ _ _ _ hi, hvac _ _ hi]

end PortGraph.MapLabels

end

end SpectralBooks
end LinearAlgebra
end OAI
