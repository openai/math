import OAI.LinearAlgebra.SpectralBooks.PortGraph.ReplacementEncoder
import OAI.LinearAlgebra.SpectralBooks.PortGraph.ReplacementReconstruction
import OAI.LinearAlgebra.SpectralBooks.PortGraph.ReplacementAssemblyIso
import OAI.LinearAlgebra.SpectralBooks.PortGraph.ReplacementUniform

/-! # Recovering the smaller decorated map up to rooted isomorphism

Changing the names of the occurrences preserves every tag, including the
chosen list index. The isomorphism uses the actual internal and exterior
wire bijections of the tree decoder.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open OAI.MatrixMultiplication

noncomputable section
open scoped Classical
namespace PortGraph.ReplacementTemplate

variable {J I O : Type} {T : J → ReplacementTemplate.{0,0,0}}
  [∀ j, Fintype (T j).Role] [∀ j, Fintype (T j).Wire]
  {V E : Type} [Fintype V] [Fintype E] [DecidableEq V] {H : RootedMap V E}
  {slot : Numbering T} {z : V → RoleLabel T} {patchId : J → I}
  {oldEdge : (Σ j, (T j).Stub) → (Σ j, (T j).Stub) → Prop}
  (hv : ∀ v, VertexTest T (actualSlots H) slot z v)
  (he : ∀ e, PairTest patchId oldEdge (readEnd hv e false) (readEnd hv e true))

/-- Transport an object in any template family along equality of its tag. -/
def atTag (F : J → Type) {j k : J} (eq : j = k) : F j ≃ F k := Equiv.cast (congrArg F eq)

private theorem pack_atTag (F : J → Type) {j k : J} (eq : j = k) (v : F j) :
    (⟨k,atTag F eq v⟩ : Σ j,F j) = ⟨j,v⟩ := by subst k; rfl

variable (tag : O ↪ J) (C : StubPairing (fun i => (T (tag i)).Stub))
  (occ : Copies (T := T) z ≃ O) (tagEq : ∀ c, c.1 = tag (occ c))
  (extWire : OutsideEdge hv ≃ C.Wire)

/-- Preservation of the paired cuts retains the endpoint occurrence and its
old stub after changing the role and wire coordinates by tag equality. -/
abbrev Paired : Prop := ∀ (e : OutsideEdge hv) b,
  Equiv.sigmaCongr occ (fun c => atTag (fun j => (T j).Stub) (tagEq c)) (endsEquiv hv he (e,b)) =
    C.ends (extWire e,b)

variable (paired : Paired hv he tag C occ tagEq extWire)

/-- Re-index all the decoded pieces by any occurrence coordinates bearing
the same template tags and paired exterior ends. -/
def assemblyChange :
    StubPairing.AssemblyIso (decodedPairing hv he) C (treePiece (T := T) (z := z)) (Forward.pieces tag) where
  occ := occ
  vertex c := atTag (fun j => (T j).Role) (tagEq c)
  wire c := atTag (fun j => (T j).Wire) (tagEq c)
  stub c := atTag (fun j => (T j).Stub) (tagEq c)
  outsideWire := extWire
  incidence c e b := by
    have aux {j k : J} (h : j = k) (e : (T j).Wire) (b : Bool) :
        atTag (fun j => (T j).Role) h ((T j).graph.vertex e b) =
          (T k).graph.vertex (atTag (fun j => (T j).Wire) h e) b := by subst k; rfl
    exact aux (tagEq c) e b
  attach c s := by
    have aux {j k : J} (h : j = k) (s : (T j).Stub) :
        atTag (fun j => (T j).Role) h ((T j).attach s) =
          (T k).attach (atTag (fun j => (T j).Stub) h s) := by subst k; rfl
    exact aux (tagEq c) s
  ends := paired

local notation "changeMap" => assemblyChange hv he tag C occ tagEq extWire paired

/-- The actual smaller vertex goes to its role in the matching occurrence. -/
def smallVertices : V ≃ StubPairing.Vertex (Forward.pieces (T := T) tag) :=
  (vertexEquiv hv he).trans (changeMap).vertices

/-- All internal wires keep their wire role, and all exterior wires map by
the prescribed bijection of the two sets of cut edges. -/
def smallEdges : E ≃ C.Edge (Forward.pieces (T := T) tag) := (decodedEdge hv he).trans (changeMap).edges

local notation "sv" => smallVertices hv he tag C occ tagEq extWire paired
local notation "se" => smallEdges hv he tag C occ tagEq extWire paired

theorem smallLabel (v : V) : Forward.label tag (sv v) = z v :=
  (pack_atTag (fun i => (T i).Role) (tagEq (vertexEquiv hv he v).1) _).trans (vertexEquiv_role hv he v)

theorem smallIncidence (e : E) (b : Bool) :
    sv (H.graph.vertex e b) = (Forward.graph tag C).vertex (se e) b :=
  (congrArg (changeMap).vertices (decoded_incidence hv he e b)).trans ((changeMap).map_incidence _ _)

theorem smallEnd (e : E) (b : Bool) : Forward.namedEnd tag C (se e,b) = readEnd hv e b := by
  obtain ⟨(q|q),rfl⟩ := (edgePartition hv).surjective e
  · have hw : decodedEdge hv he (edgePartition hv (.inl q)) = Sum.inl q :=
      congrArg ((Equiv.refl _).sumCongr (wireEquiv hv he)) ((edgePartition hv).symm_apply_apply (.inl q))
    change Forward.namedEnd tag C ((changeMap).edges (decodedEdge hv he _),b) = readEnd hv q.val b
    rw [hw, readEnd_stub hv he q b]
    apply congrArg Sum.inr
    change Forward.liftTag tag (fun j => (T j).Stub) (C.ends (extWire q,b)) = _
    rw [← paired q b]
    exact pack_atTag (fun i => (T i).Stub) (tagEq (endsEquiv hv he (q,b)).1) _
  · have hw : decodedEdge hv he (edgePartition hv (.inr q)) = Sum.inr (wireEquiv hv he q) :=
      congrArg ((Equiv.refl _).sumCongr (wireEquiv hv he)) ((edgePartition hv).symm_apply_apply (.inr q))
    change Forward.namedEnd tag C ((changeMap).edges (decodedEdge hv he _),b) = readEnd hv q.val b
    rw [hw, readEnd_wire hv he q b]
    exact congrArg (fun x => Sum.inl (x,b)) (pack_atTag (fun i => (T i).Wire) (tagEq (wireEquiv hv he q).1) _)

variable [Fintype O] [DecidableEq (StubPairing.Vertex (Forward.pieces (T := T) tag))]
  (H' : RootedMap (StubPairing.Vertex (Forward.pieces (T := T) tag)) (C.Edge (Forward.pieces tag)))
  (src : H'.graph = Forward.graph tag C) (marked : RoleLabel T → Prop)
  (root : ∀ v, marked (z v) ↔ v = H.root)
  (root' : ∀ v, marked (Forward.label tag v) ↔ v = H'.root)
  (ports : ∀ e b, H'.portNumber e b = (endNumber slot (Forward.namedEnd tag C (e,b))).val)

/-- The forward replacement constructed on the recovered occurrences is
isomorphic to the smaller input, preserving the record, list position, and
role at each original vertex. -/
def smallIso : H.Iso H' where
  vertex := sv
  edge := se
  incidence e b := by rw [src]; exact smallIncidence hv he tag C occ tagEq extWire paired e b
  root := (root' _).mp ((smallLabel hv he tag C occ tagEq extWire paired H.root).symm ▸ (root _).mpr rfl)
  number e b := by
    rw [ports,smallEnd hv he tag C occ tagEq extWire paired]
    exact (congrArg Fin.val (number_readEnd hv e b)).symm

end PortGraph.ReplacementTemplate

end

end SpectralBooks
end LinearAlgebra
end OAI
