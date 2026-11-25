import OAI.LinearAlgebra.SpectralBooks.PortGraph.ReplacementSmallIso
import OAI.LinearAlgebra.SpectralBooks.PortGraph.ReplacementForwardMap

/-! # Transport of a forward tree replacement under change of occurrence names

Matching the record and list index at each occurrence identifies every
internal role, wire and boundary stub. An isomorphism of the original
cut wires then transports the resulting numbered, role-labelled maps.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open OAI.MatrixMultiplication

noncomputable section
open scoped Classical
namespace PortGraph.ReplacementTemplate.Forward

variable {O O' J : Type} {T : J → ReplacementTemplate.{0,0,0}}
  [∀ j, Fintype (T j).Role] [∀ j, Fintype (T j).Wire]
  {tag : O ↪ J} {tag' : O' ↪ J}
  {C : StubPairing (fun i => (T (tag i)).Stub)} {D : StubPairing (fun i => (T (tag' i)).Stub)}
  (occ : O ≃ O') (eqTag : ∀ i, tag i = tag' (occ i)) (outside : C.Wire ≃ D.Wire)

/-- All old cuts retain their orientation and their endpoint in each template. -/
abbrev KeepsEnds : Prop := ∀ e b,
  Equiv.sigmaCongr occ (fun i => atTag (fun j => (T j).Stub) (eqTag i)) (C.ends (e,b)) =
    D.ends (outside e,b)

variable (ends : KeepsEnds occ eqTag outside)

/-- Reindex the pieces of a forward replacement by equal catalogue tags. -/
def transportAssembly : StubPairing.AssemblyIso C D (pieces tag) (pieces tag') where
  occ := occ
  vertex i := atTag (fun j => (T j).Role) (eqTag i)
  wire i := atTag (fun j => (T j).Wire) (eqTag i)
  stub i := atTag (fun j => (T j).Stub) (eqTag i)
  outsideWire := outside
  incidence i e b := by
    have same {j k : J} (eq : j = k) (e : (T j).Wire) :
        atTag (fun j => (T j).Role) eq ((T j).graph.vertex e b) =
          (T k).graph.vertex (atTag (fun j => (T j).Wire) eq e) b := by subst k; rfl
    exact same (eqTag i) e
  attach i s := by
    have same {j k : J} (eq : j = k) (s : (T j).Stub) :
        atTag (fun j => (T j).Role) eq ((T j).attach s) =
          (T k).attach (atTag (fun j => (T j).Stub) eq s) := by subst k; rfl
    exact same (eqTag i) s
  ends := ends

private theorem pack_cast (F : J → Type) {j k : J} (h : j = k) (x : F j) :
    (⟨k,atTag F h x⟩ : Σ a, F a) = ⟨j,x⟩ := by subst k; rfl

local notation "A" => transportAssembly occ eqTag outside ends

/-- The entire role label is retained, including the selected list index. -/
theorem transport_label (v : StubPairing.Vertex (pieces (T := T) tag)) :
    label tag' ((A).vertices v) = label tag v :=
  pack_cast (fun j => (T j).Role) (eqTag v.1) v.2

/-- The dart at either side of a transported wire reads the same template end. -/
theorem transport_end (e : C.Edge (pieces (T := T) tag)) (b : Bool) :
    namedEnd tag' D ((A).edges e,b) = namedEnd tag C (e,b) := by
  rcases e with e | ⟨i,e⟩
  · change (Sum.inr (liftTag tag' (fun j => (T j).Stub) (D.ends (outside e,b))) : End T) =
      Sum.inr (liftTag tag (fun j => (T j).Stub) (C.ends (e,b)))
    rw [← ends e b]
    exact congrArg Sum.inr (pack_cast (fun j => (T j).Stub) (eqTag _) _)
  · exact congrArg (fun z => Sum.inl (z,b)) (pack_cast (fun j => (T j).Wire) (eqTag i) e)

variable [Fintype O] [Fintype O']
  [DecidableEq (StubPairing.Vertex (pieces (T := T) tag))]
  [DecidableEq (StubPairing.Vertex (pieces (T := T) tag'))]
  (M : RootedMap (StubPairing.Vertex (pieces (T := T) tag)) (C.Edge (pieces tag)))
  (H : RootedMap (StubPairing.Vertex (pieces (T := T) tag')) (D.Edge (pieces tag')))
  (src : M.graph = graph tag C) (dst : H.graph = graph tag' D)
  (marked : RoleLabel T → Prop)
  (root : ∀ v, marked (label tag v) ↔ v = M.root)
  (root' : ∀ v, marked (label tag' v) ↔ v = H.root)
  (slot : Numbering T)
  (ports : ∀ e b, M.portNumber e b = (endNumber slot (namedEnd tag C (e,b))).val)
  (ports' : ∀ e b, H.portNumber e b = (endNumber slot (namedEnd tag' D (e,b))).val)

/-- The distinguished root and consecutive port numbers are preserved. -/
def transportIso : M.Iso H :=
  (A).rootedIso M H src dst
    ((root' _).mp ((transport_label occ eqTag outside ends M.root).symm ▸ (root _).mpr rfl))
    (fun e b => (ports e b).trans (by rw [ports',transport_end occ eqTag outside ends]))

end PortGraph.ReplacementTemplate.Forward

end

end SpectralBooks
end LinearAlgebra
end OAI
