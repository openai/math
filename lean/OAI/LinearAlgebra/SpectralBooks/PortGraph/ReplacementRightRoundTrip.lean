import OAI.LinearAlgebra.SpectralBooks.PortGraph.ReplacementChosenPairing
import OAI.LinearAlgebra.SpectralBooks.PortGraph.ReplacementForwardMap
import OAI.LinearAlgebra.SpectralBooks.PortGraph.ReplacementAcceptedRep

/-! # The reverse-then-forward round trip on the smaller map

The ambient map is decoded at its actual vertex and edge names. Replacing the
recovered old representative uses its canonical labelled patches, its actual
cut wires, and its saved term indices. The resulting equivalence preserves
the root, every port number, and the full decoration.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open OAI.MatrixMultiplication

noncomputable section
open scoped Classical

namespace PortGraph.ReplacementTemplate

namespace DecodedChoices
open ReplacementChoices

variable {N K : ℕ} {ε : ℝ} {C : System N K ε} (Term : Checked N K ε → Type)
  {T : TermTag Term → ReplacementTemplate.{0,0,0}}
  [∀ j, Fintype (T j).Role] [∀ j, Fintype (T j).Wire] [∀ j, Fintype (T j).Stub]
  {V E I : Type} [Fintype V] [Fintype E] [DecidableEq V] {H : RootedMap V E}
  {z : V → RoleLabel T} {patchId : TermTag Term → I}
  {oldEdge : (Σ j, (T j).Stub) → (Σ j, (T j).Stub) → Prop}
  (num3 : Forward.PortOrder T) (degree : ∀ j v, Fintype.card (LocalPort (T j) v) ≤ 3)
  (hv : ∀ v, VertexTest T (actualSlots H) (Forward.slotOfOrders num3 degree) z v)
  (he : ∀ e, PairTest patchId oldEdge (readEnd hv e false) (readEnd hv e true))
  [Fintype (Copies (T := T) z)]
  (stub : ∀ j, (T j).Stub ≃ j.1.val.shape.Stub)
  (d : DecodedChoices C (fun c : Copies (T := T) z => c.1.1)
    (recordPairing hv he (fun a => a.1.val) stub))

private local instance (priority := high) : DecidableEq (C.Occ (d.decorated Term (fun c => c.1.2)).1) := Classical.decEq _

variable (root : StubPairing.Vertex (Forward.pieces (T := T) (C.choiceTag Term (savedChoice Term hv he stub d))))
  (reach : ((C.choicePairing Term (savedChoice Term hv he stub d) T stub)).occurrenceGraph.ConnectedFrom root.1) (mark : RoleLabel T → Prop)
  (markSrc : ∀ v, mark (z v) ↔ v = H.root) (markFwd : ∀ v, mark (Forward.label (C.choiceTag Term (savedChoice Term hv he stub d)) v) ↔ v = root)

/-- Reverse decoding and forward replacement on the canonical old
representative return a rooted map isomorphic to the actual smaller input. -/
def rightIso : H.Iso (Forward.asMap (C.choiceTag Term (savedChoice Term hv he stub d)) (C.choicePairing Term (savedChoice Term hv he stub d) T stub) num3 degree root reach) :=
  smallIso hv he (C.choiceTag Term (savedChoice Term hv he stub d)) (C.choicePairing Term (savedChoice Term hv he stub d) T stub) d.recovered.occ (savedTag Term hv he stub d)
    (savedExterior Term hv he stub d) (savedPaired Term hv he stub d) _
    rfl mark markSrc markFwd (Forward.asMap_portNumber (C.choiceTag Term (savedChoice Term hv he stub d)) (C.choicePairing Term (savedChoice Term hv he stub d) T stub) num3 degree root reach)

/-- The isomorphism preserves even the term index at each role. Distinct
indices giving equal tensors are still separately labelled summands. -/
theorem rightIso_label (v : V) :
    Forward.label (C.choiceTag Term (savedChoice Term hv he stub d)) ((rightIso Term num3 degree hv he stub d root reach mark markSrc markFwd).vertex v) = z v :=
  smallLabel hv he (C.choiceTag Term (savedChoice Term hv he stub d)) (C.choicePairing Term (savedChoice Term hv he stub d) T stub) d.recovered.occ (savedTag Term hv he stub d)
    (savedExterior Term hv he stub d) (savedPaired Term hv he stub d) v

end DecodedChoices

namespace LocalRules

open UniformDecorations
variable {J I : Type} {T : J → ReplacementTemplate.{0,0,0}} (R : LocalRules (I := I) T)
  {s h : ℕ} (code : RoleLabel T ↪ Bits h) {A : Type} [CommSemiring A]
  (value : (a : RoleLabel T) → (RolePort T a → Bits s) → A)
  {N : ℕ} {X Y : (R.acceptedFamily code value N).Rep}

/-- A rooted map isomorphism preserving each role gives equality of the
accepted decorated summands. -/
theorem class_eq_of_roles (f : X.1.map.Iso Y.1.map) (labels : ∀ v, Y.2.val (f.vertex v) = X.2.val v) :
    (R.acceptedFamily code value N).classOf X = (R.acceptedFamily code value N).classOf Y := by
  apply Quotient.sound
  refine ⟨f,Subtype.ext (funext fun v => ?_)⟩
  exact ((labels (f.vertex.symm v)).symm.trans (congrArg Y.2.val (f.vertex.apply_symm_apply v)))

/-- Normalize a returned role-labelled map to its integer presentation.
An isomorphism back to the initial representative also respects its
transported role decoration. -/
theorem acceptedRep_isIso {V E : Type} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (M : RootedMap V E) (cap : Fintype.card V ≤ N) (hs : M.Spherical)
    (z : V → RoleLabel T) (ok : R.Accepts M z) (q : (R.acceptedFamily code value N).Rep)
    (f : q.1.map.Iso M) (roles : ∀ v, z (f.vertex v) = q.2.val v) :
    (R.acceptedFamily code value N).IsIso (R.acceptedRep code value M cap hs z ok) q := by
  let g := M.toRepIso cap hs
  refine ⟨(f.trans g).symm,Subtype.ext ?_⟩
  funext v
  change (R.acceptedRep code value M cap hs z ok).2.val (g.vertex (f.vertex v)) = q.2.val v
  exact (R.acceptedRep_role code value M cap hs z ok (f.vertex v)).trans (roles v)

end LocalRules
end PortGraph.ReplacementTemplate

end

end SpectralBooks
end LinearAlgebra
end OAI
