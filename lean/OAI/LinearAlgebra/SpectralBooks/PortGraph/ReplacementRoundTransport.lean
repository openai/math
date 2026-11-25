import OAI.LinearAlgebra.SpectralBooks.PortGraph.ReplacementForwardTransport
import OAI.LinearAlgebra.SpectralBooks.PortGraph.ReplacementChoicePairingIso
import OAI.LinearAlgebra.SpectralBooks.PortGraph.ReplacementRoundForward
import OAI.LinearAlgebra.SpectralBooks.PortGraph.ReplacementAcceptedRep

/-! # Isomorphism invariance of the actual chosen tree replacement -/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open OAI.MatrixMultiplication

noncomputable section
open scoped Classical
namespace PortGraph.ShapeCatalogue

open ReplacementTemplate ReplacementChoices UniformDecorations
variable {F : Type} [Field F] {N K w c : ℕ} {ε : ℝ}
  (C : ShapeCatalogue F K w c) (S : System N K ε) {M H : MapRep N}
  (t : (S.family C.Index).Label M) (u : (S.family C.Index).Label H)
  (f : M.map.Iso H.map) (move : (S.family C.Index).move f t = u)

include move
set_option maxHeartbeats 1600000

/-- Both the checked record and its list position agree at matched occurrences. -/
theorem forward_tag_iso (i : S.Occ M) :
    C.forwardTag S M t i = C.forwardTag S H u (S.occEquiv f i) := by
  subst u
  exact (S.family_move_sigma C.Index f t i).symm

/-- The old cut pairing transports through the equal record and list tags. -/
theorem forward_pairing_iso :
    Forward.KeepsEnds (T := C.templates) (C := C.forwardPairing S M t) (D := C.forwardPairing S H u)
      (S.occEquiv f) (C.forward_tag_iso S t u f move) (S.crossEdgeEquiv f) := by
  intro e b
  exact S.pairing_iso f e b

/-- Renaming an old map gives a rooted, numbered isomorphism of its two
actual replacements for any transported choice of list positions. -/
def forwardIso : (C.forwardMap S M t).Iso (C.forwardMap S H u) :=
  Forward.transportIso (T := C.templates) (tag := C.forwardTag S M t) (tag' := C.forwardTag S H u)
    (C := C.forwardPairing S M t) (D := C.forwardPairing S H u) (S.occEquiv f) (C.forward_tag_iso S t u f move) (S.crossEdgeEquiv f)
    (C.forward_pairing_iso S t u f move) (C.forwardMap S M t) (C.forwardMap S H u) rfl rfl (C.rules N ε).marked
    (C.forward_marked S M t) (C.forward_marked S H u) (C.rules N ε).slot
    (C.forward_portNumber S M t) (C.forward_portNumber S H u)

theorem forwardIso_role (v : StubPairing.Vertex (C.forwardPieces S M t)) :
    C.forwardLabel S H u ((C.forwardIso S t u f move).vertex v) = C.forwardLabel S M t v :=
  Forward.transport_label (S.occEquiv f) (C.forward_tag_iso S t u f move) (S.crossEdgeEquiv f)
    (C.forward_pairing_iso S t u f move) v

/-- Normalizing the two accepted labelled replacement maps to finite
vertex and edge names preserves their equality up to isomorphism. -/
theorem forward_accepted_iso {N' h : ℕ} (code : RoleLabel (C.templates (N:=N) (ε:=ε)) ↪ Bits h)
    (capM : Fintype.card (StubPairing.Vertex (C.forwardPieces S M t)) ≤ N')
    (capH : Fintype.card (StubPairing.Vertex (C.forwardPieces S H u)) ≤ N')
    (sphereM : (C.forwardMap S M t).Spherical) (sphereH : (C.forwardMap S H u).Spherical) :
    ((C.rules N ε).acceptedFamily code C.coefficient N').IsIso
      ((C.rules N ε).acceptedRep code C.coefficient _ capM sphereM _ (C.forward_accepts S M t))
      ((C.rules N ε).acceptedRep code C.coefficient _ capH sphereH _ (C.forward_accepts S H u)) :=
  (C.rules N ε).acceptedRep_iso code C.coefficient _ capM sphereM _ (C.forward_accepts S M t)
    _ capH sphereH _ (C.forward_accepts S H u) (C.forwardIso S t u f move) (C.forwardIso_role S t u f move)

end PortGraph.ShapeCatalogue

end

end SpectralBooks
end LinearAlgebra
end OAI
