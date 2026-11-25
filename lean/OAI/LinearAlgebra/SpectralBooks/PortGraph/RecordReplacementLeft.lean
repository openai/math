import OAI.LinearAlgebra.SpectralBooks.PortGraph.RecordReplacementReverse
import OAI.LinearAlgebra.SpectralBooks.PortGraph.ReplacementLeftRoundTrip
import OAI.LinearAlgebra.SpectralBooks.PortGraph.ReplacementRoundMap

/-! # The old-map composite for the uniform replacement catalogue -/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open OAI.MatrixMultiplication

noncomputable section
open scoped Classical
namespace PortGraph.ShapeCatalogue

open ReplacementChoices ReplacementTemplate UniformDecorations

variable {F : Type} [Field F] {N K w c : ℕ} {ε : ℝ} (C : ShapeCatalogue F K w c)
  (S : System N K ε) (M : MapRep N) (choice : (S.family C.Index).Label M)

set_option maxHeartbeats 1800000 in
/-- Before relabelling, re-expanding the chosen trees restores the original
map with precisely its original term indices. -/
theorem decode_forward :
    let m := C.forwardMap S M choice
    let z := C.forwardLabel S M choice
    let d := C.decode S m z (C.forward_accepts S M choice)
    (S.family C.Index).IsIso (d.decorated C.Index (fun i => i.1.2)) ⟨M,choice⟩ := by
  let m := C.forwardMap S M choice
  let ok := C.forward_accepts S M choice
  have numbers : actualSlots m = Forward.numbering (C.forwardTag S M choice)
      (C.forwardPairing S M choice) (C.rules N ε).slot := by
    rw [C.rules_slot]
    exact Forward.actualSlots_asMap ..
  exact S.forward_left_roundTrip_of_slots C.Index choice C.templates (fun _ => Equiv.refl _)
    (C.rules N ε).slot (C.forward_orient S M choice) (C.rules N ε).oldEdge (C.forward_oldEdge S M choice)
    (actualSlots m) numbers ok.2.2.choose ok.2.2.choose_spec (C.decode S m _ ok)

set_option maxHeartbeats 1800000 in
/-- The composite of the concrete forward and reverse maps is the identity
on the old decorated classes. -/
theorem reverse_forward {a h : ℕ} (ha : 0 < a) (hε : ε = 1 / (2 * (a : ℝ)))
    (code : RoleLabel (C.templates (N:=N) (ε:=ε)) ↪ Bits h) (q : (S.family C.Index).Rep) :
    (S.family C.Index).IsIso (C.reverse S code (C.forwardRep S ha hε code q)) q := by
  exact DecoratedMaps.Family.IsIso.trans _ (C.reverse_acceptedRep S code
    (C.forward_cap S q.1 q.2 ha hε) (C.forward_spherical S q.1 q.2) (C.forward_accepts S q.1 q.2))
    (C.decode_forward S q.1 q.2)

end PortGraph.ShapeCatalogue

end

end SpectralBooks
end LinearAlgebra
end OAI
