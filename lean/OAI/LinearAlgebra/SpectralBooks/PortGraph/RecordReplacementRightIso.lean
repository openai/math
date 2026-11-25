import OAI.LinearAlgebra.SpectralBooks.PortGraph.ReplacementRightRoundTrip
import OAI.LinearAlgebra.SpectralBooks.PortGraph.RecordReplacementReverse
import OAI.LinearAlgebra.SpectralBooks.PortGraph.ReplacementRoundForward

/-! # The concrete catalogue's right inverse on role-decorated map classes -/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open OAI.MatrixMultiplication

noncomputable section
open scoped Classical
namespace PortGraph.ShapeCatalogue
open ReplacementChoices ReplacementTemplate UniformDecorations

variable {F : Type} [Field F] {N K w c : ℕ} {ε : ℝ} (C : ShapeCatalogue F K w c)
  (S : System N K ε) {V E : Type} [Fintype V] [Fintype E] [DecidableEq V]
  (H : RootedMap V E) (z : V → RoleLabel (C.templates (N:=N) (ε:=ε))) (ok : (C.rules N ε).Accepts H z)

private abbrev saved := (C.decode S H z ok).decorated C.Index (fun d => d.1.2)


set_option maxHeartbeats 1600000 in
/-- Every vertex of the smaller input corresponds to its original catalogue
tag and numbered role after decoding and forward replacement. -/
def rightMapIso : H.Iso (C.forwardMap S (saved C S H z ok).1 (saved C S H z ok).2) :=
  let d := C.decode S H z ok
  let stub := fun j : C.Tag N ε => Equiv.refl j.1.val.shape.Stub
  let vv := ok.2.2.choose
  let ee := ok.2.2.choose_spec
  let t := saved C S H z ok
  smallIso (T := C.templates) (H := H) (slot := (C.rules N ε).slot) (z := z) vv ee (C.forwardTag S t.1 t.2) (C.forwardPairing S t.1 t.2) d.recovered.occ
    (DecodedChoices.savedTag C.Index vv ee stub d) (DecodedChoices.savedExterior C.Index vv ee stub d)
    (DecodedChoices.savedPaired C.Index vv ee stub d) (C.forwardMap S t.1 t.2) rfl (C.rules N ε).marked ok.2.1
    (C.forward_marked S t.1 t.2) (C.forward_portNumber S t.1 t.2)

set_option maxHeartbeats 1600000 in
theorem rightMapIso_label (v : V) :
    C.forwardLabel S (saved C S H z ok).1 (saved C S H z ok).2 ((C.rightMapIso S H z ok).vertex v) = z v :=
  let d := C.decode S H z ok
  let stub := fun j : C.Tag N ε => Equiv.refl j.1.val.shape.Stub
  let vv := ok.2.2.choose
  let ee := ok.2.2.choose_spec
  let t := saved C S H z ok
  smallLabel (T := C.templates) (H := H) (slot := (C.rules N ε).slot) (z := z) vv ee (C.forwardTag S t.1 t.2) (C.forwardPairing S t.1 t.2) d.recovered.occ
    (DecodedChoices.savedTag C.Index vv ee stub d) (DecodedChoices.savedExterior C.Index vv ee stub d)
    (DecodedChoices.savedPaired C.Index vv ee stub d) v

end PortGraph.ShapeCatalogue

end

end SpectralBooks
end LinearAlgebra
end OAI
