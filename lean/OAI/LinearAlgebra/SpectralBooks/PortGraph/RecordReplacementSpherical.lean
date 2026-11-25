import OAI.LinearAlgebra.SpectralBooks.PortGraph.OldAssemblyForest
import OAI.LinearAlgebra.SpectralBooks.PortGraph.RecordReplacementDisk
import OAI.LinearAlgebra.SpectralBooks.PortGraph.PlanarAssemblySpherical

/-! # The spherical map obtained from a choice of actual replacement terms

The common interpatch wires retain both of their ends. Direct patches and
pruned triangulation trees use their prescribed local numbering. The chosen role
in the occurrence of the old root witnesses connectivity of the replacement.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open OAI.MatrixMultiplication

noncomputable section
open scoped Classical

namespace PortGraph.PatchRecord

open Equiv
open StubPairing

variable {J F A : Type} [Field F] [Fintype J] {K w : ℕ} (R : J → PatchRecord K A)
    (conn : ∀ i, (R i).shape.InternallyConnected) (C : StubPairing fun i => (R i).shape.Stub)
    (U : ∀ i, (R i).shape.RecordTerm (conn i) w F)
    (r : vertices R) (hr : (graph R C).ConnectedFrom r)

omit [Fintype J] in
private theorem piece_inhabited (i : J) : Nonempty ((pieces R i).Vertex) :=
  ⟨⟨0,(R i).shape.positive⟩⟩

/-- Every choice of the direct or pruned term in each old record produces
a spherical map with its actual assembled numbering. -/
theorem replacement_spherical (hs : (asMap R C r hr).Spherical) :
    (C.assembleNumbering (fun i => (U i).piece)
      (fun i => (U i).numbering)).rotation.picture.GenusZero := by
  let P := pieces R
  let Q := fun i => (U i).piece
  let num := C.assembleNumbering Q (fun i => (U i).numbering)
  let s : Vertex Q := ⟨r.1,(U r.1).rootRole⟩
  have hocc := C.occurrence_connected (pieces R) hr (piece_inhabited R)
  have hconn : (C.assemble Q).ConnectedFrom s :=
    C.assemble_connected Q ((U r.1).rootRole) hocc (fun i => ⟨(U i).rootRole, (U i).tree.connected⟩)
  let B := PatchShape.RecordTerm.pieceDiskData U
  have ht (x : C.Edge Q × Bool) : C.dartEquiv Q (num.turn x) =
      Equiv.sigmaCongrRight B.turn (C.dartEquiv Q x) := by
    have hlocal : pieceTurn Q (fun i => (U i).numbering) = B.turn :=
      funext (PatchShape.RecordTerm.pieceTurn_eq U)
    exact (C.dartEquiv_assemble_turn Q (fun i => (U i).numbering) x).trans
      (congrArg (fun t : ∀ i, Equiv.Perm (PieceDart Q i) => Equiv.sigmaCongrRight t (C.dartEquiv Q x)) hlocal)
  apply C.spherical_replacement P Q (asMap R C r hr).num num (diskData R conn) B
    (diskData_asMap_turn R conn C r hr) ht r s hr hconn (piece_inhabited R) rfl _ hs
  intro live i
  exact (diskData_stubTurn R conn live i).trans
    (PatchShape.RecordTerm.pieceDiskData_stubTurn U live i).symm

end PortGraph.PatchRecord

end

end SpectralBooks
end LinearAlgebra
end OAI
