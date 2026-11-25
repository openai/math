import OAI.LinearAlgebra.SpectralBooks.PortGraph.ReplacementRoundForward
import OAI.LinearAlgebra.SpectralBooks.PortGraph.RecordReplacementSpherical

/-! # Sphericity of the concrete forward map -/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open OAI.MatrixMultiplication

noncomputable section
open scoped Classical
namespace PortGraph.ShapeCatalogue

open ReplacementTemplate ReplacementChoices
variable {F : Type} [Field F] {N K w c : ℕ} {ε : ℝ}
    (C : ShapeCatalogue F K w c) (S : System N K ε) (M : MapRep N)
    (t : (S.family C.Index).Label M)

local notation "tag" => C.forwardTag S M t
local notation "pair" => C.forwardPairing S M t

section
private local instance (priority := high) : DecidableEq (S.Occ M) := Classical.decEq _

private theorem replacement_genus :
    ((S.pairing M).assembleNumbering (fun i => (C.selected (tag i)).piece)
      (fun i => (C.selected (tag i)).numbering)).rotation.picture.GenusZero := by
  let P := S.partition M
  let U := fun i : S.Occ M => C.selected (tag i)
  have hs := ((P.oldIso M.map (S.label M) (S.name M)).spherical_iff).mpr M.spherical
  exact PatchRecord.replacement_spherical (S.record M) (fun i => (S.record_valid M i).connected)
    (S.pairing M) U (P.root M.map (S.label M) (S.name M)) (P.connected M.map (S.label M) (S.name M)) hs

private theorem rotations_eq :
    Forward.assemblyRotation tag pair C.portOrder =
      ((S.pairing M).assembleNumbering (fun i => (C.selected (tag i)).piece)
        (fun i => (C.selected (tag i)).numbering)).rotation := by
  rfl

private theorem forward_assembly_genus : (Forward.assemblyRotation tag pair C.portOrder).picture.GenusZero := by
  rw [rotations_eq]
  exact replacement_genus C S M t

end

set_option maxHeartbeats 1000000 in
/-- Every actual choice of terms gives a spherical smaller map. -/
theorem forward_spherical : (C.forwardMap S M t).Spherical := by
  have hg := forward_assembly_genus C S M t
  have ha : (Forward.assemblyRotation tag pair C.portOrder).picture.GenusZero := by
    simpa only [HyperbolicObstruction.PictureSwitch.PictureMap.GenusZero,
      HyperbolicObstruction.PictureSwitch.PictureMap.euler,
      HyperbolicObstruction.PictureSwitch.cycles_eq_card_classes, ← Nat.card_eq_fintype_card] using hg
  exact Forward.asMap_spherical tag pair C.portOrder C.degree (C.forwardRoot S M t)
    (C.forward_reach S M t) ha

end PortGraph.ShapeCatalogue

end

end SpectralBooks
end LinearAlgebra
end OAI
