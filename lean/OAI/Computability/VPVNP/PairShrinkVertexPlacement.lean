import OAI.Computability.VPVNP.PairShrinkVertexLinks
import OAI.Computability.VPVNP.PairVertexSiteSegments

/-!
# The shrinking role's labels and register frame in the terminal vertex image
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.ShrinkVertexImage

open BurstRAM BurstRAM.PrivateRAM VertexImage Compression

variable {K : Type} [_root_.Field K] {S : BlockSchedule K} (B : S.Templates)
    {t : ℕ} (ord : B.Entry → Fin t)
    (geometry rootFields leaf refresh : Segment) {p r w : ℕ}

/-- The vertex instruction segments for geometry, root fields, leaf processing, the scheduled
shrinking program, and refresh. -/
noncomputable abbrev vertexParts := segments geometry rootFields leaf (shrinkSegment B ord) refresh

variable (A : VertexImage.Placement (vertexParts B ord geometry rootFields leaf refresh) p r)
    (M : Machine w p r 11)

theorem vertex_rows (h : VertexImage.Contains A M) (i : Fin (shrinkSegment B ord).count) :
    M.code (A.stage .shrink i) = ((shrinkSegment B ord).row (A.stage .shrink) A.dfs A.saved
      (A.localRegs .shrink) (A.dfsPC 3) i).resize w :=
  stage_linked A M h .shrink i

/-- The role can use its entire allocated register range while preserving the DFS bank. -/
theorem vertex_dfs_apart (j : Fin 9) : A.dfs j ∉ Set.range (A.localRegs .shrink) := by
  rintro ⟨i, h⟩
  exact (A.reg.injective.ne (by simp) : A.localRegs .shrink i ≠ A.dfs j) h

theorem vertex_saved_apart (j : Saved) : A.saved j ∉ Set.range (A.localRegs .shrink) := by
  rintro ⟨i, h⟩
  exact (A.reg.injective.ne (by simp) : A.localRegs .shrink i ≠ A.saved j) h

/-- Any subroutine bank placed inside the shrinking segment enjoys the same separation. -/
theorem vertex_subbank_apart {n : ℕ} (bank : Fin n ↪ Fin (shrinkSegment B ord).privateRegs)
    (j : Fin 9) : A.dfs j ∉ Set.range (bank.trans (A.localRegs .shrink)) :=
  fun ⟨i, h⟩ => vertex_dfs_apart B ord geometry rootFields leaf refresh A j ⟨bank i, h⟩

end PairSimulation.ShrinkVertexImage

end VPVNP
end Computability
end OAI
