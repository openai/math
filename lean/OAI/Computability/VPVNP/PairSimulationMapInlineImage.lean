import OAI.Computability.VPVNP.PairSimulationMapInline
import OAI.Computability.VPVNP.PairSimulationInlineSegment

/-!
# The concrete grouped map call inside the native vertex image

A grid point and a party determine the selector and matrix table. This segment installs
its width-two code in the vertex image's literal format. The image can reuse the same
table at every visit by entering it with the current private descriptor pointer.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.MapInline

open MotifSelector MotifGrid MotifBlocks MotifConversion
open BurstRAM.PrivateRAM InlinePublic MapConstants CompressorRecords
open scoped Fin.CommRing

variable {J D E K : Type} [Fintype J] [DecidableEq J] [Fintype D] [Fintype E] [Field K]
  {src dst : D → J} {G : Supply J E} {p₀ : D → ℚ} {q₀ : E → ℚ} {H H' : ℝ}
  {B : FixedBlock K src dst G (realWidths p₀) (realWidths q₀) H H'}
  {z : B.grid.demands} {j : J} {r k t w P R : ℕ}
  (L : MapCallTable.Layout B z j r k) (ord : (parameterData B).Entry → Fin t)

/-- All labels and registers are fixed for this map template. -/
noncomputable def imageSegment : VertexImage.Segment := segment L.template (rawBank L.core ord)

variable (loc : Fin (imageSegment L ord).count → Fin P) (reg : Fin (r + 2) ↪ Fin R)
    (done : Fin P)

/-- Places the lowered call table and its registers in the host image. Successful exits
transfer to the supplied continuation, while a failing exit uses the segment's reject row. -/
noncomputable abbrev imagePlacement := linkedPlacement L.template (rawBank L.core ord) loc reg done

private theorem init_continues {v W R₁ p' k' : ℕ} (a : RowRecipe.Assign v 5)
    (bank : Fin v ↪ Fin R₁) (ptr : Fin R₁) (next : Fin p') :
    continues (MapInitCompiler.instruction (w := W) (k := k') bank ptr a next) = true := by
  obtain ⟨dst, rhs⟩ := a
  cases rhs <;> rfl

/-- The initial source opcode is the first operand assignment or the directory initializer. -/
theorem entry_continues : continues (L.template.code L.template.entry) = true := by
  change continues (L.text L.locations (L.locations.symm (L.initPC L.locations 0))) = true
  unfold MapCallTable.Layout.initPC
  split
  · simp only [Equiv.symm_apply_apply, MapCallTable.Layout.text]
    exact init_continues _ _ _ _
  · simp [MapCallTable.Layout.dirPC, MapCallTable.Layout.text, MapDirectoryInit.text, continues]

theorem imageEntry :
    (imagePlacement L ord loc reg done).entry L.template.entry =
      loc (imageSegment L ord).entry :=
  segment_entry _ _ _ _ _ (entry_continues L)

theorem imageDone : (imagePlacement L ord loc reg done).entry (callProgram L).done = done :=
  success_entry _ _ _ _ _ (exit_codes L).2

variable (dfs : Fin 9 ↪ Fin R) (saved : VertexImage.Saved ↪ Fin R)
    (M : Machine w P R 11)
    (installed : ∀ a, M.code (loc a) =
      ((imageSegment L ord).row loc dfs saved reg done a).resize w)

include installed in
/-- The actual installed rows discharge the code premise of the native map call. -/
theorem imageLinked : Linked L ord (imagePlacement L ord loc reg done) M :=
  contains_linkedRows _ _ _ _ _ M (segment_rows _ _ _ dfs saved reg done M installed)

include installed in
/-- A failed map reaches the machine's genuine rejecting instruction. -/
theorem imageReject : M.code ((imagePlacement L ord loc reg done).entry (callProgram L).bad) =
    .reject :=
  rejecting_entry _ _ _ _ _ M (segment_rows _ _ _ dfs saved reg done M installed) (exit_codes L).1

end PairSimulation.MapInline

end VPVNP
end Computability
end OAI
