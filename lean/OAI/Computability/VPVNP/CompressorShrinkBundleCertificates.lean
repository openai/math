import OAI.Computability.VPVNP.CompressorShrinkBundleExecution
import OAI.Computability.VPVNP.CompressorShrinkBundleAccess
import OAI.Computability.VPVNP.CompressorShrinkPreparationAccess
import OAI.Computability.VPVNP.CompressorSourceWalkJoin

/-! # Native shrinking source packets with their cursor and data certificates -/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.ShrinkBundlePlan.Scheduled

open BurstRAM Compression PhaseRecipe ShrinkWidthFootprints

variable {w a g : ℕ} {X : State a (packingLaneBits a g)} {T : IncidenceDirectory w} {start : ℕ}
variable {m : Memory w} (r : ShrinkInput.Run X T start m)

/-- The scheduled bundle stage has the stated source run and cursor limit, and its external
reads and writes stay within the respective shrinking regions. -/
def Certified (X : State a (packingLaneBits a g)) (T : IncidenceDirectory w) (start lo : ℕ)
    (shape : DescriptorSpace.Shape) (step : ℕ) (origin : Expr) (j : Stage) (mem : Memory w)
    (rs : List (Report w)) : Prop :=
  Source X T start shape step origin j mem rs ∧ Checked (j.limit X start)
    (fun x ↦ lo ≤ x ∧ x < ShrinkInput.stop X start) (fun x ↦ start ≤ x ∧ x < ShrinkInput.stop X start) rs

/-- The sources and their actual footprints have the same report boundaries
throughout the eleven workers, including both prefix scans. -/
theorem certified_sources (shape : DescriptorSpace.Shape) (step : ℕ) (origin : Expr) {abs : List (Report w)}
    (last : AbsoluteRun r abs) (lo : ℕ) (low : ∀ c, lo ≤ (T.column c).val) (room : ShrinkInput.stop X start < 2^w) :
    SourceWalk (Certified X T start lo shape step origin) order r.greedy.post (preparationReports X T start r ++ abs) := by
  have fit := (ShrinkInput.range_bounds X start).2.2.2.trans_lt room
  have tail : SourceWalk (Source X T start shape step origin) [.absolute] r.post abs := .singleton last.native
  rw [← preparation_post X T start r] at tail
  have native := (preparation_sources shape step origin X T start r fit).append tail
  let cert (j : Stage) (_ : Memory w) (rs : List (Report w)) :=
    Checked (j.limit X start) (fun x ↦ lo ≤ x ∧ x < ShrinkInput.stop X start)
      (fun x ↦ start ≤ x ∧ x < ShrinkInput.stop X start) rs
  have hc : SourceWalk cert order r.greedy.post (preparationReports X T start r ++ abs) := by
    obtain ⟨sites,clear,cl,ap,ga,rk⟩ := r.preparation_footprints lo low room
    obtain ⟨sw,tp,cp,ab,ac⟩ := width_footprints r last lo (low 5) room
    simp only [preparationReports,order,preparationOrder,List.append_assoc,List.cons_append,List.nil_append]
    exact .next sites (.next clear (.next cl (.next ap (.next ga (.next rk (.next sw (.next tp
      (.next cp (.next ab (.singleton ac))))))))))
  apply SourceWalk.and_of_counts (Stage.limit X start) _ _ native hc
  · exact fun _ _ _ hs ↦ source_calls shape step origin X T start hs
  · exact fun _ _ _ hs ↦ hs.1.calls

end CompressorRecords.ShrinkBundlePlan.Scheduled

end VPVNP
end Computability
end OAI
