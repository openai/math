import OAI.ThreeFlat.RAM.HistoryStageArmResources
import OAI.ThreeFlat.RAM.HistoryStageSelectedResources

namespace OAI
/-! # Static resources of the actual selected history-node program -/
namespace ThreeFlat.RAM.HistoryStageBody.Physical
open Computability.VPVNP.BurstRAM PhysicalProcedure PhysicalPinsExpr DescriptorExpr
open scoped Classical BigOperators Fin.CommRing
noncomputable section

def armResources (f : Family) :=
  let base := layout 0 ⟨0,0,0,0,0,0⟩ f
  kernelResources base f.childBound+rootResources base f.childBound

theorem arm_resources (f : Family) (W u : ℕ) (a : Archive) (g : Family) (eq : g.schema=f.schema) :
    resources (HistoryStageBody.procedure (layout u a g) g.childBound W)≤armResources f := by
  let base := layout 0 ⟨0,0,0,0,0,0⟩ f
  have project {α : Type} (field : Family→α) : field g.schema=field f.schema := congrArg field eq
  have same : Same (layout u a g) base :=
    ⟨project Family.mode,project Family.demands,project Family.supplies,
      project Family.parties,project Family.motifs⟩
  have c : g.childBound=f.childBound := project Family.childBound
  rw [c,HistoryStageBody.procedure,resources_seq]
  exact Nat.add_le_add (kernel_resources _ _ same _) (root_resources _ _ same _)


def selectedResources (fs : List Family) :=
  49+leafResources+(fs.map (fun f=>6+4*(enabled 0 f).work+armResources f)).sum

theorem selected_resources (fs : List Family) (W u : ℕ) (a : Archive) (shape : TraceBucketAtom.Layout)
    (pub : Fin TraceEndpointROM.params→Word W) (gs : List Family) (same : gs.map Family.schema=fs.map Family.schema) :
    resources (selected W u a shape pub gs)≤ selectedResources fs :=
  selected_resources_of_arms fs armResources (fun f _ => arm_resources f) W u a shape pub gs same



private theorem familiesFrom_schema {F : Type} [Field F] [Fintype F] (gs : List (Grid F)) (x y : ℕ) :
    (familiesFrom x gs).map Family.schema=(familiesFrom y gs).map Family.schema := by
  induction gs generalizing x y with
  | nil => rfl
  | cons g gs ih =>
    exact congrArg₂ List.cons (show (g.family x).schema = (g.family y).schema from rfl)
      (ih (x + g.size) (y + g.size))

/-- A single finite code, register and public-word budget for all sizes and placements of the
archive installed for this particular shrink/refresh block. -/
theorem block_selected_resources {F : Type} [Field F] [Fintype F] (B : Diagonal.PhysicalStage.Block F) :
    ∃ cut : ℕ, ∀ (start height K W u : ℕ) (shape : TraceBucketAtom.Layout)
      (pub : Fin TraceEndpointROM.params→Word W),
      let p := selected W u (archive B start height K) shape pub (families B start height)
      p.labels+p.registers+p.slots≤cut := by
  refine ⟨selectedResources (families B 0 0), ?_⟩
  intro start height K W u shape pub
  have same : (families B start height).map Family.schema = (families B 0 0).map Family.schema := by
    unfold families
    exact familiesFrom_schema (grids B) _ _
  exact selected_resources (families B 0 0) W u (archive B start height K) shape pub
    (families B start height) same


end
end ThreeFlat.RAM.HistoryStageBody.Physical

end OAI
