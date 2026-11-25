import OAI.Hierarchy.DescentReindexedMass
import OAI.Hierarchy.DescentNetworkReindex
import OAI.Hierarchy.DescentMeasuredHistory

namespace OAI
/-! # Transport of the measured stage through physical old-graph numbering -/

namespace Hierarchy.DescentSixParty.PhysicalRename
open Computability.BorderVNP.Crossing DescentColonies
open scoped Classical BigOperators
noncomputable section
variable {F : Type} [Field F] {d : ℕ} {P : Type} {bits : P→ℕ}
variable (A : MarkedWorld F d P bits) (site : Equiv.Perm A.graph.Site) (edge : Equiv.Perm A.graph.Edge)

/-- All scalar budgets, source records, and marked incidence facts are inherited
from the same physical history after relabeling. -/
def stage {G : PoweredGadget F} {u ε : ℝ} (I : StageInput A G u ε) : StageInput (world A site edge) G u ε where
  V := I.V
  finite := I.finite
  decideV := I.decideV
  Atoms := I.Atoms
  k := I.k
  pos := I.pos ∘ site.symm
  block := I.block ∘ site.symm
  hub := I.hub ∘ site.symm
  records := I.records ∘ site.symm
  wire := I.wire
  hist := I.hist
  z := I.z
  cap := I.cap
  Δ := I.Δ
  near := I.near
  fieldBits := I.fieldBits
  degreeMin := I.degreeMin
  degree := I.degree
  wirePos := I.wirePos
  unitPos := I.unitPos
  capPos := I.capPos
  small v x := (blockMass A site edge I.pos I.block _ _
    (siteUnits A site edge I.hub I.records I.wire 256 I.hist) v x).le.trans (I.small v x)
  adjacent i hi := by
    obtain ⟨i,rfl⟩ := edge.surjective i
    change I.pos (site.symm (site (A.graph.dst (edge.symm (edge i))))) ∈
      I.near (I.pos (site.symm (site (A.graph.src (edge.symm (edge i))))))
    simpa only [Equiv.symm_apply_apply] using
      I.adjacent i ((core_mem A site edge i).mp hi)
  reverse i hi := by
    obtain ⟨i,rfl⟩ := edge.surjective i
    change I.pos (site.symm (site (A.graph.src (edge.symm (edge i))))) ∈
      I.near (I.pos (site.symm (site (A.graph.dst (edge.symm (edge i))))))
    simpa only [Equiv.symm_apply_apply] using
      I.reverse i ((core_mem A site edge i).mp hi)
  internal i hi := by
    obtain ⟨i,rfl⟩ := edge.surjective i
    change I.block (site.symm (site (A.graph.src (edge.symm (edge i))))) =
      I.block (site.symm (site (A.graph.dst (edge.symm (edge i)))))
    simpa only [Equiv.symm_apply_apply] using
      I.internal i ((core_mem A site edge i).mp hi)
  widths i hi := by
    obtain ⟨i,rfl⟩ := edge.surjective i
    exact (width A.graph site edge i).trans (I.widths i ((core_mem A site edge i).mp hi))
  inside i hi := by
    obtain ⟨i,rfl⟩ := edge.surjective i
    change I.hub (site.symm (site (A.graph.src (edge.symm (edge i))))) = false ∧
      I.hub (site.symm (site (A.graph.dst (edge.symm (edge i))))) = false
    simpa only [Equiv.symm_apply_apply] using
      I.inside i ((core_mem A site edge i).mp hi)
  outside i hi := by
    obtain ⟨i,rfl⟩ := edge.surjective i
    change I.hub (site.symm (site (A.graph.src (edge.symm (edge i))))) ≠
      I.hub (site.symm (site (A.graph.dst (edge.symm (edge i)))))
    simpa only [Equiv.symm_apply_apply] using
      I.outside i (fun h=>hi ((core_mem A site edge i).mpr h))
  q := I.q
  qpos := I.qpos
  unitPrice := I.unitPrice
  retained := by
    have sum : (∑v : (world A site edge).graph.Site,((I.records (site.symm v)).length:ℝ))=
        ∑v : A.graph.Site,((I.records v).length:ℝ) := Fintype.sum_equiv site.symm _ _ (fun _=>rfl)
    change I.q * (I.hist : ℝ) *
      (∑ v : (world A site edge).graph.Site, ((I.records (site.symm v)).length : ℝ)) ≤ ε
    rw [sum]
    exact I.retained
  roots := I.roots

@[simp] theorem stage_pos {G : PoweredGadget F} {u ε : ℝ} (I : StageInput A G u ε) (v : A.graph.Site) :
    (stage A site edge I).pos (site v)=I.pos v :=
  congrArg I.pos (site.symm_apply_apply v)

@[simp] theorem stage_block {G : PoweredGadget F} {u ε : ℝ} (I : StageInput A G u ε) (v : A.graph.Site) :
    (stage A site edge I).block (site v)=I.block v :=
  congrArg I.block (site.symm_apply_apply v)

end
end Hierarchy.DescentSixParty.PhysicalRename

end OAI
