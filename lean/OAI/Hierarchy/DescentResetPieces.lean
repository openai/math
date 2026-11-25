import OAI.Hierarchy.DescentWholeGrain

namespace OAI
/-! # One-bit specialization of the measured router input -/

namespace Hierarchy.DescentSixParty.MarkedWorld
open Computability.BorderVNP.Crossing
open scoped BigOperators Classical
noncomputable section
variable {F : Type*} [Field F] {D : ℕ} {P : Type*} {bits : P→ℕ}
variable (A : MarkedWorld F D P bits)

abbrev fineNetwork := A.grains A.graph.width 1
def fine := A.granular A.graph.width 1 (fun e=>by simp)
theorem fine_value (x : Ports bits) : A.fine.value x=A.value x :=
  A.granular_value A.graph.width 1 (fun e=>by simp) x
omit [Field F] in
theorem fine_mark (e : A.fine.graph.Edge) : e∈A.fine.core ↔ e.1∈A.core := by
  let p : Σe : A.graph.Edge,Fin (A.graph.width e) := e
  exact show p ∈ Finset.univ.filter (fun r : Σe : A.graph.Edge,Fin (A.graph.width e)=>r.1∈A.core) ↔ p.1∈A.core from
      ⟨fun z=>(Finset.mem_filter.mp z).2,fun z=>Finset.mem_filter.mpr ⟨Finset.mem_univ _,z⟩⟩
omit [Field F] in
theorem fine_core : A.fine.liveWidth=A.liveWidth :=
  A.granular_core A.graph.width 1 (fun e=>by simp)
omit [Field F] in
theorem fine_tether : A.fine.tetherWidth=A.tetherWidth :=
  A.granular_tether A.graph.width 1 (fun e=>by simp)
omit [Field F] in
theorem fine_width (e : A.fine.graph.Edge) : A.fine.graph.width e=1 := rfl

end
end Hierarchy.DescentSixParty.MarkedWorld

end OAI
