import OAI.Hierarchy.DescentReindexedMass
import OAI.Hierarchy.DescentGroupStageData

namespace OAI
/-! # Physical relabeling of a grouped stage and its occupied coordinates -/
namespace Hierarchy.DescentSixParty.GroupStage
open DescentColonies PhysicalRename
open scoped Classical BigOperators
noncomputable section
variable {F P J V : Type} [Field F] [Fintype J] [DecidableEq J] [Fintype V] [DecidableEq V]
variable {d k : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits} {G : PoweredGadget F} {q ε : ℝ}

/-- Relabel the actual source of every charge, pin and coordinate. -/
def names (A : GroupStage W G q ε J V k) (s : Equiv.Perm W.graph.Site) (e : Equiv.Perm W.graph.Edge) :
    GroupStage (PhysicalRename.world W s e) G q ε J V k where
  Atoms := A.Atoms
  wire := A.wire
  hist := A.hist
  z := A.z
  cap := A.cap
  degree := A.degree
  pos := A.pos ∘ s.symm
  block := A.block ∘ s.symm
  near := A.near
  hub := A.hub
  records := A.records ∘ s.symm
  fieldBits := A.fieldBits
  degreeMin := A.degreeMin
  degreeBound := A.degreeBound
  symmetric := A.symmetric
  pricePos := A.pricePos
  wirePos := A.wirePos
  unitPos := A.unitPos
  capPos := A.capPos
  small v x := (PhysicalRename.blockMass W s e A.pos A.block _ _
    (PhysicalRename.siteUnits W s e (fun t=>A.hub (A.pos t).2) A.records A.wire 256 A.hist) v x).le.trans (A.small v x)
  saturated v hv x := (PhysicalRename.blockMass W s e A.pos A.block _ _
    (PhysicalRename.siteUnits W s e (fun t=>A.hub (A.pos t).2) A.records A.wire 256 A.hist) v x).trans (A.saturated v hv x)
  noHubAtoms u hu := A.noHubAtoms (s.symm u) hu
  peers i := by
    obtain ⟨i,rfl⟩ := e.surjective i
    change A.pos (s.symm (s (W.graph.dst (e.symm (e i))))) ∈ DescentHostDirectory.groupedNear A.near (A.pos (s.symm (s (W.graph.src (e.symm (e i)))))) ∧
      A.pos (s.symm (s (W.graph.src (e.symm (e i))))) ∈ DescentHostDirectory.groupedNear A.near (A.pos (s.symm (s (W.graph.dst (e.symm (e i))))))
    simpa only [Equiv.symm_apply_apply] using A.peers i
  same i := by
    obtain ⟨i,rfl⟩ := e.surjective i
    change A.block (s.symm (s (W.graph.src (e.symm (e i)))))=A.block (s.symm (s (W.graph.dst (e.symm (e i)))))
    simpa only [Equiv.symm_apply_apply] using A.same i
  incidence := by
    constructor
    · intro i hi
      obtain ⟨i,rfl⟩ := e.surjective i
      change A.hub (A.pos (s.symm (s (W.graph.src (e.symm (e i)))))).2=false ∧ A.hub (A.pos (s.symm (s (W.graph.dst (e.symm (e i)))))).2=false
      simpa only [Equiv.symm_apply_apply] using A.incidence.inside i ((core_mem W s e i).mp hi)
    · intro i hi
      obtain ⟨i,rfl⟩ := e.surjective i
      change A.hub (A.pos (s.symm (s (W.graph.src (e.symm (e i)))))).2≠A.hub (A.pos (s.symm (s (W.graph.dst (e.symm (e i)))))).2
      simpa only [Equiv.symm_apply_apply] using A.incidence.outside i (fun h=>hi ((core_mem W s e i).mpr h))
  widths i hi := by
    obtain ⟨i,rfl⟩ := e.surjective i
    exact (PhysicalRename.width W.graph s e i).trans (A.widths i ((core_mem W s e i).mp hi))
  retained := by
    have total : (∑v : (world W s e).graph.Site,((A.records (s.symm v)).length:ℝ))=
        ∑v : W.graph.Site,((A.records v).length:ℝ) :=
      Fintype.sum_equiv s.symm _ _ (fun _=>rfl)
    change (q * A.hist) * (∑v : (world W s e).graph.Site, ((A.records (s.symm v)).length:ℝ)) ≤ ε
    rw [total]
    exact A.retained
  roots := A.roots

theorem names_coordinates (A : GroupStage W G q ε J V k) (s : Equiv.Perm W.graph.Site) (e : Equiv.Perm W.graph.Edge)
    (h : Function.Injective (fun v=>(A.pos v,A.block v))) :
    Function.Injective (fun v=>((A.names s e).pos v,(A.names s e).block v)) := h.comp s.symm.injective

end
end Hierarchy.DescentSixParty.GroupStage

end OAI
