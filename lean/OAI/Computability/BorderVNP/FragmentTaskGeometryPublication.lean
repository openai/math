import OAI.Computability.BorderVNP.FragmentTaskDirectoryRoom

/-! # Address and marker bounds from the signed geometry output reservation -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.FragmentRows

open Packing Packing.RoutingOutputs GeometryAdvice

/-- The signed geometry emits its complete descriptor inverse after the
37 scalar controls and before the cube header. Its published marker and report
width bounds therefore suffice for the source geometry of the actual task scan. -/
theorem task_geometry_of_publication_at (a : SignedTaskArena.Layout) (mem : ℕ → ℕ) (scope : Option ℕ)
    {frame fresh profile gates outputs bits w J A descriptorColumn : ℕ}
    (low : frame+112 ≤ fresh) (cellCap : a.cube.cells ≤ a.p.report.cells)
    (total : a.cube.cables*3+(RoutingOutputs.count a.cube.cables a.cube.cells J A+
      ((a.cube.cells+(J+a.cube.cells))+(37+(descriptorColumn+2*a.p.padded)))) ≤ outputs)
    (cube : a.cube.header.header=Allocation.stop fresh profile gates outputs bits w) :
    let origin := Allocation.dest fresh profile gates outputs bits
    let tbl := bases origin a.cube.cables a.cube.cells J
    let ctl := controlsBase origin a.cube.cables a.cube.cells J A
    a.p.sorted=ctl+37+descriptorColumn →
    a.cube.cells ≤ a.p.stops ∧ a.p.stops+a.cube.cells ≤ a.p.padded →
    (∀ c < a.cube.cells, mem (a.p.sorted+a.p.padded+c)<a.p.padded ∧
      mem (a.p.sorted+a.p.padded+(a.p.stops+c))<a.p.padded) →
    (∀ c < a.cube.cells, scope.elim True (fun team => mem (a.cube.hostDirectory+2*c)=team) →
      mem (tbl.ends+2*a.cube.cables+c)+mem (a.before.tailWidths+c) ≤ a.cube.cellStride) →
    a.SparsePlacement frame ctl ∧ TaskSourceGeometry a frame tbl.ends ctl mem scope := by
  intro origin tbl ctl sorted markers ranks widths
  have start : frame+112 ≤ origin := by dsimp [origin,Allocation.dest,Allocation.temp]; omega
  have stop : origin+outputs ≤ a.cube.header.header := by
    rw [cube]; dsimp only [Allocation.stop,Allocation.packed,Allocation.dense,origin]; omega
  have address : frame+112 ≤ tbl.ends ∧ tbl.ends+2*a.cube.cables+a.cube.cells ≤ ctl ∧
      ctl+37+descriptorColumn+2*a.p.padded ≤ origin+outputs := by
    dsimp only [tbl,ctl,controlsBase,bases,RoutingOutputs.count] at total ⊢
    omega
  have headerBank := a.open_table_order.1
  obtain ⟨hdr,_,_,_,_,_,power,powers,group,team,owners,pairs,_⟩ := a.cube.group_order
  constructor
  · exact ⟨by omega,by omega,.inl (by omega),by omega,by omega,cellCap⟩
  · refine ⟨by omega,address.1,address.2.1,by omega,.inl (by omega),markers,ranks,?_⟩
    cases scope with
    | none => exact fun c hc => widths c hc trivial
    | some t => exact Or.inr ⟨fun c _ => by omega,fun c hc owned => widths c hc owned⟩

/-- An all-cell extent bound gives the unrestricted version of the same
physical marker and report geometry. -/
theorem task_geometry_of_publication (a : SignedTaskArena.Layout) (mem : ℕ → ℕ)
    {frame fresh profile gates outputs bits w J A descriptorColumn : ℕ}
    (low : frame+112 ≤ fresh) (cellCap : a.cube.cells ≤ a.p.report.cells)
    (total : a.cube.cables*3+(RoutingOutputs.count a.cube.cables a.cube.cells J A+
      ((a.cube.cells+(J+a.cube.cells))+(37+(descriptorColumn+2*a.p.padded)))) ≤ outputs)
    (cube : a.cube.header.header=Allocation.stop fresh profile gates outputs bits w) :
    let origin := Allocation.dest fresh profile gates outputs bits
    let tbl := bases origin a.cube.cables a.cube.cells J
    let ctl := controlsBase origin a.cube.cables a.cube.cells J A
    a.p.sorted=ctl+37+descriptorColumn →
    a.cube.cells ≤ a.p.stops ∧ a.p.stops+a.cube.cells ≤ a.p.padded →
    (∀ c < a.cube.cells, mem (a.p.sorted+a.p.padded+c)<a.p.padded ∧
      mem (a.p.sorted+a.p.padded+(a.p.stops+c))<a.p.padded) →
    (∀ c < a.cube.cells, mem (tbl.ends+2*a.cube.cables+c)+mem (a.before.tailWidths+c) ≤ a.cube.cellStride) →
    a.SparsePlacement frame ctl ∧ TaskSourceGeometry a frame tbl.ends ctl mem := by
  intro origin tbl ctl sorted markers ranks widths
  exact task_geometry_of_publication_at a mem none low cellCap total cube sorted markers ranks (fun c hc _ => widths c hc)

end RoutingISA.FragmentRows

end BorderVNP
end Computability
end OAI
