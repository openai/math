import OAI.ThreeFlat.Diagonal.CompressorTemplateEmit
import OAI.ThreeFlat.Diagonal.CompressorTagSimulation

namespace OAI
/-! # The native ordered tag compiler is the verified candidate-offset scan -/
namespace ThreeFlat.Diagonal.CompressorPacking.Native.ShrinkStage.Template
open Computability.VPVNP.BurstRAM Computability.VPVNP.BurstRAM.PrivateRAM RAM.DescriptorExpr Placement
open scoped Fin.NatCast
variable {w : ℕ} (cell : Word w)

def tagColumns : TagColumns w 1 1 :=
  ⟨emit cell (f offsets),emit cell g.dst,emit cell g.src,emit cell g.forwardTag,emit cell g.backTag⟩

theorem emit_offset (d t : ℕ) : emit cell (offset d t)=offsetRow (tagColumns cell) d t := by
  unfold offset
  rw [emit_free]
  unfold offsetRow
  congr 1
  simp [Ordered.directions,List.flatMap_append,List.map_append,List.map_flatMap,List.flatMap_map,
    List.map_map,List.ofFn_eq_map,List.map_cons,Function.comp_def,
    tagColumns,stepTerms,tagTerms,tagDirection,xor,row,readRow,Demand.formulaOps,o]

end ThreeFlat.Diagonal.CompressorPacking.Native.ShrinkStage.Template

end OAI
