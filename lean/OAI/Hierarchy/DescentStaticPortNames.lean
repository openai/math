import OAI.Hierarchy.ProtocolRAMStaticPorts
import OAI.Hierarchy.DescentStaticWordColumn

namespace OAI
/-! # Physical instruction-table size for literal address scaling -/
namespace Hierarchy.DescentStaticWordColumn
open ProtocolRAM
open ThreeFlat.RAM PhysicalProcedure DescriptorExpr

theorem names_scale (w out n lanes : ℕ) (e : Expr) :
    names (ProtocolRAMStaticPorts.program w out n lanes e)≤11+4*(e.work+1+2*ProtocolRAMPortScale.bitWidth lanes) := by
  have bound:=ProtocolRAMPortScale.binds w (ProtocolRAMPortScale.bitWidth lanes) lanes
  simp only [names,ProtocolRAMStaticPorts.program,PhysicalInputPhases.writing,Term.labels_eq]
  simp only [ProtocolRAMStaticPorts.expression,Term.binds_letThen,Term.binds_rename,compile_binds]
  omega

end Hierarchy.DescentStaticWordColumn

end OAI
