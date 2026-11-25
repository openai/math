import OAI.Hierarchy.DescentOperandReindex
import OAI.Hierarchy.DescentRetainedSevenRead
import OAI.Hierarchy.DescentResetOperandSetupChart

namespace OAI
namespace Hierarchy.DescentResetOperandSetup.Chart
open DescentSIMDLookup DescentResetRetainedSetup DescentPackedZip
open scoped Classical Fin.CommRing
noncomputable section
variable (C : DescentResetOperandSetup.Chart)
variable (hostEq : C.placement.oldHosts=C.retained.hosts) (groupEq : C.placement.groups*C.placement.blocks=C.retained.grouped)
    (which : C.seven.control.Targets) (packet : C.seven.Packets) (strips : C.retained.Strips)

def assignedDigits (z : Fin (C.retained.outputs*C.placement.shapes)) :
    Fin C.placement.oldHosts → Fin (C.placement.groups*C.placement.blocks) → Cell C.retained.bits :=
  let p : Fin C.retained.outputs × Fin C.placement.shapes := finProdFinEquiv.symm z
  reindexed (a:=C.retained.bits) hostEq groupEq (C.seven.decoded which packet strips p.1 p.2)

end
end Hierarchy.DescentResetOperandSetup.Chart

end OAI
