import OAI.Hierarchy.DescentOrdinaryPaletteLayout

namespace OAI
/-! The block output of a durable role palette follows its prior, birth, spread and selection tables. -/
namespace Hierarchy.DescentOrdinaryPrimitiveCheckpoint.Layout
open ProtocolRAM DescentSIMDLookup DescentHaloWalkRAM
theorem bank_lower (L : Layout) (base : ℕ) (x : Fin L.blocks) : base≤(L.bank base x).base:=by
  simp only [bank,DescentOrdinaryRoleRetile.Layout.bank,durableStart,joinStart,spreadStart,bookStart,portStart,originStart,birthStart,
    DescentOrdinaryRoleRetile.Layout.roof,DescentOrdinaryRoleRetile.Layout.output,
    DescentSIMDLookup.Overlap.dest,DescentSIMDLookup.Overlap.dictBase,Shape.roof,Shape.output,
    DescentOrdinaryOriginReshape.Layout.finish,DescentOrdinaryOriginReshape.Layout.out,
    DescentScalarBookReshape.output,DescentOrdinaryOriginReshape.Layout.transpose,
    DescentOrdinaryOriginReshape.Layout.raw,ProtocolRAM.Bank.size,
    DescentOrdinaryRefsROM.Chart.endAddress,DescentOrdinaryRefsROM.Chart.tableBase,
    DescentOrdinaryRefsROM.Chart.digitSize,DescentOrdinaryRefsROM.Chart.digitBits,
    DescentOrdinaryRefsROM.Chart.tableSize,DescentOrdinaryRefsROM.Chart.count,
    DescentOrdinaryRefsROM.Chart.width,DescentOrdinaryRefsROM.Chart.keyBits,
    DescentOrdinaryRefsROM.Chart.actors,DescentOrdinaryRefsROM.Chart.nodes,DescentOrdinaryRefsROM.Chart.donors,
    DescentScalarHaloPortROM.stop,references,Nat.zero_add,Nat.add_assoc]
  exact Nat.le_add_right ..
end Hierarchy.DescentOrdinaryPrimitiveCheckpoint.Layout

end OAI
