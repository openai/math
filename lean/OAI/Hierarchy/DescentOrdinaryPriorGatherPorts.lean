import OAI.Hierarchy.DescentScalarHaloProgram

namespace OAI
/-! A later operand bank can reuse the sorted donor roster and its static address columns. -/
namespace Hierarchy.DescentScalarHaloProgram
open DescentHaloWalkRAM DescentPackedColony DescentSIMDLookup ProtocolRAM
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
noncomputable section

theorem later_bank (H G M D base top w : ℕ) (B : Bank)
    (separate : stop H G M D base≤top) (ceiling : top<2^w)
    (fit : B.Fits w top) (rows : H*chunks G M≤B.size) :
    Accessible (ports H G M D base) B H G M w top :=by
  let P:=breadth D
  let R:=sorted H G M D base
  have words : H*P≤R.size:=Nat.le_pow_clog (by decide) _
  have end_ : R.base+R.size≤top:=separate
  have placed : R.Fits w top:=
    ⟨Nat.two_pow_pos _,(Nat.le_add_left ..).trans_lt (end_.trans_lt ceiling),end_⟩
  have early : endsBase H G M D base≤top:=by
    unfold stop ranksBase at separate
    omega
  exact (DescentScalarHaloPortROM.geometry H G M P (statics H G M D base) top R B early ceiling
    placed words fit rows).1

end
end Hierarchy.DescentScalarHaloProgram

end OAI
