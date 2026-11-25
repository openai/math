import OAI.Hierarchy.DescentOrdinaryWordTariff
import OAI.Hierarchy.DescentOrdinaryFinalTariff

namespace OAI
/-! # Fully charged final seven-field normalization -/
namespace Hierarchy.DescentOrdinaryFinal.Chart
open DescentPacking.PackedMatch.Local
open DescentSIMDLookup DescentPackedZip DescentStaticWordColumn DescentPackedFlowBatch ProtocolRAM
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
noncomputable section
variable (B : DescentOrdinaryFinal.Chart)

theorem word_volume (s : B.Sources) (floor w h u ratio R : ℕ) (pos : 0<u) (wide : 2*u≤h) (bus : w≤ratio*h)
    (joinRoom : (B.scalarWidth*B.inputs+B.scalarWidth)*B.layout.lanes≤h/2)
    (rows : B.rows≤R*Stage.DateBill.words B.layout.hosts B.layout.groups h u) :
    Stage.DateBill.bitTariff (B.program s floor w) (B.ticks s floor)≤
      (2*ratio*(B.tickUnits R+7*B.textUnits))*Stage.DateBill.volumeBits B.layout.hosts B.layout.groups h u :=by
  let U:=Stage.DateBill.words B.layout.hosts B.layout.groups h u
  have dyadic : 2^(h/2)≤U:=by dsimp [U,Stage.DateBill.words];omega
  have nz : 1≤U :=(Nat.two_pow_pos _).trans_le dyadic
  have up (n : ℕ) : n≤n*U:=by simpa only [Nat.mul_one] using Nat.mul_le_mul_left n nz
  have cg : B.scalarWidth*B.layout.lanes≤h/2:=(Nat.mul_le_mul_right _ (Nat.le_add_left ..)).trans joinRoom
  have c : B.castWords≤8*U:=by
    change 4*(2*2^(B.scalarWidth*B.layout.lanes))≤8*U
    have d:=(Nat.pow_le_pow_right (by decide : 0<2) cg).trans dyadic
    omega
  have b : B.tableWords≤((B.inputs+B.outputs)*2)*U:=by
    unfold tableWords;rw [Nat.mul_assoc (B.inputs+B.outputs) 2 U]
    exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ ((Nat.pow_le_pow_right (by decide) joinRoom).trans dyadic))
  obtain ⟨clocked,printed⟩:=B.tariff s floor w
  have ct : B.cpu≤B.tickUnits R*U:=calc
    _ ≤ (4*U+10*(8*U))+(4*U+10*(((B.inputs+B.outputs)*2)*U))+
      (4*U+B.passes*(4*U+(R*U)*(2*B.work+4))) :=by
      unfold cpu;gcongr <;> first | exact up _
    _ = _:=by unfold tickUnits;ring
  have cn : B.textCost≤B.textUnits*U:=calc
    _ ≤ 15*(8*U+1*U)+15*(((B.inputs+B.outputs)*2)*U+1*U)+(15*U+B.passes*((11+4*B.work)*U)) :=by
      unfold textCost;gcongr <;> first | exact up _
    _ = _:=by unfold textUnits;ring
  exact Stage.DateBill.from_words _ _ _ _ _ _ ratio (B.tickUnits R) B.textUnits pos wide bus
    (clocked.trans ct) (printed.trans cn)

end
end Hierarchy.DescentOrdinaryFinal.Chart

end OAI
