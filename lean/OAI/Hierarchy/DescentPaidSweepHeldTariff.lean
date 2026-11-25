import OAI.Hierarchy.DescentPaidSweepHeldBill
import OAI.Hierarchy.DescentPaidSweepHeldRepacked
import OAI.Hierarchy.DescentPaidSweepPrice
import OAI.Hierarchy.DescentReachedCountRepackTariff

namespace OAI
/-! # Price of the held-field publication at the public clipped group pitch -/
namespace Hierarchy.DescentPaidResidentCount.Sweep.HeldRepacked
open DescentSIMDLookup DescentPackedZip DescentOrdinaryAtomFieldRAM DescentStaticWordColumn ProtocolRAM
open ThreeFlat.RAM PhysicalProcedure
noncomputable section
variable (base H G old M k paths cap b n p : ℕ)
local notation "D₀" => paths*2^k

/-- Includes the ROM writes, real old-to-clipped repacking, the census gather, both
    bitmap scans and all printed labels, registers and static words. -/
theorem tariff (field : Bank) (P : DescentPackedColony.Ports paths) (operand : ℕ→Expr)
    (labels : Fin p→ Cell n) (w unit : ℕ) (cost : ∀j<2^k,(operand j).work≤unit)
    (incoming : 0<old) (clipped : 0<M) :
    ticks base H G old M k paths cap b n p field P operand labels w+
      7*names (program base H G old M k paths cap b n p field P operand labels w)≤
        bill base H G old M k paths cap b n p unit :=by
  let L:=RoleCounts.Repitch.count H G old M k paths b base
  let prefix_:=RoleCounts.Repitch.phase H G old M k paths b base w P operand
  have first:=RoleCounts.Repitch.price H G old M k paths b base w unit P operand cost incoming clipped
  have second:=Sweep.tariff L.roof D₀ cap b H G M labels (.lookup field .row) L.expr w
  change prefix_.ticks+7*names prefix_.program≤_ at first
  change _≤2*tableBill _+tableBill _+columnBill p _ 37+columnBill p _ 19 at second
  unfold ticks program bill
  rw [names_seq]
  dsimp only [prefix_,L] at first second
  omega

end
end Hierarchy.DescentPaidResidentCount.Sweep.HeldRepacked

end OAI
