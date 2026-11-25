import OAI.Hierarchy.DescentOrdinaryOriginInvoice
import OAI.Hierarchy.DescentPackedChunkWork

namespace OAI
/-! # Bit cost of issuing all selected donor numbers at the bought physical pitch -/
namespace Hierarchy.DescentOrdinaryOriginMask.Return
open DescentSIMDLookup DescentPackedZip DescentOrdinaryAtomFieldRAM DescentOrdinaryAtomFieldRAM.ScalarOperand
open DescentHaloWalkRAM DescentPackedActorMask DescentStaticWordColumn DescentPacking.PackedMatch.Local
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
noncomputable section
variable (R : Return)

open DescentPackedColony
local notation "r" => R.blocks
local notation "M" => R.lanes

theorem scaled_bill (C : Fin R.lows→Refs R.degree R.depth R.oldNodes R.capacity)
    (base w ratio h packed : ℕ)
    (source : ∀i,(C i).want.work+(C i).addr.work+(C i).counts.work≤26)
    (fit : R.peak*(M*r)≤h/2) (density : h≤M*packed) (bus : w≤ratio*h) :
    (R.ticks C base+7*names (R.program C w base))*w≤
      ratio*(2600*(R.lows+1)*h+(160+300*r)*
        ((R.hosts*R.lows)*h+(R.hosts*R.lows)*R.groups*packed)+115*((4+r)*2^(h/2))*h) :=by
  have bill:=R.origin_table_bill C w base source fit
  have rows_eq : R.lows*R.grid.rows=R.grid.nextRows:=by
    change R.lows*(R.hosts*chunks R.groups M)=(R.hosts*R.lows)*chunks R.groups M
    ac_rfl
  rw [rows_eq] at bill
  have clipped : R.grid.nextRows*h≤(R.hosts*R.lows)*h+(R.hosts*R.lows)*R.groups*packed :=
    DescentDatedSeedStartup.chunk_work (R.hosts*R.lows) R.groups M h packed density
  calc
    _ ≤ (2600*(R.lows+1)+160*R.grid.nextRows+300*(r*R.grid.nextRows)+115*((4+r)*2^(h/2)))*(ratio*h) :=
      Nat.mul_le_mul bill bus
    _ = ratio*(2600*(R.lows+1)*h+(160+300*r)*(R.grid.nextRows*h)+115*((4+r)*2^(h/2))*h):=by ring
    _ ≤ _ :=Nat.mul_le_mul_left ratio (Nat.add_le_add_right
      (Nat.add_le_add_left (Nat.mul_le_mul_left (160+300*r) clipped) _) _)

end
end Hierarchy.DescentOrdinaryOriginMask.Return

end OAI
