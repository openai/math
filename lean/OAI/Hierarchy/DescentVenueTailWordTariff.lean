import OAI.Hierarchy.DescentVenueSlabWordTariff

namespace OAI
/-! # The compact peer directory and broadcast table at the end of the venue publisher -/
namespace Hierarchy.DescentSixParty.StageVenueTail
open DescentPackedColony DescentSIMDLookup ProtocolRAM DescentPacking.PackedMatch.Local.Stage.DateBill

theorem tariff_split (k H G M D : ℕ) :
    tariff k H G M D≤1024*(2^k+D+1)*(1+H+H*chunks G M)+115*2^k*2^M := by
  unfold tariff DescentScalarHaloPortROM.length
  ring_nf
  omega

theorem word_bill_rows (pins : Sources) (base k H G M h unit D w ratio : ℕ)
    (after : M≤h/2) (rows : H*chunks G M*h≤H*h+H*G*unit) (bus : w≤ratio*h) :
    bitTariff (program pins base k H G M D w) (ticks pins base k H G M D) ≤
      1024*ratio*(2^k+D+1)*(h+2*H*h+H*G*unit)+(115*ratio*2^k)*(2^(h/2)*h) := by
  have power : 2^M≤2^(h/2):=Nat.pow_le_pow_right (by decide) after
  have invoice:=(price pins base k H G M D w).trans (tariff_split k H G M D)
  calc
    _ ≤ (1024*(2^k+D+1)*(1+H+H*chunks G M)+115*2^k*2^M)*(ratio*h) := Nat.mul_le_mul invoice bus
    _ = 1024*ratio*(2^k+D+1)*(h+H*h+H*chunks G M*h)+(115*ratio*2^k*2^M)*h := by ring
    _ ≤ 1024*ratio*(2^k+D+1)*(h+H*h+(H*h+H*G*unit))+(115*ratio*2^k*2^(h/2))*h := by gcongr
    _ = _ := by ring

theorem word_bill_dense (pins : Sources) (base k H G M h unit D w ratio : ℕ)
    (after : M≤h/2) (full : h≤M*unit) (bus : w≤ratio*h) :
    bitTariff (program pins base k H G M D w) (ticks pins base k H G M D) ≤
      1024*ratio*(2^k+D+1)*(h+2*H*h+H*G*unit)+(115*ratio*2^k)*(2^(h/2)*h) := by
  exact word_bill_rows pins base k H G M h unit D w ratio after (DescentDatedSeedStartup.chunk_work H G M h unit full) bus

theorem word_bill (pins : Sources) (base k H G h unit D w ratio : ℕ) (positive : 0<unit)
    (wide : 2*unit≤h) (bus : w≤ratio*h) :
    bitTariff (program pins base k H G (lanes h unit) D w) (ticks pins base k H G (lanes h unit) D) ≤
      1024*ratio*(2^k+D+1)*(h+2*H*h+4*H*G*unit)+(115*ratio*2^k)*(2^(h/2)*h) := by
  let M:=lanes h unit
  have after : M≤h/2:=Nat.div_le_div_left (by omega : 2≤2*unit) (by decide)
  have power : 2^M≤2^(h/2):=Nat.pow_le_pow_right (by decide) after
  have rows : H*chunks G M*h≤H*h+4*H*G*unit:=volume H G h unit positive wide
  have invoice:=(price pins base k H G M D w).trans (tariff_split k H G M D)
  calc
    _ ≤ (1024*(2^k+D+1)*(1+H+H*chunks G M)+115*2^k*2^M)*(ratio*h) := Nat.mul_le_mul invoice bus
    _ = 1024*ratio*(2^k+D+1)*(h+H*h+H*chunks G M*h)+(115*ratio*2^k*2^M)*h := by ring
    _ ≤ 1024*ratio*(2^k+D+1)*(h+H*h+(H*h+4*H*G*unit))+(115*ratio*2^k*2^(h/2))*h := by gcongr
    _ = _ := by ring

end Hierarchy.DescentSixParty.StageVenueTail

end OAI
