import OAI.Hierarchy.DescentOrdinaryWordTariff
import OAI.Hierarchy.DescentOrdinaryOverlapReserve
import OAI.Hierarchy.DescentPackedChunkWork
import OAI.Hierarchy.DescentStageVenueTariff

namespace OAI
/-! # Bus-word cost of the public signed, paid and actor retile instructions -/
namespace Hierarchy.DescentVenueSlabs
open DescentSIMDLookup ProtocolRAM DescentPacking.PackedMatch.Local.Stage.DateBill
variable (s : Shape)
local notation "H" => s.hosts
local notation "G" => s.groups
local notation "p" => s.pages
local notation "A" => s.sourceLanes
local notation "B" => s.targetLanes
local notation "old" => H*chunks G A
local notation "next" => H*chunks G B
local notation "dir" => (Overlap.pieces G A B+1)*(A+1)*2^(s.bits*A)

theorem tariff_split : tariff s≤4096*(p+1)*(1+old+next)+2048*dir := by
  unfold tariff Overlap.rows
  ring_nf
  omega

theorem word_bill_rows (pages : Fin p→Bank) (base w h a b ratio : ℕ)
    (live₀ : 0<A) (live₁ : 0<B) (oldBound : A≤h) (newBound : B≤h)
    (oldRows : old*h≤H*h+H*G*a) (newRows : next*h≤H*h+H*G*b) (bits : s.bits*A≤h/2) (bus : w≤ratio*h) :
    bitTariff (program s pages base w) (ticks s pages base) ≤
      4096*ratio*(p+1)*(h+2*H*h+(H*G)*(a+b))+
        (2048*ratio)*(2*(h+1)^2*2^(h/2))*h := by
  have table:=Overlap.half_pages h G A B s.bits oldBound newBound bits
  have price:=(price s pages base w live₀ live₁).trans (tariff_split s)
  calc
    _ ≤ (4096*(p+1)*(1+old+next)+2048*dir)*(ratio*h) := Nat.mul_le_mul price bus
    _ = 4096*ratio*(p+1)*(h+old*h+next*h)+(2048*ratio)*dir*h := by ring
    _ ≤ 4096*ratio*(p+1)*(h+(H*h+H*G*a)+(H*h+H*G*b))+
        (2048*ratio)*(2*(h+1)^2*2^(h/2))*h := by gcongr
    _ = _ :=by ring

theorem word_bill_dense (pages : Fin p→Bank) (base w h a b ratio : ℕ)
    (live₀ : 0<A) (live₁ : 0<B) (oldBound : A≤h) (newBound : B≤h)
    (oldFill : h≤A*a) (newFill : h≤B*b) (bits : s.bits*A≤h/2) (bus : w≤ratio*h) :
    bitTariff (program s pages base w) (ticks s pages base) ≤
      4096*ratio*(p+1)*(h+2*H*h+(H*G)*(a+b))+
        (2048*ratio)*(2*(h+1)^2*2^(h/2))*h := by
  exact word_bill_rows s pages base w h a b ratio live₀ live₁ oldBound newBound
    (DescentDatedSeedStartup.chunk_work H G A h a oldFill) (DescentDatedSeedStartup.chunk_work H G B h b newFill) bits bus

theorem word_bill (pages : Fin p→Bank) (base w h a b ratio : ℕ)
    (pos₀ : 0<a) (wide₀ : 2*a≤h) (pos₁ : 0<b) (wide₁ : 2*b≤h)
    (oldLanes : A=lanes h a) (newLanes : B=lanes h b) (bits : s.bits*A≤h/2) (bus : w≤ratio*h) :
    bitTariff (program s pages base w) (ticks s pages base) ≤
      4096*ratio*(p+1)*(h+2*H*h+4*(H*G)*(a+b))+
        (2048*ratio)*(2*(h+1)^2*2^(h/2))*h := by
  have live₀ : 0<A:=oldLanes.symm ▸ (occupancy h a pos₀ wide₀).1
  have live₁ : 0<B:=newLanes.symm ▸ (occupancy h b pos₁ wide₁).1
  have oldRows : old*h≤H*h+4*H*G*a:=oldLanes.symm ▸ volume H G h a pos₀ wide₀
  have newRows : next*h≤H*h+4*H*G*b:=newLanes.symm ▸ volume H G h b pos₁ wide₁
  have oldBound : A≤h:=oldLanes.symm ▸ (Nat.div_le_self ..)
  have newBound : B≤h:=newLanes.symm ▸ (Nat.div_le_self ..)
  have table:=Overlap.half_pages h G A B s.bits oldBound newBound bits
  have price:=(price s pages base w live₀ live₁).trans (tariff_split s)
  calc
    _ ≤ (4096*(p+1)*(1+old+next)+2048*dir)*(ratio*h) := Nat.mul_le_mul price bus
    _ = 4096*ratio*(p+1)*(h+old*h+next*h)+(2048*ratio)*dir*h := by ring
    _ ≤ 4096*ratio*(p+1)*(h+(H*h+4*H*G*a)+(H*h+4*H*G*b))+
        (2048*ratio)*(2*(h+1)^2*2^(h/2))*h := by gcongr
    _ = _ :=by ring

end Hierarchy.DescentVenueSlabs

end OAI
