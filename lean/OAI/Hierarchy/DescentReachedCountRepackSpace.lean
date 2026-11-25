import OAI.Hierarchy.DescentReachedCountRepackBill
import OAI.Hierarchy.DescentReachedCountAreaRate
import OAI.Hierarchy.DescentVenueShapeRate

namespace OAI
/-! # Translation and address width of the genuine count repacking banks -/
namespace Hierarchy.DescentOrdinaryAtomFieldRAM.RoleCounts.Repitch
open DescentSIMDLookup DescentDatedAddressBook DescentPaidResidentCount Filter
noncomputable section
set_option quotPrecheck false
variable (H G old M k paths b : ℕ)
local notation "S" => shape H G old M k b
local notation "L" base => count H G old M k paths b base

theorem translate (base : ℕ) :
    (L base).roof=base+(L 0).roof := by
  unfold count
  rw [Layout.translate,Layout.translate (after H G old M k b 0)]
  unfold after
  rw [DescentVenueSlabs.translates (S) base,Nat.add_assoc]

variable {ι : ℕ→Type*}

theorem roof_rate (H G old M k P b cap : ∀h,ι h→ℕ)
    (hosts : Bounded H) (groups : Bounded G) (earlier : Bounded old) (lanes : Bounded M)
    (blocks : Bounded (fun h i=>2^(k h i))) (paths : Bounded P) (live : ∀h i,0<P h i)
    (key : ∃C:ℕ,∀ᶠ h:ℕ in atTop,∀i,b h i*old h i≤C*h)
    (bits : ∃C:ℕ,∀ᶠ h:ℕ in atTop,∀i,Sweep.sumBits (P h i*2^(k h i)) (cap h i) (b h i) (M h i)≤C*h) :
    Bounded (fun h i=>(count (H h i) (G h i) (old h i) (M h i) (k h i) (P h i) (b h i) 0).roof) := by
  have front:=DescentVenueSlabs.extent_rate (fun h i=>shape (H h i) (G h i) (old h i) (M h i) (k h i) (b h i))
    blocks hosts groups earlier lanes key
  have back:=RoleCounts.roof_rate H G M k P b cap hosts groups lanes blocks paths live bits
  apply (front.add back).of_le
  intro h i
  exact (Layout.translate _ _ _ _ _ _ _).le

end
end Hierarchy.DescentOrdinaryAtomFieldRAM.RoleCounts.Repitch

end OAI
