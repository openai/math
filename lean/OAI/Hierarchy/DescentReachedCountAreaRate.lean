import OAI.Hierarchy.DescentReachedCountPageLayout
import OAI.Hierarchy.DescentPaidSweepLayout
import OAI.Hierarchy.DescentDatedAddressRate

namespace OAI
/-! The direct count dictionary fits the existing paid sweep's scalar address budget. -/
namespace Hierarchy.DescentOrdinaryAtomFieldRAM.RoleCounts
open DescentDatedAddressBook DescentSIMDLookup DescentPaidResidentCount Filter
noncomputable section

theorem romBits_le (base H G M k paths b cap : ℕ) (live : 0 < paths) :
    (layout base H G M k paths b).romBits ≤ 2*Sweep.sumBits (paths*2^k) cap b M := by
  let d:=paths*2^k
  have positive : 0<d := Nat.mul_pos live (Nat.two_pow_pos _)
  have bound : b≤b*d := by simpa using (Nat.mul_le_mul_left b positive)
  have narrow : b*d+b≤2*(1*DescentPackedActorMask.actors d cap+b*d) := by omega
  simpa only [layout,Layout.romBits,Layout.donors,Sweep.sumBits,d,Nat.mul_assoc] using
    Nat.mul_le_mul_right M narrow

variable {ι : ℕ→Type*}
theorem roof_rate (H G M k P b cap : ∀h,ι h→ℕ)
    (hosts : Bounded H) (groups : Bounded G) (lanes : Bounded M)
    (blocks : Bounded (fun h i=>2^(k h i))) (paths : Bounded P) (live : ∀h i,0<P h i)
    (bits : ∃C:ℕ,∀ᶠ h:ℕ in atTop,∀i,Sweep.sumBits (P h i*2^(k h i)) (cap h i) (b h i) (M h i)≤C*h) :
    Bounded (fun h i=>(layout 0 (H h i) (G h i) (M h i) (k h i) (P h i) (b h i)).roof) := by
  obtain ⟨C,limit⟩:=bits
  have rom:=Bounded.pow_of_linear (K:=2*C) (x:=fun h i=>(layout 0 (H h i) (G h i) (M h i) (k h i) (P h i) (b h i)).romBits) (by
    filter_upwards [limit] with h hx
    intro i
    simpa only [Nat.mul_assoc] using (romBits_le 0 (H h i) (G h i) (M h i) (k h i) (P h i) (b h i) (cap h i) (live h i)).trans
      (Nat.mul_le_mul_left 2 (hx i)))
  have chunk : Bounded (fun h i=>chunks (G h i) (M h i)) :=
    (groups.add lanes).of_le fun _ _=>(Nat.div_le_self ..).trans (Nat.sub_le ..)
  have sheets:=(hosts.mul chunk).padded
  have «public»:=(((paths.mul blocks).mul (Bounded.const 2)).mul rom)
  apply (((blocks.mul sheets).add «public»).add sheets).of_le
  intro h i
  simp only [layout,Layout.roof,Layout.outBase,Layout.romBase,Layout.tableWords,Layout.span,
    Layout.pageBits,Layout.rows,Layout.donors,Nat.zero_add,Nat.le_refl]

end
end Hierarchy.DescentOrdinaryAtomFieldRAM.RoleCounts

end OAI
