import OAI.Hierarchy.DescentResetOriginalDonors
import OAI.Hierarchy.DescentResetStemProjectRate

namespace OAI
/-! # Address rate of the genuine original donor shelves -/
namespace Hierarchy.DescentResetOriginalDonors
open Filter DescentDatedAddressBook
variable {ι : ℕ→Type*}
namespace Panel
theorem rate (P : ∀h,ι h→Panel)
    (sites : Bounded (fun h i=>(P h i).sparseHosts)) (groups : Bounded (fun h i=>(P h i).groups))
    (blocks : Bounded (fun h i=>(P h i).blocks)) (lanes : Bounded (fun h i=>(P h i).lanes))
    (fields : Bounded (fun h i=>(P h i).fields))
    (cast : ∃K:ℕ,∀ᶠ h:ℕ in atTop,∀i,(P h i).oldBits*(P h i).lanes≤K*h)
    (target : ∃K:ℕ,∀ᶠ h:ℕ in atTop,∀i,(P h i).bits*((P h i).blocks+1)*(P h i).lanes≤K*h) :
    Bounded (fun h i=>(P h i).endAddress 0) :=by
  obtain ⟨C,hc⟩:=cast
  obtain ⟨K,hk⟩:=target
  have exp : Bounded (fun h i=>2^((P h i).oldBits*(P h i).lanes)):=Bounded.pow_of_linear hc
  have low (h) (i : ι h) : (P h i).bits≤(P h i).bits*((P h i).blocks+1):=Nat.le_mul_of_pos_right _ (Nat.succ_pos _)
  have project:=DescentResetStemProject.rates fields sites groups blocks lanes lanes
    ⟨K,hk.mono fun h bound i=>(Nat.mul_le_mul_right _ (low h i)).trans (bound i)⟩
    ⟨K,hk.mono fun h bound i=>(Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (Nat.le_succ _))).trans (bound i)⟩
  apply (((Bounded.const (ι:=ι) 2).mul exp).add project).of_le
  intro h i
  change DescentResetStemProject.endAddress _ _ _ _ _ _ _ _≤_
  rw [DescentResetStemProject.extent]
  simp only [Panel.cut, DescentContactWidthPage.endAddress, DescentContactWidthPage.words,
    Nat.zero_add, Nat.le_refl]

end Panel
namespace Layout
variable (L : ∀h,ι h→Layout)
structure ScalarRoom : Prop where
  sites : Bounded (fun h i=>(L h i).sparseHosts)
  groups : Bounded (fun h i=>(L h i).groups)
  blocks : Bounded (fun h i=>(L h i).blocks)
  lanes : Bounded (fun h i=>(L h i).lanes)
  slots : Bounded (fun h i=>(L h i).slots)
  old : ∃K:ℕ,∀ᶠ h:ℕ in atTop,∀i,max (L h i).fieldBits (L h i).metaBits*(L h i).lanes≤K*h
  newKey : ∃K:ℕ,∀ᶠ h:ℕ in atTop,∀i,max (L h i).selectorBits (L h i).shortBits*((L h i).blocks+1)*(L h i).lanes≤K*h

theorem rate (r : ScalarRoom L) : Bounded (fun h i=>(L h i).endAddress 0) :=by
  let pairs:=(Bounded.const (ι:=ι) 2).mul r.slots
  obtain ⟨K,old⟩:=r.old
  obtain ⟨T,new_⟩:=r.newKey
  have field:=old.mono fun h bound i=>(Nat.mul_le_mul_right _ (le_max_left (L h i).fieldBits _)).trans (bound i)
  have «meta»:=old.mono fun h bound i=>(Nat.mul_le_mul_right _ (le_max_right _ (L h i).metaBits)).trans (bound i)
  have selector:=new_.mono fun h bound i=>(Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _
    (le_max_left (L h i).selectorBits _))).trans (bound i)
  have short:=new_.mono fun h bound i=>(Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _
    (le_max_right _ (L h i).shortBits))).trans (bound i)
  have a:=Panel.rate (fun h i=>(L h i).labels) r.sites r.groups r.blocks r.lanes pairs ⟨K,field⟩ ⟨T,selector⟩
  have b:=Panel.rate (fun h i=>(L h i).tickets) r.sites r.groups r.blocks r.lanes pairs ⟨K,field⟩ ⟨T,short⟩
  have c:=Panel.rate (fun h i=>(L h i).halos) r.sites r.groups r.blocks r.lanes r.slots ⟨K,«meta»⟩ ⟨T,short⟩
  apply ((a.add b).add c).of_le
  intro h i
  rw [endAddress,(L h i).halos.extent,haloBase,(L h i).tickets.extent]
  exact le_rfl
end Layout
end Hierarchy.DescentResetOriginalDonors

end OAI
