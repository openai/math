import OAI.Hierarchy.DescentPreparedPrivateRoots

namespace OAI
/-! # Concrete upper price of the complete public root bank, including all input gates -/
namespace Hierarchy.DescentFallbackPeriod.Projected.RootBook
open DescentSIMDLookup DescentSixParty.Chronology DescentPackedColony.Phase.Arena
open scoped Classical BigOperators
noncomputable section
variable {n r D L cap field : ℕ} (b : RootBook n r D L cap field)
local notation "Page" => RootPage r (2^n)

def maxSlots :=Finset.univ.sup (fun p:Page=>(b.table p).1)
def addressBits (M : ℕ) :=Finset.univ.sup (fun p:Page=>(b.table p).2.unit*M)

theorem width_bound (H G M : ℕ) :
    b.payloadWidth H G M ≤ 1+b.maxSlots*(2*2^(b.addressBits M))+2^(b.addressBits M)+2^(Nat.clog 2 (H*chunks G M)) := by
  change 1+Finset.univ.sup _≤_
  rw [show 1+b.maxSlots*(2*2^(b.addressBits M))+2^(b.addressBits M)+2^(Nat.clog 2 (H*chunks G M))=
    1+(b.maxSlots*(2*2^(b.addressBits M))+2^(b.addressBits M)+2^(Nat.clog 2 (H*chunks G M))) by omega]
  apply Nat.add_le_add_left
  apply Finset.sup_le
  intro p _
  let s:=b.table p
  have g:s.2.unit*M≤b.addressBits M:=Finset.le_sup (f:=fun z:Page=>(b.table z).2.unit*M) (Finset.mem_univ _)
  have inputSmall : s.2.field*s.1*M≤b.addressBits M:=
    (Nat.mul_le_mul_right M (show s.2.field*s.1≤ s.2.unit from Nat.le_add_right ..)).trans g
  have nmax:s.1≤b.maxSlots:=Finset.le_sup (f:=fun z:Page=>(b.table z).1) (Finset.mem_univ _)
  have room:=Nat.mul_le_mul nmax (Nat.mul_le_mul_left 2 (Nat.pow_le_pow_right (by decide : 0<2) g))
  have lut:=Nat.pow_le_pow_right (by decide : 0<2) inputSmall
  change 0+s.1*(2*2^(s.2.unit*M))+2^(s.2.field*s.1*M)+_≤_
  omega

def pageBound (H G M : ℕ) := (1+b.maxSlots*(2*2^(b.addressBits M))+2^(b.addressBits M)+2^(Nat.clog 2 (H*chunks G M)))+b.sharedWords M

theorem literal_fee (base H G M w : ℕ) :
    4+10*(b.book base H G M w).length≤
      4+10*((b.repeatEnd base H G M-base)+Fintype.card Page*b.pageBound H G M) := by
  have lower:base≤b.repeatEnd base H G M:=(b.limits base H G M).1.trans (b.limits base H G M).2.1
  have bound:=Nat.mul_le_mul_left (Fintype.card Page) (Nat.add_le_add_right (b.width_bound H G M) (b.sharedWords M))
  change 4+10*((b.repeatEnd base H G M+Fintype.card Page*b.width H G M)-base)≤_
  change Fintype.card Page*b.width H G M≤Fintype.card Page*b.pageBound H G M at bound
  omega

end
end Hierarchy.DescentFallbackPeriod.Projected.RootBook

end OAI
