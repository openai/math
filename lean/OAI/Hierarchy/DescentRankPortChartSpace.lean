import OAI.Hierarchy.DescentScalarHaloPortROM
import OAI.Hierarchy.DescentDatedAddressRate

namespace OAI
/-! # Space for the compact actor port directory used to rank reset windows -/
namespace Hierarchy.DescentRankPortChart
open DescentPackedColony DescentSIMDLookup DescentDatedAddressBook

def rosterEnd (base H : ℕ) := base+3*2^(Nat.clog 2 (4*H))

def endAddress (base H G M : ℕ) :=
  DescentScalarHaloPortROM.stop H G M 4 (rosterEnd base H)

theorem shift (base H G M : ℕ) : endAddress base H G M=base+endAddress 0 H G M := by
  simp [endAddress,rosterEnd,DescentScalarHaloPortROM.stop,Nat.add_assoc]

theorem bounded {ι : ℕ→Type*} {H G M : ∀h,ι h→ℕ} (hi : Bounded H)
    (gi : Bounded G) (mi : Bounded M) : Bounded (fun h i=>endAddress 0 (H h i) (G h i) (M h i)) := by
  let num:=fun h i=>H h i*chunks (G h i) (M h i)
  have n : Bounded num:=hi.mul (Bounded.div (Bounded.sub (gi.add mi)))
  have four:=Bounded.const (ι:=ι) 4
  have s:=(four.mul hi).padded
  have many:=hi.mul four
  have pad:=(((many.max' (n.max' hi)).add (.const 1)).padded)
  have words:=(four.mul n).add (hi.add (n.add many))
  exact ((((Bounded.const 0).add ((Bounded.const 3).mul s)).add words).add pad)

end Hierarchy.DescentRankPortChart

end OAI
