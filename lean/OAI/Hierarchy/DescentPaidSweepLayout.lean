import OAI.Hierarchy.DescentPackedActorMask

namespace OAI
/-! # Retained, dyadic banks for every ordinary successor's paid and occupied rows -/
namespace Hierarchy.DescentPaidResidentCount.Sweep
open DescentSIMDLookup DescentPackedActorMask ProtocolRAM
variable (base p D cap b n H G M : ℕ)

def rowCount := H*chunks G M
def span := 2^(Nat.clog 2 (p*rowCount H G M))
def maskBits := (n*actors D cap)*M
def sumBits := (1*actors D cap+b*D)*M
def sumBase :=base+(p*2)*2^(maskBits D cap n M)
def paidBank : Bank :=⟨sumBase base p D cap n M+2*2^(sumBits D cap b M),Nat.clog 2 (p*rowCount H G M)⟩
def actorBase := (paidBank base p D cap b n H G M).base+span p H G M
def aliveBank : Bank :=⟨actorBase base p D cap b n H G M+(p*2)*2^(maskBits D cap n M),Nat.clog 2 (p*rowCount H G M)⟩
def roof := (aliveBank base p D cap b n H G M).base+span p H G M

theorem roof_affine : roof base p D cap b n H G M=base+roof 0 p D cap b n H G M := by
  simp [roof,aliveBank,actorBase,paidBank,sumBase,Nat.add_assoc]

theorem covered : p*rowCount H G M≤ span p H G M := Nat.le_pow_clog (by decide) _

theorem geometry :
    base≤ sumBase base p D cap n M ∧
    sumBase base p D cap n M≤(paidBank base p D cap b n H G M).base ∧
    (paidBank base p D cap b n H G M).base+p*rowCount H G M≤actorBase base p D cap b n H G M ∧
    actorBase base p D cap b n H G M≤(aliveBank base p D cap b n H G M).base ∧
    (aliveBank base p D cap b n H G M).base+p*rowCount H G M≤roof base p D cap b n H G M :=
  ⟨Nat.le_add_right _ _,Nat.le_add_right _ _,Nat.add_le_add_left (covered p H G M) _,
    Nat.le_add_right _ _,Nat.add_le_add_left (covered p H G M) _⟩

end Hierarchy.DescentPaidResidentCount.Sweep

end OAI
