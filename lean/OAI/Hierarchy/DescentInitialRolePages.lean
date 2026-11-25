import OAI.Hierarchy.DescentRegisterTypes
import OAI.Hierarchy.DescentSeedTokenSourceLayout
import OAI.Hierarchy.DescentSeedTokenLayout

namespace OAI
/-! # The physical primitive role-page register at the seed date -/
namespace Hierarchy.DescentDatedAddressBook
open DescentSIMDLookup ProtocolRAM
noncomputable section
namespace PriorRolePages
def bank (p : PriorRolePages) (j : ℕ) : Bank:=⟨p.first+j*p.stride,p.bits⟩
def endAddress (p : PriorRolePages) :=p.first+p.blocks*p.stride+2^p.bits
theorem fits (p : PriorRolePages) (w bound j : ℕ) (active : j<p.blocks)
    (placed : p.endAddress≤bound) (room : bound<2^w) : (p.bank j).Fits w bound:=by
  have h:=Nat.mul_le_mul_right p.stride active.le
  change p.first+p.blocks*p.stride+2^p.bits≤bound at placed
  exact ⟨Nat.two_pow_pos p.bits,by change 2^p.bits<2^w;omega,by change p.first+j*p.stride+2^p.bits≤bound;omega⟩

def transposed (base O H G X a A M : ℕ) : PriorRolePages:=
  ⟨DescentSeedTokenTransposition.out base O H G X a A M,H*chunks G M,Nat.clog 2 (H*chunks G M),X⟩
theorem transposed_pages (base O H G X a A M : ℕ) :
    let p:=transposed base O H G X a A M
    p.endAddress=DescentSeedTokenTransposition.endAddress base O H G X a A M ∧
      ∀x : Fin X,p.bank x.val=DescentSeedTokenTransposition.page base O H G X a A M x:=
  ⟨rfl,fun _=>rfl⟩

open DescentSeedRoot
open Catalyst
def initial {F : Type} [Field F] {c p : ℕ} (X : Approximation F c p)
    (R s payload k H G M base : ℕ) : PriorRolePages:=
  transposed (DescentPackedSeed.Primitive.Source.finish X R s payload base) (Fintype.card (Old X))
    H G (2^k) (DescentPackedSeed.Primitive.roleBits s) (DescentPackedSeed.Primitive.pieces payload s) M

end PriorRolePages
end
end Hierarchy.DescentDatedAddressBook

end OAI
