import OAI.Hierarchy.DescentFullHostOrdinal

namespace OAI
/-! # Public predecessor and hub eligibility at a rectangular ordinary host ordinal -/
namespace Hierarchy.DescentHostDirectory
open scoped Classical
noncomputable section
theorem heapRoom (k : ℕ) : 0<2^(k+1)-1 := by have:=Nat.two_pow_pos k;rw [pow_succ];omega

def ordinaryHubRow (k slots gain t : ℕ) : ℕ×Bool :=
  let node : Fin (2^(k+1)-1):=⟨(t/slots)%(2^(k+1)-1),Nat.mod_lt _ (heapRoom k)⟩
  ((t/slots)/(2^(k+1)-1),decide (((heapIndex k).symm node).val.1=k-gain ∧ t%slots=0))

theorem ordinaryHubRow_at {V : Type} [Fintype V] (k slots gain : ℕ) (old : V→ℕ)
    (x : Key V) (member : x∈keys k slots) :
    let t:=(old x.1*(2^(k+1)-1)+nodeNumber x.2.1.1 x.2.1.2)*slots+x.2.2
    ordinaryHubRow k slots gain t=(old x.1,decide (x.2.1.1=k-gain ∧ x.2.2=0)) := by
  classical
  have endpoints:=Finset.mem_product.mp (Finset.mem_product.mp member).2
  let localNode : ↥(codes k):=⟨x.2.1,endpoints.1⟩
  have small:=Finset.mem_range.mp endpoints.2
  have a:(heapIndex k localNode).val=nodeNumber x.2.1.1 x.2.1.2:=rfl
  have nb:= (heapIndex k localNode).isLt
  rw [a] at nb
  dsimp only
  rw [Nat.mul_comm (old x.1) (2^(k+1)-1),Nat.mul_comm (_+nodeNumber _ _) slots]
  unfold ordinaryHubRow
  simp only [Nat.mul_add_div (by omega : 0<slots),Nat.div_eq_of_lt small,Nat.add_zero,
    Nat.mul_add_div (heapRoom k),Nat.div_eq_of_lt nb,Nat.mul_add_mod,Nat.mod_eq_of_lt small,Nat.mod_eq_of_lt nb]
  have eqn : (⟨nodeNumber x.2.1.1 x.2.1.2,nb⟩:Fin (2^(k+1)-1))=heapIndex k localNode:=Fin.ext a.symm
  rw [eqn,Equiv.symm_apply_apply]


end
end Hierarchy.DescentHostDirectory

end OAI
