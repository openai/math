import OAI.ThreeFlat.Diagonal.TraceBanks
import OAI.ThreeFlat.Diagonal.TraceWordTests
import OAI.Computability.VPVNP.RAMMemory

namespace OAI
/-! # Joining two native input banks and their static pin maps -/
namespace Hierarchy.DescentSeedRoot
open ThreeFlat.Diagonal TraceBanks
open Computability.VPVNP.BurstRAM Computability.VPVNP.RAMMemory

noncomputable section

/-- The immutable seed prefix and further native input banks share one address
space and one static pin map. Reading the second bank subtracts exactly the seed length. -/
def joinWords {w n m : ℕ} (left : Fin n→Word w) (right : Fin m→Word w) : ℕ→Word w :=
  fun a=>if ha : a<n+m then (Sum.elim left right) (finSumFinEquiv.symm ⟨a,ha⟩) else 0

def joinPins {w n m : ℕ} {K : Type*} (left : Fin n×Fin (w+1)→K)
    (right : Fin m×Fin (w+1)→K) (q : Fin (n+m)×Fin (w+1)) : K :=
  (finSumFinEquiv.symm q.1).elim (fun a=>left (a,q.2)) (fun b=>right (b,q.2))

theorem join_agrees {w n m : ℕ} {K : Type*} (emit : K→Bool) (a : Fin n→Word w) (b : Fin m→Word w)
    (pa : Fin n×Fin (w+1)→K) (pb : Fin m×Fin (w+1)→K)
    (ha : ∀ z,emit (pa z)=TraceWords.bits (wide (a z.1)) z.2)
    (hb : ∀ z,emit (pb z)=TraceWords.bits (wide (b z.1)) z.2)
    (z : Fin (n+m)×Fin (w+1)) :
    emit (joinPins pa pb z)=TraceWords.bits (wide (joinWords a b z.1.val)) z.2 := by
  simp only [joinPins,joinWords,dite_eq_left z.1.isLt]
  cases eq : finSumFinEquiv.symm z.1 with
  | inl i => exact ha (i,z.2)
  | inr i => exact hb (i,z.2)

theorem join_left {w n m : ℕ} (a : Fin n→Word w) (b : Fin m→Word w) (i : Fin n) :
    initialMemory (n+m) (joinWords a b) i.val=a i := by
  change initialMemory (n+m) (joinWords a b) (finSumFinEquiv (Sum.inl i : Fin n⊕Fin m)).val=a i
  let pos := finSumFinEquiv (Sum.inl i : Fin n⊕Fin m)
  change initialMemory (n+m) (joinWords a b) pos.val=a i
  rw [initialMemory,ite_eq_left pos.isLt,joinWords,dite_eq_left pos.isLt]
  change Sum.elim a b (finSumFinEquiv.symm (finSumFinEquiv (Sum.inl i : Fin n⊕Fin m)))=a i
  simp only [Equiv.symm_apply_apply,Sum.elim_inl]

theorem join_right {w n m : ℕ} (a : Fin n→Word w) (b : Fin m→Word w) (i : Fin m) :
    initialMemory (n+m) (joinWords a b) (n+i.val)=b i := by
  change initialMemory (n+m) (joinWords a b) (finSumFinEquiv (Sum.inr i : Fin n⊕Fin m)).val=b i
  let pos := finSumFinEquiv (Sum.inr i : Fin n⊕Fin m)
  change initialMemory (n+m) (joinWords a b) pos.val=b i
  rw [initialMemory,ite_eq_left pos.isLt,joinWords,dite_eq_left pos.isLt]
  change Sum.elim a b (finSumFinEquiv.symm (finSumFinEquiv (Sum.inr i : Fin n⊕Fin m)))=b i
  simp only [Equiv.symm_apply_apply,Sum.elim_inr]


end
end Hierarchy.DescentSeedRoot

end OAI
