import Mathlib.Data.List.OfFn
import Mathlib.Logic.Equiv.Fin.Basic

namespace OAI
/-! # Original leg and chunk coordinates in the rectangular seed operand page -/
namespace Hierarchy.DescentPackedSeed.Rectangle

theorem flattened {α : Type} {K N : ℕ} (a : Fin K→Fin N→α) :
    (List.ofFn (fun i=>List.ofFn (a i))).flatten=
      List.ofFn (fun j : Fin (K*N)=>let key : Fin K×Fin N:=finProdFinEquiv.symm j;a key.1 key.2) :=by
  rw [List.ofFn_mul]
  apply congrArg List.flatten
  apply congrArg List.ofFn
  funext i
  apply congrArg List.ofFn
  funext d
  have code : (⟨i.val*N+d.val,by simpa only [finProdFinEquiv_apply_val,Nat.mul_comm,Nat.add_comm] using
      (finProdFinEquiv (i,d)).isLt⟩:Fin (K*N))=finProdFinEquiv (i,d):=by
    apply Fin.ext
    simp [finProdFinEquiv_apply_val,Nat.mul_comm,Nat.add_comm]
  rw [code,Equiv.symm_apply_apply]

theorem singleton_flat {α : Type} (xs : List α) : (xs.map (fun a=>[a])).flatten=xs :=by
  induction xs with
  | nil=>rfl
  | cons a tail ih=>simp [ih]

theorem before_rect {N t : ℕ} (leg : Fin 3) (chunk : Fin N) (slot : Fin (3*N))
    (ordinal : finProdFinEquiv (leg,chunk)=slot) :
    slot.val<t*N ↔ leg.val<t :=by
  have at_:=congrArg Fin.val ordinal
  simp only [finProdFinEquiv_apply_val,Nat.mul_comm N leg.val] at at_
  by_cases low : leg.val<t
  · have small : leg.val*N+chunk.val<(leg.val+1)*N:=by
      rw [Nat.succ_mul]
      exact Nat.add_lt_add_left chunk.isLt _
    have fit:=(small.trans_le (Nat.mul_le_mul_right N (Nat.succ_le_of_lt low)))
    exact ⟨fun _=>low,fun _=>by omega⟩
  · have bound:=Nat.mul_le_mul_right N (Nat.le_of_not_gt low)
    exact ⟨fun h=>by omega,fun h=>(low h).elim⟩

end Hierarchy.DescentPackedSeed.Rectangle

end OAI
