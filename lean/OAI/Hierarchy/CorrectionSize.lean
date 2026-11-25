import OAI.Hierarchy.CorrectionAssembly
import OAI.Hierarchy.CorrectionBatch

namespace OAI
/-! # Linear total size of the sparse correction network

An exact module of size at most a fixed multiple of the correction spacing
times the one-copy size fits in a constant multiple of the batch budget.
-/

noncomputable section
namespace Hierarchy.CorrectionSize

open ThreeFlat Routing
open Catalyst CorrectionAssembly CorrectionBatch CorrectionFrame
open scoped Classical BigOperators

def BatchBound (F : Type*) [Field F] (E C : ℕ) : Prop :=
    ∀ {k p s : ℕ} (X : Approximation F k p)
      (N : BitNetwork F (Fintype.card (Fin p))) (H : ℕ),
      0 < s → 2 ≤ H → (Nat.log 2 (s+1)+2)^3 ≤ X.size →
      N.cells+N.internal ≤ E*H*X.size →
      ∃ A : BitNetwork F (Fintype.card (Fin s × Port p X.width)),
        (package X.width A).size ≤ C*s*X.size ∧
        ∀ x, TypedWiring.value A x = retained X (TypedWiring.value N) (s/H) x

theorem linear_batch_uniform (E : ℕ) : ∃ C : ℕ, ∀ (F : Type*) [Field F], BatchBound F E C := by
  obtain ⟨K,c,make⟩ := sparse_networks_uniform
  refine ⟨4*(65537+232+6*c+176*K*E)+2,fun F _ {k p s} X N H hs hH small hN => ?_⟩
  let S := X.size
  have hquo : (s/H)*H ≤ s := Nat.div_mul_le_self s H
  have hquota : 2*(s/H) ≤ s := (Nat.mul_le_mul_right _ hH).trans (by simpa [Nat.mul_comm] using hquo)
  obtain ⟨A,bound,ev⟩ := make F X N _ hquota
  refine ⟨A,?_,ev⟩
  have hS : 1 ≤ S := (by omega : 1 ≤ Nat.log 2 (s+1)+2).trans
    ((Nat.le_self_pow (by decide : (3:ℕ) ≠ 0) _).trans small)
  have hdata : p ≤ S := by
    simp [S,Approximation.size,Port,Fintype.card_sum]; omega
  have hw : Fintype.card (Wire X.width) ≤ S := by
    simp [S,Approximation.size,Port,Fintype.card_sum,Fintype.card_prod]; omega
  have hnet : X.network.cells+X.network.internal ≤ S := Nat.le_add_right _ _
  have hopen : Fintype.card (Port p X.width) ≤ S := Nat.le_add_left _ _
  have hlog : Nat.log 2 s ≤ S := (Nat.log_mono_right (Nat.le_succ _)).trans
    ((by omega : Nat.log 2 (s+1) ≤ Nat.log 2 (s+1)+2).trans
      ((Nat.le_self_pow (by decide : (3:ℕ) ≠ 0) _).trans small))
  have overhead : 32768*(s+1)*(Nat.log 2 (s+1)+2)^3+1 ≤ 65537*(s*S) := by
    have he : s+1 ≤ 2*s := by omega
    have h := Nat.mul_le_mul he small
    have hsS : 1 ≤ s*S := Nat.mul_pos hs hS
    nlinarith only [h,hsS]
  have rowBound := Nat.mul_le_mul_left s
    (show (16+(176*X.network.cells+29*X.network.internal))+40*Fintype.card (Wire X.width)
      ≤ 232*S by omega)
  have routeBound := Nat.mul_le_mul_right c (Nat.mul_le_mul_left s
    (show Nat.log 2 s+p+4 ≤ 6*S by omega))
  have exactBound : K*(s/H)*(176*N.cells+29*N.internal) ≤ 176*K*E*(s*S) := by
    calc
      _ ≤ K*(s/H)*(176*(E*H*S)) := Nat.mul_le_mul_left _ (by dsimp [S]; omega)
      _ = (176*K*E*S)*((s/H)*H) := by ring
      _ ≤ (176*K*E*S)*s := Nat.mul_le_mul_left _ hquo
      _ = _ := by ring
  have extBound := Nat.mul_le_mul_left s hopen
  have hsS := Nat.mul_pos hs hS
  rw [size_package]
  change A.cells+A.internal+s*Fintype.card (Port p X.width) ≤ _*s*S
  nlinarith only [bound,overhead,rowBound,routeBound,exactBound,extBound,hsS]

theorem linear_batch (F : Type*) [Field F] (E : ℕ) : ∃ C : ℕ, BatchBound F E C := by
  obtain ⟨C,h⟩ := linear_batch_uniform E
  exact ⟨C,h F⟩

end Hierarchy.CorrectionSize

end
end OAI
