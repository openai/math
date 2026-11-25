import OAI.Computability.NearSquareRoot.KernelEffectiveFamilyProduct
import OAI.Computability.NearSquareRoot.ScheduleRegisterAlignEffectiveTask

/-! # Fixed-command contracts for linking generated scale operations -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace EffectiveScale
open IntegerMultiplication Code CommonRegisters GeneratorSyntax KernelEffectiveFamily

/-- The witness is kept fixed when changing budgets, joining stages, or
parking a sibling tree. -/
abbrev TimedAt {I : Type} (c : Cmd) (a : I → ℕ) (src dst : I → Tree) :=
  EffectiveTask.Runs c a src dst

namespace TimedAt
variable {I J : Type} {c d : Cmd} {a b : I → ℕ} {p q s : I → Tree}

theorem on (hc : TimedAt c a p q) (j : J → I) : TimedAt c (a ∘ j) (p ∘ j) (q ∘ j) :=
  EffectiveTask.Runs.on hc j

theorem bound (hc : TimedAt c a p q) (k : ℕ) (hk : ∀ i, a i+1 ≤ k*(b i+1)) :
    TimedAt c b p q := EffectiveTask.Runs.bound hc k hk

theorem join (hc : TimedAt c a p q) (hd : TimedAt d b q s) :
    TimedAt (c.join d) (fun i => a i+b i) p s := EffectiveTask.Runs.comp hc hd

theorem left (hc : TimedAt c a p q) (sib : I → Tree) :
    TimedAt (leftCmd c) a (fun i => .fork (p i) (sib i)) (fun i => .fork (q i) (sib i)) := by
  obtain ⟨C,h⟩ := hc
  refine ⟨C+7, fun i env r => (fits_pair ((h i env (pile 0 (sib i) r)).join
    (fits_pack (q i) (sib i) r 0 env))).mono ?_⟩
  rw [Nat.add_mul]
  omega

theorem right (hc : TimedAt c a p q) (sib : I → Tree) :
    TimedAt (rightCmd c) (fun i => (sib i).count+a i)
      (fun i => .fork (sib i) (p i)) (fun i => .fork (sib i) (q i)) := by
  obtain ⟨C,h⟩ := hc
  refine ⟨91+C,fun i env r => ?_⟩
  have save := fits_move (i:=0) (u:=2) (j:=1) (by decide) (by decide) (sib i) env (pile 0 (p i) r)
  rw [pile_comm 1 _ r 0 _ (by decide)] at save
  have back := fits_move (i:=1) (u:=2) (j:=0) (by decide) (by decide) (sib i) env (pile 0 (q i) r)
  rw [pile_comm 1 _ r 0 _ (by decide)] at back
  apply (fits_pair (save.join ((h i env (pile 1 (sib i) r)).join
    (back.join (fits_pack (sib i) (q i) r 0 env))))).mono
  rw [Nat.add_mul]
  have hmul := Nat.mul_le_mul_left C (by omega : a i+1 ≤ (sib i).count+a i+1)
  dsimp only
  omega

end TimedAt
end EffectiveScale

end NearSquareRoot
end Computability
end OAI
