import OAI.ThreeFlat.Diagonal.PhysicalBlockSchedule

namespace OAI
/-! # Lane counts consumed by repetitions of a fixed physical block -/

noncomputable section
namespace ThreeFlat.Diagonal.PhysicalStage

open HistoryContraction
variable {F : Type} [Field F]

private theorem charge_cast {s t : ℕ} (e : s=t) (p : Program F s) :
    (e ▸ p : Program F t).charge=p.charge := by cases e; rfl

namespace Block
variable (B : Block F)

def shrinkLaneBudget : ℕ → ℕ → ℕ
  | 0, _ => 0
  | n+1, i => shrinkCharge (B.exponent i) + shrinkLaneBudget n (i+1)

def blockCharge : ℕ := B.shrinkLaneBudget B.levels 0 + B.exponent B.levels

theorem charge_shrinkPrefix (n i : ℕ) (p : Program F (B.exponent (i+n))) :
    (B.shrinkPrefix n i p).charge = B.shrinkLaneBudget n i + p.charge := by
  induction n generalizing i with
  | zero => simp [shrinkPrefix, shrinkLaneBudget]
  | succ n ih => simp only [shrinkPrefix,Program.charge,ih,charge_cast,shrinkLaneBudget,Nat.add_assoc]

theorem charge_prefix (p : Program F (B.exponent 0)) :
    (B.prefix p).charge = B.blockCharge + p.charge := by
  simp only [«prefix»,charge_shrinkPrefix,charge_cast,Program.charge,blockCharge,Nat.add_assoc]

theorem charge_repeat (n : ℕ) : (B.repeat n).charge = B.blockCharge*n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [«repeat»,charge_prefix,ih,Nat.mul_succ,Nat.add_comm]

end Block
end ThreeFlat.Diagonal.PhysicalStage

end
end OAI
