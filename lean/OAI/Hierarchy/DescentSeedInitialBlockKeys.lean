import OAI.Hierarchy.DescentAtomSchedule

namespace OAI
/-! # The physical census ordinal for the seed packet's original group and block -/
namespace Hierarchy.DescentCompiler.AtomSchedule
variable (S : AtomSchedule) {k : ℕ}

theorem seed_population_eq (radix : S.radix=2^k) : S.copies=S.groupCount 0*2^k :=by
  simp only [copies,groupCount,Nat.sub_zero,pow_succ,←radix,Nat.mul_assoc]

theorem seed_block_index (radix : S.radix=2^k) (g : Fin (S.groupCount 0)) (x : Fin (2^k)) :
    ((S.initialDigits radix).symm (g,x))=
      (finProdFinEquiv (g,x)).cast (S.seed_population_eq radix).symm :=by
  rfl

end Hierarchy.DescentCompiler.AtomSchedule

end OAI
