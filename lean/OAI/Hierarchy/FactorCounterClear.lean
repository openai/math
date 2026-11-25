import OAI.Hierarchy.FactorBucketPass

namespace OAI
/-! # Clearing the native counter bank before the owner pass -/

namespace Hierarchy.FactorBucketRAM

open Computability.VPVNP.BurstRAM PrivateRAM Computability.VPVNP.PrimedStackRAM
open ThreeFlat.RAM PhysicalProcedure
open scoped Fin.CommRing
variable {width r k : ℕ}

def clearOps : List (Op 14 12) :=
  [.publicWord 2 9,.binary .add 2 2 0,.constant 3 0,.write 2 3,
   .constant 4 1,.binary .add 0 0 4]

def clearStep (v : Parameters width) (i : Word width) (m : Memory width) : Memory width :=
  writeMemory m (v 9+i) 0

theorem clear_trace (reg : Fin 14 ↪ Fin r) (pub : Fin 12 → Fin k) (v : Fin k → Word width)
    (state : Word width) (rs : Regs width r) (m : Memory width) :
    Executes clearOps clearStep reg pub v state rs m := by
  simp [Executes,clearOps,clearStep,Function.comp_apply,OrdinalOpLoop.relocate,trace,Op.effect,
    BinaryOp.eval,Function.update,reg.injective.eq_iff]

theorem clear_bank (v : Parameters width) (m : Memory width) (base n : ℕ)
    (atBase : v 9=(base:Word width)) (fits : base+n≤2^width) (a : ℕ) :
    iterRows clearStep v m n a = if base≤a ∧ a<base+n then 0 else m a := by
  induction n with
  | zero => simp [iterRows]
  | succ n ih =>
    have bounded : base+n<2^width := by omega
    simp only [iterRows,clearStep,atBase,←Nat.cast_add]
    rw [GridPassageRAMRow.writeMemory_nat _ _ bounded]
    by_cases eq : a=base+n
    · subst a; simp []
    · rw [Function.update_of_ne eq,ih (by omega)]
      by_cases inside : base≤a ∧ a<base+n
      · simp [inside, show base≤a ∧ a<base+(n+1) by omega]
      · simp [inside,show ¬(base≤a ∧ a<base+(n+1)) by omega]

end Hierarchy.FactorBucketRAM

end OAI
