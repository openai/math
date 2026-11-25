import OAI.Optimization.LinearProgramming.RAM.FrameHeaders
import OAI.Optimization.LinearProgramming.RAM.RAMFrame

/-! Compute the first unused address-register index for a block writing only statically
addressed index cells. In particular this works uniformly for address-header assemblers. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace RAM
namespace Call

open Block Tape

private def directIndex : Instr → Bool
  | .addrStore .. => false
  | _ => true

private def indexLimit : Instr → Nat
  | .addrConst d _ | .addrCopy d _ | .incr d _ | .decr d _ | .addrLoad d _ => d+1
  | _ => 0

def directIndexBlock : Block → Bool
  | .skip => true
  | .op i => directIndex i
  | .seq a b | .branch _ a b => directIndexBlock a && directIndexBlock b
  | .loop _ a => directIndexBlock a

def indexLimitBlock : Block → Nat
  | .skip => 0
  | .op i => indexLimit i
  | .seq a b | .branch _ a b => max (indexLimitBlock a) (indexLimitBlock b)
  | .loop _ a => indexLimitBlock a

theorem indexWritesBelow_of_direct (b : Block) (R : Nat) (dir : directIndexBlock b = true)
    (hR : indexLimitBlock b ≤ R) : b.indexWritesBelow R = true := by
  induction b with
  | skip => rfl
  | op i =>
    cases i <;> simp_all [directIndexBlock,directIndex,indexLimitBlock,indexLimit,
      Block.indexWritesBelow,Instr.indexWritesBelow]
  | seq a b ha hb | branch _ a b ha hb =>
    obtain ⟨h₁,h₂⟩ := Bool.and_eq_true_iff.mp dir
    exact Bool.and_eq_true_iff.mpr ⟨ha h₁ ((le_max_left _ _).trans hR),
      hb h₂ ((le_max_right _ _).trans hR)⟩
  | loop _ _ ih => exact ih dir hR

@[simp] private theorem expr_direct {n : Nat} (e : AddressTerm n) (a : Nat) :
    directIndexBlock (e.code a) = true := by
  induction e generalizing a with
  | val _ | reg _ => rfl
  | binary op l r hl hr =>
    cases op <;> simp [AddressTerm.code,hl,hr,directIndexBlock,AddressOp.code,
      addSub,multiply,countLoop,directIndex]

@[simp] theorem header_direct {n : Nat} (assigns : HeaderPlan n) (scratch : Nat) :
    directIndexBlock (HeaderPlan.code scratch assigns) = true := by
  induction assigns with
  | nil => rfl
  | cons head tail ih =>
    obtain ⟨d,e⟩ := head
    simp [HeaderPlan.code,directIndexBlock,directIndex,ih]

end Call
end RAM
end LinearProgramming
end Optimization
end OAI
