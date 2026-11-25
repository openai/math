import OAI.Optimization.LinearProgramming.RAM.Call
import OAI.Optimization.LinearProgramming.RAM.Code

/-! Relocatable code layout for the two-call optimization reduction. The three
terminal blocks precede the second call, enabling direct tag-to-PC returns. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace PrimalDual
namespace Bridge

open RAM RAM.Block

structure EndBlocks where
  infeasible : Block
  optimum : Block
  ray : Block
  stage : Block
  prepare : Block

namespace EndBlocks

def stopCode (b : Block) (pc tag : Nat) := b.compile pc ++ [.halt tag]

@[simp] theorem length_stopCode (b : Block) (pc tag : Nat) : (stopCode b pc tag).length=b.size+1 := by
  simp [stopCode]

def optPC (bs : EndBlocks) (pc : Nat) := pc+(bs.infeasible.size+1)
def rayPC (bs : EndBlocks) (pc : Nat) := bs.optPC pc+(bs.optimum.size+1)
def stagePC (bs : EndBlocks) (pc : Nat) := bs.rayPC pc+(bs.ray.size+1)
def prepPC (bs : EndBlocks) (pc : Nat) := bs.stagePC pc+bs.stage.size
def callPC (bs : EndBlocks) (pc : Nat) := bs.prepPC pc+bs.prepare.size

def firstRet (bs : EndBlocks) (pc tag : Nat) := if tag=0 then bs.stagePC pc else pc
def secondRet (bs : EndBlocks) (pc tag : Nat) := if tag=0 then bs.optPC pc else bs.rayPC pc

def emit (bs : EndBlocks) (p : Program) (pc : Nat) : Program :=
  stopCode bs.infeasible pc 0 ++ (stopCode bs.optimum (bs.optPC pc) 1 ++
    (stopCode bs.ray (bs.rayPC pc) 2 ++ (bs.stage.compile (bs.stagePC pc) ++
      (bs.prepare.compile (bs.prepPC pc) ++ Call.subroutine p (bs.callPC pc) (bs.secondRet pc)))))

structure Placed (bs : EndBlocks) (target original : Program) (pc : Nat) : Prop where
  first : CodeAt target pc (stopCode bs.infeasible pc 0)
  optimum : CodeAt target (bs.optPC pc) (stopCode bs.optimum (bs.optPC pc) 1)
  ray : CodeAt target (bs.rayPC pc) (stopCode bs.ray (bs.rayPC pc) 2)
  stage : CodeAt target (bs.stagePC pc) (bs.stage.compile (bs.stagePC pc))
  prepare : CodeAt target (bs.prepPC pc) (bs.prepare.compile (bs.prepPC pc))
  callee : CodeAt target (bs.callPC pc) (Call.subroutine original (bs.callPC pc) (bs.secondRet pc))

theorem placed {bs : EndBlocks} {target original : Program} {pc : Nat}
    (h : CodeAt target pc (bs.emit original pc)) : bs.Placed target original pc := by
  unfold emit at h
  have h2 := h.right
  rw [length_stopCode] at h2
  have h3 := h2.right
  rw [length_stopCode] at h3
  have h4 := h3.right
  rw [length_stopCode] at h4
  have h5 := h4.right
  rw [length_compile] at h5
  have h6 := h5.right
  rw [length_compile] at h6
  exact ⟨h.left,h2.left,h3.left,h4.left,h5.left,h6⟩

end EndBlocks
end Bridge
end PrimalDual
end LinearProgramming
end Optimization
end OAI
