import OAI.Optimization.LinearProgramming.RAM.Code

/-! A static frame for caller-owned address registers above the fixed temporaries of a block. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace RAM

/-- The instruction writes no address cell with index at least `firstFree`.
An indirect address-bank store has no such static guarantee. Scalar-bank writes are unrestricted. -/
def Instr.indexWritesBelow (firstFree : Nat) : Instr → Bool
  | .addrConst d _ | .addrCopy d _ | .incr d _ | .decr d _ | .addrLoad d _ => decide (d < firstFree)
  | .addrStore _ _ => false
  | _ => true

def Block.indexWritesBelow (firstFree : Nat) : Block → Bool
  | .skip => true
  | .op i => i.indexWritesBelow firstFree
  | .seq a b | .branch _ a b => a.indexWritesBelow firstFree && b.indexWritesBelow firstFree
  | .loop _ a => a.indexWritesBelow firstFree

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

private theorem write_frame (op : Instr) (m z : Memory K) (R j : Nat)
    (run : ∀ pc, execInstr op (m.atPC pc) = some (z.atPC (pc+1)))
    (ok : op.indexWritesBelow R = true) (hj : R ≤ j) : z.index j = m.index j := by
  have h := congrArg (fun result : Option (State K) => result.map (fun s => s.index j)) (run 0)
  cases op with
  | addrConst d _ | addrCopy d _ | incr d _ | decr d _ | addrLoad d _ =>
    have hd : d < R := of_decide_eq_true ok
    have hne : j ≠ d := by omega
    simpa only [execInstr,Memory.atPC,State.putIndex,Option.map_some,Option.some.injEq,
      Function.update_of_ne hne] using h.symm
  | addrStore _ _ => contradiction
  | div d a b =>
    by_cases hb : m.data b = 0
    · simp [execInstr,Memory.atPC,hb] at h
    · simpa [execInstr,Memory.atPC,hb,State.putData] using h.symm
  | const _ _ | copy _ _ | add _ _ _ | sub _ _ _ | mul _ _ _ | load _ _ | store _ _ =>
    simpa [execInstr,Memory.atPC,State.putData] using h.symm
  | branchLT _ _ _ _ | branchAddrLT _ _ _ _ | jump _ | halt _ =>
    simpa [execInstr,Memory.atPC,State.putData] using h.symm

/-- The register guarantee holds through every iteration, independently of the value stored. -/
theorem Block.Eval.index_frame {safe : Memory K → Prop} {b : Block} {m z : Memory K} {k : Nat}
    (run : Block.Eval safe b m k z) {R j : Nat} (static : b.indexWritesBelow R = true)
    (hj : R ≤ j) : z.index j = m.index j := by
  induction run with
  | skip => rfl
  | op _ _ h => exact write_frame _ _ _ R j h static hj
  | seq _ _ ih1 ih2 =>
    obtain ⟨h1,h2⟩ := Bool.and_eq_true_iff.mp static
    exact (ih2 h2).trans (ih1 h1)
  | branchTrue _ _ ih => exact ih (Bool.and_eq_true_iff.mp static).1
  | branchFalse _ _ ih => exact ih (Bool.and_eq_true_iff.mp static).2
  | loopFalse => rfl
  | loopTrue _ _ _ ih1 ih2 => exact (ih2 static).trans (ih1 static)

end RAM
end LinearProgramming
end Optimization
end OAI
