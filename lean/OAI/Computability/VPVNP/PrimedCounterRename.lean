import OAI.Computability.VPVNP.PrimedInputRAMFlowRun

/-!
# Register and public-word placement for the pair counter

The input passes and the preorder parser use their own local operand numbers.
Relabeling the operands embeds each finite block into the common auxiliary
machine. A native write to a register still has exactly the specified effect
on the embedded register file.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PrimedCounter

open BurstRAM BurstRAM.PrivateRAM PrimedInputRAM PrimedStackRAM

variable {r k R K w : ℕ}

/-- Relocate both operand spaces of a native instruction. -/
def renameOp (reg : Fin r → Fin R) (pub : Fin k → Fin K) : Op r k → Op R K
  | .constant dst v => .constant (reg dst) v
  | .publicWord dst i => .publicWord (reg dst) (pub i)
  | .copy dst src => .copy (reg dst) (reg src)
  | .stateWord dst => .stateWord (reg dst)
  | .binary op dst x y => .binary op (reg dst) (reg x) (reg y)
  | .read dst a => .read (reg dst) (reg a)
  | .write a s => .write (reg a) (reg s)
  | .guardEq x y => .guardEq (reg x) (reg y)
  | .guardLt x y => .guardLt (reg x) (reg y)

private theorem restrict_update (rs : Regs w R) (reg : Fin r ↪ Fin R) (dst : Fin r) (v : Word w) :
    (Function.update rs (reg dst) v) ∘ reg = Function.update (rs ∘ reg) dst v := by
  funext i
  by_cases hi : i = dst <;> simp [hi, Function.comp_apply]

/-- Restricting the updated large register file gives the same operation as
executing directly on the small register file. Reads, writes, guard failures
and the emitted RAM event agree exactly. -/
theorem effect_rename (reg : Fin r ↪ Fin R) (pub : Fin k → Fin K) (op : Op r k)
    (data : Fin K → Word w) (state : Word w) (rs : Regs w R) (mem : Memory w) :
    ((renameOp reg pub op).effect data state rs mem).map (fun (e,r',m') => (e,r' ∘ reg,m')) =
      op.effect (data ∘ pub) state (rs ∘ reg) mem := by
  cases op <;> simp [renameOp, Op.effect, restrict_update, Function.comp_apply]

/-- Relabel the operands of an entire structured graph, preserving its branch
order and all of its loop back edges. -/
def renameFlow (reg : Fin r → Fin R) (pub : Fin k → Fin K) : Flow r k → Flow R K
  | .line op => .line (renameOp reg pub op)
  | .seq a b => .seq (renameFlow reg pub a) (renameFlow reg pub b)
  | .ifEq x y a b => .ifEq (reg x) (reg y) (renameFlow reg pub a) (renameFlow reg pub b)
  | .ifLt x y a b => .ifLt (reg x) (reg y) (renameFlow reg pub a) (renameFlow reg pub b)
  | .branch a b => .branch (renameFlow reg pub a) (renameFlow reg pub b)
  | .whileLt x y a => .whileLt (reg x) (reg y) (renameFlow reg pub a)

theorem rename_length (reg : Fin r → Fin R) (pub : Fin k → Fin K) (a : Flow r k) :
    (renameFlow reg pub a).length = a.length := by
  induction a <;> simp_all [renameFlow, Flow.length]

/-- Instruction labels are transported according to their enclosing blocks. -/
def renameLabels (reg : Fin r → Fin R) (pub : Fin k → Fin K) :
    (a : Flow r k) → a.Label ≃ (renameFlow reg pub a).Label
  | .line _ => Equiv.refl Unit
  | .seq a b => (renameLabels reg pub a).sumCongr (renameLabels reg pub b)
  | .ifEq _ _ a b | .ifLt _ _ a b | .branch a b =>
    (Equiv.refl Unit).sumCongr ((renameLabels reg pub a).sumCongr (renameLabels reg pub b))
  | .whileLt _ _ a => (Equiv.refl Unit).sumCongr (renameLabels reg pub a)

theorem rename_entry (reg : Fin r → Fin R) (pub : Fin k → Fin K) (a : Flow r k) :
    renameLabels reg pub a a.entry = (renameFlow reg pub a).entry := by
  induction a with
  | seq a b ha _ => exact congrArg Sum.inl ha
  | _ => rfl

end PrimedCounter

end VPVNP
end Computability
end OAI
