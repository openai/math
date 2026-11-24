import OAI.Computability.VPVNP.PrimedInputRAMOpcodeExecutionTable

/-!
# Private register reset before the embedded input body

The standalone assembler prologue sets registers 4, 5 and 30 before entering
the input body. The combined pair program instead uses fresh input registers.
Parameter loading and cursor decoding overwrite these three registers before
dispatch, and have identical events and post-registers at either entry.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PrimedCounter.InputPrefix

open BurstRAM BurstRAM.PrivateRAM PrimedStackRAM PrimedInputRAM PrimedInputRAM.Opcodes
variable {w : ℕ}
private def straight : PrimedInputRAM.Flow 48 16 → Prop
  | .line _ => True
  | .seq a b => straight a ∧ straight b
  | _ => False

private theorem exec_straight_once {pub : Pub → Word w} {st : Word w} {rs out : Regs w 48}
    {m m' : Memory w} {es : List (Event w)} {a : Code}
    (h : Flow.Exec pub st a rs m es out m') (hs : straight a) :
    Flow.once pub st false a rs m = some (es,out,m') := by
  induction h with
  | line he => simp [Flow.once, he]
  | seq _ _ iha ihb => simp [Flow.once, iha hs.1, ihb hs.2]
  | ifEqYes | ifEqNo | ifLtYes | ifLtNo | branchYes | branchNo | whileDone | whileStep => contradiction

set_option maxHeartbeats 2000000 in
private theorem prefixRegs_erased (pub : Pub → Word w) (st : Word w) (m : Memory w) :
    Flow.once pub st false (.seq loadParameters unpackCursor) (prefixRegs st (pub 0)) m =
      Flow.once pub st false (.seq loadParameters unpackCursor) (fun _ ↦ 0) m := by
  simp only [loadParameters, parameterTail, unpackCursor, Opcodes.sequence, Opcodes.bin, Opcodes.set,
    Opcodes.line, Flow.once,
    Op.effect, List.foldl_cons, List.foldl_nil, Option.map_some, bind, Option.bind_some, pure]
  simp only [Option.some.injEq, Prod.mk.injEq, and_true]
  constructor
  · simp [prefixRegs]
  · funext i
    by_cases h4 : i = 4 <;> by_cases h5 : i = 5 <;> by_cases h30 : i = 30 <;>
      simp [Function.update_apply, prefixRegs, h4, h5, h30]

theorem dataCall_prefixRegs {pub : Pub → Word w} {st : Word w} {m m' : Memory w}
    {es : List (Event w)} {out : Regs w 48}
    (h : Flow.Exec pub st body (fun _ ↦ 0) m es out m') :
    Flow.Exec pub st body (prefixRegs st (pub 0)) m es out m' := by
  cases h with | seq he hact =>
    cases he with | seq he hd =>
      have hlin : straight (.seq loadParameters unpackCursor) := by
        simp [straight, loadParameters, parameterTail, unpackCursor, Opcodes.sequence, Opcodes.set,
          Opcodes.line, Opcodes.bin]
      have ho := exec_straight_once he hlin
      rw [← prefixRegs_erased] at ho
      exact ((Flow.once_sound pub st false _ _ _ ho).1.seq hd).seq hact
end PrimedCounter.InputPrefix

end VPVNP
end Computability
end OAI
