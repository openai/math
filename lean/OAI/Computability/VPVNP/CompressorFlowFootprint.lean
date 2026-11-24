import OAI.Computability.VPVNP.PrimedInputRAMFlowComplete
import OAI.Computability.VPVNP.RAMRecords
import OAI.Computability.VPVNP.RAMChoicePrefix
import OAI.Computability.VPVNP.CompressorSourceTransport

/-!
# Event support of the private compressor computations

An accepting flow with an empty choice tape fixes its entire event list.
A flow containing only register operations and control transfers accesses
no external cells, including when its finite execution takes loop branches.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.FlowFootprint

open BurstRAM PrimedInputRAM PrimedStackRAM SourceTransport

variable {w r k : ℕ}

theorem events_eq {f : Flow r k} {pub : Fin k → Word w} {s : Word w} {rs r₁ r₂ : Regs w r}
    {m m₁ m₂ : Memory w} {es fs : List (Event w)}
    (first : Flow.Exec pub s f rs m es r₁ m₁) (empty : choiceBits es = [])
    (second : Flow.Exec pub s f rs m fs r₂ m₂) : es = fs := by
  let left : Report w := ⟨es,none⟩
  let right : Report w := ⟨fs,none⟩
  have a := (Flow.template_execute_iff f none pub s (fun _ => 0) rs m (es.length+1) [] left).mpr
    ⟨r₁,m₁,first,rfl,Nat.lt_succ_self _,empty⟩
  have b := (Flow.template_execute_iff f none pub s (fun _ => 0) rs m (fs.length+1) ([] ++ choiceBits fs) right).mpr
    ⟨r₂,m₂,second,rfl,Nat.lt_succ_self _,rfl⟩
  exact congrArg Report.events (execute_prefix_unique a b).2

/-- Test whether an instruction avoids external memory reads and writes. -/
def privateOp : Op r k → Bool
  | .read .. | .write .. => false
  | _ => true

/-- Recursively check that every instruction in a flow avoids external memory reads and writes. -/
def privateOnly : Flow r k → Bool
  | .line op => privateOp op
  | .seq a b | .ifEq _ _ a b | .ifLt _ _ a b | .branch a b => privateOnly a && privateOnly b
  | .whileLt _ _ a => privateOnly a

private theorem private_tick {op : Op r k} {pub : Fin k → Word w} {s : Word w}
    {rs out : Regs w r} {m post : Memory w} {e : Event w}
    (code : privateOp op = true) (run : op.effect pub s rs m = some (e,out,post)) : e = .tick := by
  cases op <;> simp only [privateOp,Bool.false_eq_true] at code
  all_goals simp only [Op.effect,Option.some.injEq,Prod.mk.injEq] at run
  all_goals first | exact run.1.symm | split at run <;> simp_all

theorem noProbes {f : Flow r k} {pub : Fin k → Word w} {s rs m es out post}
    (code : privateOnly f = true) (run : Flow.Exec pub s f rs m es out post) :
    countProbes es = 0 := by
  have add (es fs : List (Event w)) : countProbes (es ++ fs) = countProbes es + countProbes fs := by
    induction es with
    | nil => simp [countProbes]
    | cons e es ih => cases e <;> simp [countProbes,ih,Nat.add_assoc]
  induction run with
  | line h => rw [private_tick code h]; rfl
  | seq _ _ ih ih' =>
    have both := Bool.and_eq_true_iff.mp code
    rw [add,ih both.1,ih' both.2]
  | ifEqYes _ _ ih | ifLtYes _ _ ih | branchYes _ ih => exact ih (Bool.and_eq_true_iff.mp code).1
  | ifEqNo _ _ ih | ifLtNo _ _ ih | branchNo _ ih => exact ih (Bool.and_eq_true_iff.mp code).2
  | whileDone => rfl
  | whileStep _ _ _ ih ih' => simp only [countProbes,add,ih code,ih' code,Nat.add_zero]

theorem bounds_of_noProbes {es : List (Event w)} (readable writable : ℕ → Prop) (h : countProbes es = 0) :
    Reads readable es ∧ Writes writable es := by
  induction es with
  | nil => exact ⟨fun _ _ hn => (List.not_mem_nil hn).elim,fun _ _ hn => (List.not_mem_nil hn).elim⟩
  | cons e es ih =>
    cases e with
    | read | write => simp [countProbes] at h
    | tick | choice =>
      obtain ⟨rd,wr⟩ := ih h
      exact ⟨fun a v hn => rd a v (List.mem_cons.mp hn |>.resolve_left (by simp)),
        fun a v hn => wr a v (List.mem_cons.mp hn |>.resolve_left (by simp))⟩

end CompressorRecords.FlowFootprint

end VPVNP
end Computability
end OAI
