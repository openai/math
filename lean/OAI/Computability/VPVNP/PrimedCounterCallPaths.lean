import OAI.Computability.VPVNP.PrimedCounterCall
import OAI.Computability.VPVNP.PrimedInputRAMFlowComplete

/-!
# Reading back a native call of the scheduled pair counter

The final tick compares the next cursor with the total count. Recovering
the structured execution before that tick yields both the consumed binary
tape and the post-call external memory used by the next scheduled item.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PrimedCounter.Call

open BurstRAM BurstRAM.PrivateRAM PrimedStackRAM PrimedInputRAM

variable {r k w : ℕ}

private theorem line_memory (pub : Fin k → Word w) (state : Word w) (op : Op r k) (rs : Regs w r)
    (m : Memory w) {e rs' m'} (he : op.effect pub state rs m = some (e,rs',m')) :
    after m [e] = m' := by
  cases op <;> simp only [Op.effect] at he
  all_goals first | split at he | skip
  all_goals first | contradiction | (cases Option.some.inj he; rfl)

/-- Report replay has exactly the external-memory effect of the structured body. -/
theorem exec_memory {pub : Fin k → Word w} {state : Word w} {a : Flow r k} {rs m es rs' m'}
    (he : Flow.Exec pub state a rs m es rs' m') : after m es = m' := by
  induction he with
  | line h => exact line_memory _ _ _ _ _ h
  | seq _ _ h₁ h₂ =>
    rw [show ∀ a b : List (Event w), ∀ m, after m (a++b) = after (after m a) b by simp [after], h₁, h₂]
  | ifEqYes _ _ ih | ifEqNo _ _ ih | ifLtYes _ _ ih | ifLtNo _ _ ih | branchYes _ ih | branchNo _ ih =>
    exact ih
  | whileDone => rfl
  | whileStep _ _ _ h₁ h₂ =>
    simpa only [after, List.foldl_cons, update, List.foldl_append] using
      (congrArg (fun m => after m _ ) h₁).trans h₂

private theorem stop_spec (a : Flow r k) (next total : Fin r) (pub : Fin k → Word w)
    (state : Word w) (regs : Regs w r) (priv : Word w → Word w) (mem : Memory w)
    (bits : List Bool) (fuel : ℕ) (out : Report w) :
    let M := (template a next total).instantiate w pub
    execute M.program fuel ⟨stop a,state,regs,priv⟩ mem bits = some out ↔
      2 ≤ fuel ∧ bits = [] ∧ out = ⟨[.tick], if regs next = regs total then none else some (regs next)⟩ := by
  let M := (template a next total).instantiate w pub
  change execute M.program fuel _ mem bits = some out ↔ _
  cases fuel with
  | zero => simp [execute]
  | succ fuel =>
    cases fuel with
    | zero =>
      have hc : M.code (stop a) = .jumpEq next total (accept a) (back a) := by
        simp [M, Template.instantiate, template, stop, Instr.resize]
      simp [execute, Machine.program, hc, Instr.run]
    | succ fuel =>
      rw [execute_stop a next total pub]
      cases bits <;> simp [eq_comm]

/-- Exact decomposition of a successful native call. The inequality counts
the body events, the cursor comparison and the terminal return/accept opcode. -/
theorem execute_iff (a : Flow r k) (next total : Fin r) (pub : Fin k → Word w)
    (state : Word w) (regs : Regs w r) (priv : Word w → Word w) (mem : Memory w)
    (bits : List Bool) (fuel : ℕ) (out : Report w) :
    let M := (template a next total).instantiate w pub
    execute M.program fuel ⟨M.entry,state,regs,priv⟩ mem bits = some out ↔
      ∃ es rs' m', Flow.Exec pub state a regs mem es rs' m' ∧ es.length + 2 ≤ fuel ∧
        choiceBits es = bits ∧ out.events = es ++ [.tick] ∧
        out.result = (if rs' next = rs' total then none else some (rs' next)) ∧ after mem out.events = m' := by
  let M := (template a next total).instantiate w pub
  change execute M.program fuel ⟨pc a a.entry,state,regs,priv⟩ mem bits = some out ↔ _
  constructor
  · intro h
    obtain ⟨es,rs',m',left,rest,tail,he,hf,hbs,ht,hout⟩ :=
      (linked a next total pub).complete (reject_code a next total pub) state priv regs mem fuel bits out h
    obtain ⟨hle,rfl,rfl⟩ := (stop_spec a next total pub state rs' priv m' rest left tail).1 ht
    subst out
    refine ⟨es, rs', m', he, by omega, by simpa using hbs.symm, rfl, rfl, ?_⟩
    change after mem (es ++ [.tick]) = m'
    simpa [after, update] using exec_memory he
  · rintro ⟨es,rs',m',he,hlen,hb,hev,hr,_⟩
    let extra := fuel - (es.length + 2)
    have hx := execute_body a next total pub state regs priv mem he [] extra
    have hf : es.length + (extra+2) = fuel := by dsimp [extra]; omega
    rw [hf, List.append_nil, hb] at hx
    have ho : out = ⟨es ++ [.tick], if rs' next = rs' total then none else some (rs' next)⟩ := by
      cases out
      simp_all
    rw [ho]
    exact hx

end PrimedCounter.Call

end VPVNP
end Computability
end OAI
