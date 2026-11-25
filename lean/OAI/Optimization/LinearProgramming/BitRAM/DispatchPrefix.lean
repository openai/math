import OAI.Optimization.LinearProgramming.BitRAM.Ops
import OAI.Optimization.LinearProgramming.BitRAM.DispatchSource
import OAI.Optimization.LinearProgramming.BitRAM.DispatchLoop

/-! Unique observable boundaries of the frozen bit machine: ordinary instructions
run to completion until a pending request or the actual halt pointer is reached. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace BitRAM
namespace Dispatch
open OracleSpec

inductive Stop (p : BitProgram) where
  | halted (c : p.Config)
  | request (c : p.Config) (next : Fin p.states)

/-- The counter counts ordinary ticks only. The request has been recognized, and its
answer has not been supplied. -/
inductive Prefix (p : BitProgram) : p.Config → ℕ → Stop p → Prop where
  | halted {c} (pc : c.pc=none) : Prefix p c 0 (.halted c)
  | request {c q next} (pc : c.pc=some q)
      (ask : p.instruction q (c.store (p.scan q)).head? = .ask next) :
      Prefix p c 0 (.request c next)
  | next {c q t n stop} (pc : c.pc=some q)
      (ord : ordinaryTarget c (p.instruction q (c.store (p.scan q)).head?) = some t)
      (tail : Prefix p t n stop) : Prefix p c (n+1) stop

/-- The exact accounting when a standard bit-program run is interrupted at its first
request. The queued word and answer are paid once when that request is resumed. -/
def Suffix {p : BitProgram} (o : WordOracle) (n total : ℕ) (d : p.Config) : Stop p → Prop
  | .halted c => c=d ∧ n=total
  | .request c q => ∃ left, n+chargedAsk o c+left=total ∧ p.Run o (answered o c q) left d

private theorem ordinary_or_ask {p : BitProgram} (c : p.Config) (op : Op p) :
    (∃ t, ordinaryTarget c op=some t) ∨ (∃ q, op=.ask q) := by
  cases op <;> simp [ordinaryTarget]

theorem prefix_of_run {p : BitProgram} {o : WordOracle} {c d : p.Config} {time : ℕ}
    (r : p.Run o c time d) (halted : d.pc=none) :
    ∃ n stop, Prefix p c n stop ∧ Suffix o n time d stop := by
  induction r with
  | refl c => exact ⟨0,.halted c,.halted halted,rfl,rfl⟩
  | @step c s d rest elapsed edge tail ih =>
    obtain ⟨q,pc⟩ := tick_running edge
    rcases ordinary_or_ask c (p.instruction q (c.store (p.scan q)).head?) with ⟨t,ht⟩|⟨nxt,ask⟩
    · have act := ordinary_tick o pc ht
      obtain ⟨hk,he⟩ := Prod.mk.inj (Option.some.inj (act.symm.trans edge))
      subst elapsed
      subst s
      obtain ⟨n,stop,pre,post⟩ := ih halted
      refine ⟨n+1,stop,.next pc ht pre,?_⟩
      cases stop with
      | halted d' =>
        obtain ⟨same,count⟩ := post
        exact ⟨same,by omega⟩
      | request c' q' =>
        obtain ⟨left,h,finish⟩ := post
        exact ⟨left,by omega,finish⟩
    · have act := tick_ask (bo := o) pc ask
      obtain ⟨hk,he⟩ := Prod.mk.inj (Option.some.inj (act.symm.trans edge))
      subst elapsed
      subst s
      exact ⟨0,.request c nxt,.request pc ask,rest,by simp,tail⟩

theorem prefix_le_time {p : BitProgram} {o : WordOracle} {n time : ℕ} {d : p.Config}
    {stop : Stop p} (h : Suffix o n time d stop) : n ≤ time := by
  cases stop with
  | halted c => exact Nat.le_of_eq h.2
  | request c q => obtain ⟨left,hr,_⟩ := h; omega

end Dispatch
end BitRAM
end LinearProgramming
end Optimization
end OAI
