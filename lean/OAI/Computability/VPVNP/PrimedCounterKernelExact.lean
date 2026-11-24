import OAI.Computability.VPVNP.PrimedCounterCallPaths
import OAI.Computability.VPVNP.PrimedStackRAMNodeRun

/-!
# Observing a bounded kernel through its compiled flow

The standalone accept continuation observes the event log and exact use of the choice tape.
Returning a designated register observes its final value. External memory is recovered by
replaying the same log, provided the kernel records its writes faithfully.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PrimedStackRAM

open BurstRAM BurstRAM.PrivateRAM PrimedInputRAM PrimedCounter

variable {w r k budget : ℕ} {a : Flow r k} {f : Kernel w r k}
  {pub : Fin k → Word w} {st : Word w} {rs : Regs w r} {m : Memory w}

/-- A kernel records the actual external-memory effect of each successful run. -/
def Replays (f : Kernel w r k) : Prop :=
  ∀ {pub st rs m bits o}, f pub st rs m bits = some o → after m o.events = o.mem

private theorem exit_run (result : Option (Fin r)) (pub : Fin k → Word w) (st : Word w)
    (rs : Regs w r) (m : Memory w) (bits : List Bool) (fuel : ℕ) :
    execute ((a.template result).instantiate w pub).program (fuel+1)
        ⟨a.exitPC,st,rs,fun _ => 0⟩ m bits =
      if bits = [] then some ⟨[], result.map rs⟩ else none := by
  cases result <;> cases bits <;>
    simp [execute, Machine.program, Template.instantiate, Flow.template_exit, Instr.resize, Instr.run]

private theorem Refines.return_run (h : Refines a budget f) (result : Option (Fin r))
    (pub : Fin k → Word w) (st : Word w) (rs : Regs w r) (m : Memory w)
    (bits : List Bool) (fuel : ℕ) (hf : budget < fuel) :
    BurstRAM.execute ((a.template result).instantiate w pub).program fuel ⟨a.pc a.entry,st,rs,fun _ => 0⟩ m bits =
      (f pub st rs m bits).bind fun o =>
        if o.bits = [] then some ⟨o.events, result.map o.regs⟩ else none := by
  let M := (a.template result).instantiate w pub
  have hb : M.code a.rejectPC = .reject := by
    simp [M, Template.instantiate, Flow.template_reject, Instr.resize]
  have hr := h.execute (Flow.template_linked a result pub) hb st rs (fun _ => 0) m bits fuel hf.le
  rw [hr]
  change (f pub st rs m bits).bind _ = _
  cases hs : f pub st rs m bits with
  | none => rfl
  | some o =>
    have hn := h.bounded hs
    obtain ⟨n, hn⟩ : ∃ n, fuel - o.events.length = n + 1 := ⟨fuel-o.events.length-1, by omega⟩
    simp only [Option.bind_some, hn, exit_run]
    split <;> simp_all
    change (⟨o.events ++ [], _⟩ : Report w) = _
    simp

/-- On a finite derivation's exact tape, a bounded refining kernel succeeds and returns
the same events, registers and external memory. -/
theorem Refines.kernel_of_exec (h : Refines a budget f) (replay : Replays f)
    {es : List (Event w)} {rs' : Regs w r} {m' : Memory w} (he : Flow.Exec pub st a rs m es rs' m') :
    f pub st rs m (choiceBits es) = some ⟨es, rs', m', []⟩ := by
  let fuel := budget + es.length + 1
  have run (result : Option (Fin r)) :
      ((f pub st rs m (choiceBits es)).bind fun o =>
        if o.bits = [] then some (⟨o.events, result.map o.regs⟩ : Report w) else none) =
        some ⟨es,result.map rs'⟩ := by
    rw [← h.return_run result pub st rs m _ fuel (by dsimp [fuel]; omega)]
    exact (Flow.template_execute_iff a result pub st (fun _ => 0) rs m fuel _ _).mpr
      ⟨rs', m', he, rfl, by dsimp [fuel]; omega, rfl⟩
  have h₀ := run none
  cases hx : f pub st rs m (choiceBits es) with
  | none => simp [hx] at h₀
  | some x =>
    have hb : x.bits = [] := by
      by_contra hn
      simp [hx, hn] at h₀
    have hes : x.events = es := by simpa [hx, hb] using h₀
    have hrs : x.regs = rs' := by
      funext i
      have hi := run (some i)
      simpa [hx, hb, hes] using hi
    have hm : x.mem = m' := (replay hx).symm.trans (hes ▸ Call.exec_memory he)
    cases x
    congr

/-- Exact-use characterization, including rejected tapes. -/
theorem Refines.kernel_iff_exec (h : Refines a budget f) (replay : Replays f)
    (bits : List Bool) (es : List (Event w)) (rs' : Regs w r) (m' : Memory w) :
    f pub st rs m bits = some ⟨es, rs', m', []⟩ ↔
      Flow.Exec pub st a rs m es rs' m' ∧ bits = choiceBits es := by
  constructor
  · intro hx
    have hr := h.return_run none pub st rs m bits (budget+1) (by omega)
    simp only [hx, Option.bind_some, ite_true, Option.map_none] at hr
    obtain ⟨r₁, m₁, he, _, _, hbits⟩ :=
      (Flow.template_execute_iff a none pub st (fun _ => 0) rs m (budget+1) bits _).mp hr
    change choiceBits es = bits at hbits
    have hs := h.kernel_of_exec replay he
    change f pub st rs m (choiceBits es) = some _ at hs
    rw [hbits, hx] at hs
    cases Option.some.inj hs
    exact ⟨he, hbits.symm⟩
  · rintro ⟨he,rfl⟩
    exact h.kernel_of_exec replay he

end PrimedStackRAM

end VPVNP
end Computability
end OAI
