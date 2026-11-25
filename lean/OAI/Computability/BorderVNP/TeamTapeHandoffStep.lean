import OAI.Computability.BorderVNP.TeamTapeHandoffCapacity

/-!
# Executable admission of a single team RAM instruction

Before entering an ordinary or private instruction, this control reads the
remaining local and global capacities. On a successful test it performs the
four word-kernel updates in the same register bank. Handoffs and rejections
exit directly from the comparison code with the entire bank untouched.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamTapeHandoff

open VPVNP RAMTape BurstRAM RAMTape.PublicExprMachine

/-- The pre-instruction code has separate guard, clock-update and terminal phases. -/
inductive StepState where
  | guard (q : GuardState)
  | charge (q : chargeCode.State)
  | done (d : Decision)
  deriving Fintype

private def stepPorts : GuardPort → ISA.Port 6 0
  | .remaining => .reg 0
  | .global => .reg 1
  | .burst => .reg 3
  | .tmp => .work 0
  | .out => .work 1

private theorem stepPorts_injective : Function.Injective stepPorts := by
  intro a b h
  cases a <;> cases b <;> first | rfl | contradiction

private def dispatch : GuardState → StepState
  | .done .execute => .charge chargeCode.body.entry
  | .done d => .done d
  | q => .guard q

/-- Branch to the charged instruction, unchanged handoff, or rejected clock overrun.
The row table depends only on the fixed layout and is independent of word width. -/
def stepCode : StackCode (ISA.Port 6 0) StepState
  | .guard q => (guardCode q).rename stepPorts dispatch
  | .charge q => (chargeCode.body.code q).rename id (fun next => next.elim (.done .execute) StepState.charge)
  | .done d => .halt (d != .reject)

/-- The six physical counter words on returning from a successful charge. -/
def chargedRegisters {w : ℕ} (l g elapsed q : Word w) : Fin 6 → Word w :=
  ![packed w (l.val-(1+q.val)), packed w (g.val-(1+q.val)), packed w (elapsed.val+(1+q.val)),
    q, (1 : Word w), packed w (1+q.val)]

/-- Local capacity is tested first. Exactly the execute branch commits new counters,
and the saved data outside these six clock registers are preserved in every case. -/
theorem step_run {w : ℕ} (l g elapsed q : Word w) (persist : Word w) (log : PrivateRAM.WriteLog w) :
    ∃ T ≤ 2*(8*w+2) + 600*(w+1)^2, StackRuns stepCode T (.guard (.scan false (.left true)))
      (ISA.bank Fin.elim0 persist (chargeRegisters l g elapsed q) log) (.done (decision l.val g.val q.val))
      (ISA.bank Fin.elim0 persist (if decision l.val g.val q.val = .execute then chargedRegisters l g elapsed q
        else chargeRegisters l g elapsed q) log) := by
  let s := ISA.bank Fin.elim0 persist (chargeRegisters l g elapsed q) log
  let cost := if l.val ≤ q.val then 8*w+2 else 2*(8*w+2)
  have hb : cost ≤ 2*(8*w+2) := by dsimp [cost]; split <;> omega
  have hguard := (guard_run l g q).lift stepPorts stepPorts_injective dispatch s (target := stepCode) (by
    intro u h
    cases u with
    | scan => rfl
    | done d => simp [guardCode] at h)
  have hi : installStacks stepPorts s (guardBank l g q) = s :=
    installStacks_eq stepPorts_injective _ _ (by intro p; cases p <;> rfl)
  rw [hi] at hguard
  cases hdec : decision l.val g.val q.val with
  | handoff =>
    exact ⟨cost, hb.trans (Nat.le_add_right ..), by simpa only [hdec, dispatch, reduceCtorEq,
      ↓reduceIte] using hguard⟩
  | reject =>
    exact ⟨cost, hb.trans (Nat.le_add_right ..), by simpa only [hdec, dispatch, reduceCtorEq,
      ↓reduceIte] using hguard⟩
  | execute =>
    obtain ⟨t, ht, hcharge⟩ := charge_run l g elapsed q hdec persist log
    let label (u : Option chargeCode.State) : StepState := u.elim (.done .execute) StepState.charge
    have hc := hcharge.lift id Function.injective_id label s (target := stepCode) (by
      intro u hu; cases u with | none => contradiction | some _ => rfl)
    have hid (b : Stacks (ISA.Port 6 0)) : installStacks id s b = b :=
      funext fun p => installStacks_at Function.injective_id s b p
    rw [hid, hid] at hc
    rw [hdec] at hguard
    exact ⟨cost+t, Nat.add_le_add hb ht, by simpa only [label, dispatch, Option.elim_none,
      Option.elim_some, ↓reduceIte, cost, s, chargedRegisters] using hguard.trans hc⟩

end TeamTapeHandoff

end BorderVNP
end Computability
end OAI
