import OAI.Computability.BorderVNP.TeamTapeHandoffFrame
import OAI.Computability.VPVNP.RAMTapeSuccessorCap
import OAI.Computability.VPVNP.RAMTapePublicExprArithmetic
import Mathlib.Tactic.FinCases

/-!
# Physical charge tests and clock updates before a team instruction

An ordinary instruction has burst length zero. A subroutine with burst length
`q` costs `q+1`. Comparing `q` against the two *remaining* capacities avoids
overflow in the guard itself. A local refusal performs neither the subroutine
nor any clock updates. Otherwise exceeding the global cap rejects.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamTapeHandoff

open VPVNP RAMTape BurstRAM TapeWord

/-- Local refusal hands off the unchanged state. Global overrun rejects. -/
inductive Decision where
  | handoff | reject | execute
  deriving DecidableEq

instance : Fintype Decision := derive_fintype% _

/-- Classification with the paper's strict post-instruction overflow rule. -/
def decision (remaining global burst : ℕ) : Decision :=
  if remaining ≤ burst then .handoff else if global ≤ burst then .reject else .execute

/-- A greedy handoff occurs exactly when the next instruction would exceed this processor's block. -/
theorem decision_handoff_iff (remaining global burst : ℕ) :
    decision remaining global burst = .handoff ↔ remaining < 1 + burst := by
  unfold decision
  split_ifs <;> simp_all <;> omega

/-- Both remaining budgets suffice on the execution branch. -/
theorem decision_execute_iff (remaining global burst : ℕ) :
    decision remaining global burst = .execute ↔ 1+burst ≤ remaining ∧ 1+burst ≤ global := by
  unfold decision
  split_ifs <;> simp_all <;> omega

/-- Scratch and read-only operands for the two fixed binary comparison scans. -/
inductive GuardPort where
  | remaining | global | burst | tmp | out
  deriving DecidableEq

instance : Fintype GuardPort := derive_fintype% _

/-- Switch to the global comparison only when the instruction fits locally. -/
inductive GuardState where
  | scan (global : Bool) (q : SuccessorCap.State)
  | done (d : Decision)
  deriving Fintype

private def guardPorts (global : Bool) : ScanPort → GuardPort
  | .left => if global then .global else .remaining
  | .right => .burst
  | .tmp => .tmp
  | .out => .out

private theorem guardPorts_injective (global : Bool) : Function.Injective (guardPorts global) := by
  intro x y h
  cases global <;> cases x <;> cases y <;> simp_all [guardPorts]

private def guardLabel (global : Bool) : SuccessorCap.State → GuardState
  | .done noSpace => if global then .done (if noSpace then .reject else .execute)
    else if noSpace then .done .handoff else .scan true (.left true)
  | q => .scan global q

/-- A single finite table, independent of word width. The comparison loops restore every operand. -/
def guardCode : StackCode GuardPort GuardState
  | .scan b q => (SuccessorCap.code q).rename (guardPorts b) (guardLabel b)
  | .done d => .halt (d != .reject)

/-- Layout of the charged counts on the three read-only input ports. -/
def guardBank {w : ℕ} (remaining global burst : Word w) : Stacks GuardPort
  | .remaining => wordBits remaining
  | .global => wordBits global
  | .burst => wordBits burst
  | .tmp | .out => []

private theorem guardScan {w : ℕ} (b : Bool) (l g q : Word w) :
    StackRuns guardCode (8*w+2) (.scan b (.left true)) (guardBank l g q)
      (guardLabel b (.done (decide ((if b then g.val else l.val) ≤ q.val)))) (guardBank l g q) := by
  have h := SuccessorCap.run_lift (guardPorts b) (guardPorts_injective b) (guardLabel b)
    (target := guardCode) (by intro u hu; cases u <;> first | rfl | simp [SuccessorCap.code] at hu)
    (guardBank l g q) (by cases b <;> simp [guardBank, guardPorts])
    (by rfl) (by rfl)
  cases b <;> simpa [guardLabel, guardBank, guardPorts, value_wordBits] using h

/-- The actual bit scans compute the pre-burst branch. Both scans leave the complete
bank unchanged, so a refused instruction hands off its original state. -/
theorem guard_run {w : ℕ} (l g q : Word w) :
    StackRuns guardCode (if l.val ≤ q.val then 8*w+2 else 2*(8*w+2)) (.scan false (.left true))
      (guardBank l g q) (.done (decision l.val g.val q.val)) (guardBank l g q) := by
  have h := guardScan false l g q
  by_cases hl : l.val ≤ q.val
  · simpa [guardLabel, hl, decision] using h
  · have h' : StackRuns guardCode (8*w+2) (.scan false (.left true)) (guardBank l g q)
        (.scan true (.left true)) (guardBank l g q) := by simpa [guardLabel, hl] using h
    simpa [guardLabel, decision, hl, two_mul] using h'.trans (guardScan true l g q)

open RAMTape.PublicExprMachine

/-- Physical register file for a clock update. Slots zero and one hold remaining local and
global ticks, slot two holds elapsed global ticks, slots three and four are the burst length
and one, and slot five receives the charge. -/
def chargeRegisters {w : ℕ} (l g elapsed q : Word w) : Fin 6 → Word w := ![l,g,elapsed,q,1,0]

/-- Four physical word operations, with an exact unit increment even when the burst is empty. -/
def chargeCode : FiniteRoutine (ISA.Port 6 0) :=
  (((Arithmetic.add.code 5 3 4).followedBy (Arithmetic.sub.code 0 0 5)).followedBy
    (Arithmetic.sub.code 1 1 5)).followedBy (Arithmetic.add.code 2 2 5)

/-- The word updates after a passing guard are mathematical (unwrapped) additions and
subtractions. The outer clock plus remaining global capacity is represented by a word. -/
theorem charge_run {w : ℕ} (l g elapsed q : Word w)
    (pass : decision l.val g.val q.val = .execute)
    (persist : Word w) (log : BurstRAM.PrivateRAM.WriteLog w) :
    ∃ T ≤ 600*(w+1)^2, chargeCode.Runs T
      (ISA.bank Fin.elim0 persist (chargeRegisters l g elapsed q) log)
      (ISA.bank Fin.elim0 persist
        ![packed w (l.val-(1+q.val)), packed w (g.val-(1+q.val)), packed w (elapsed.val+(1+q.val)),
          q, (1 : Word w), packed w (1+q.val)] log) := by
  obtain ⟨hl, hg⟩ := (decision_execute_iff ..).mp pass
  have hcharge : 1+q.val < 2^w := hl.trans_lt l.isLt
  have hunit : (1 : Word w).val = 1 := by
    change 1 % (2^w) = 1
    exact Nat.mod_eq_of_lt (by omega)
  let reg := chargeRegisters l g elapsed q
  let c := packed w (1+q.val)
  have hc : c.val = 1+q.val := packed_val hcharge
  let r₁ := Function.update reg 5 c
  let r₂ := Function.update r₁ 0 (packed w (l.val-(1+q.val)))
  let r₃ := Function.update r₂ 1 (packed w (g.val-(1+q.val)))
  let r₄ := Function.update r₃ 2 (packed w (elapsed.val+(1+q.val)))
  obtain ⟨t₁, h₁, s₁⟩ := Arithmetic.runs Arithmetic.add 5 3 4 Fin.elim0 persist reg log
  have ha : (Arithmetic.add.eval (reg 3).val (reg 4).val) = 1+q.val := by
    change q.val + (1 : Word w).val = _; rw [hunit, Nat.add_comm]
  rw [ha] at s₁
  obtain ⟨t₂, h₂, s₂⟩ := Arithmetic.runs Arithmetic.sub 0 0 5 Fin.elim0 persist r₁ log
  have hb : Arithmetic.sub.eval (r₁ 0).val (r₁ 5).val = l.val - (1+q.val) := by
    simp [r₁, Arithmetic.eval, hc, reg, chargeRegisters]
  rw [hb] at s₂
  obtain ⟨t₃, h₃, s₃⟩ := Arithmetic.runs Arithmetic.sub 1 1 5 Fin.elim0 persist r₂ log
  have hd : Arithmetic.sub.eval (r₂ 1).val (r₂ 5).val = g.val - (1+q.val) := by
    simp [r₂, r₁, Arithmetic.eval, hc, reg, chargeRegisters]
  rw [hd] at s₃
  obtain ⟨t₄, h₄, s₄⟩ := Arithmetic.runs Arithmetic.add 2 2 5 Fin.elim0 persist r₃ log
  have he : Arithmetic.add.eval (r₃ 2).val (r₃ 5).val = elapsed.val + (1+q.val) := by
    simp [r₃, r₂, r₁, Arithmetic.eval, hc, reg, chargeRegisters]
  rw [he] at s₄
  have hfinal : r₄ = ![packed w (l.val-(1+q.val)), packed w (g.val-(1+q.val)),
        packed w (elapsed.val+(1+q.val)), q, (1 : Word w), c] := by
    funext j; fin_cases j <;> rfl
  refine ⟨t₁+t₂+t₃+t₄, by omega, ?_⟩
  rw [← hfinal]
  exact ((s₁.followedBy s₂).followedBy s₃).followedBy s₄

/-- No information is lost in the three updated counter words. -/
theorem charge_values {w : ℕ} (l g elapsed q : Word w)
    (pass : decision l.val g.val q.val = .execute) (safe : elapsed.val+g.val < 2^w) :
    (packed w (l.val-(1+q.val))).val = l.val-(1+q.val) ∧
      (packed w (g.val-(1+q.val))).val = g.val-(1+q.val) ∧
      (packed w (elapsed.val+(1+q.val))).val = elapsed.val+(1+q.val) := by
  obtain ⟨_, hg⟩ := (decision_execute_iff ..).mp pass
  exact ⟨packed_val ((Nat.sub_le ..).trans_lt l.isLt), packed_val ((Nat.sub_le ..).trans_lt g.isLt),
    packed_val (by omega)⟩

end TeamTapeHandoff

end BorderVNP
end Computability
end OAI
