import OAI.Computability.BorderVNP.TeamTapeHandoffStep

/-!
# Starting a time block from the predecessor's elapsed-tick word

The cumulative clock is checked against the team's public limit before the
global countdown is initialized. The local countdown is the new processor's
full block. A halted predecessor is propagated without executing an instruction,
and the last processor requires the canonical accepting status.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamTapeHandoff

open VPVNP RAMTape BurstRAM TapeWord RAMTape.PublicExprMachine

/-- Terminal status bit test on the final processor. It reads the first physical
bit of the canonical outgoing register frame. -/
inductive EndState where
  | read | done (accept : Bool)
  deriving Fintype

/-- Inspect the final status tag, rejecting a missing bit or a live register state. -/
def endCode : StackCode Unit EndState
  | .read => .pop () fun b => .done (b.getD false)
  | .done accept => .halt accept

/-- Last-processor acceptance reads the halt bit and leaves the payload unmodified. -/
theorem end_run {w k : ℕ} (f : Frame w k) (suffix : List Bool) :
    StackRuns endCode 1 .read (fun _ => f.bits ++ suffix) (.done f.halted)
      (fun _ => f.words.flatMap wordBits ++ suffix) := by
  refine .cons (.pop (k := ()) (f := fun b => .done (b.getD false)) rfl) ?_
  have he : Function.update (fun _ : Unit => f.bits ++ suffix) () (f.bits ++ suffix).tail =
      fun _ => f.words.flatMap wordBits ++ suffix := by funext u; cases u; rfl
  rw [he]
  exact .nil ..

/-- Startup register bank. The limit in slot one will be replaced by the available
global countdown; slots zero and two already hold the new full block and incoming time. -/
def startupRegisters {w : ℕ} (H limit elapsed q : Word w) : Fin 6 → Word w :=
  chargeRegisters H limit elapsed q

private def startupPorts : ScanPort → ISA.Port 6 0
  | .left => .reg 2
  | .right => .reg 1
  | .tmp => .work 0
  | .out => .work 1

private theorem startupPorts_injective : Function.Injective startupPorts := by
  intro i j h
  cases i <;> cases j <;> first | rfl | contradiction

private abbrev subtractElapsed : FiniteRoutine (ISA.Port 6 0) := Arithmetic.sub.code 1 1 2

/-- Read the clock comparison and prepare the global countdown only on a valid incoming time. -/
inductive StartupState where
  | scan (q : SuccessorCap.State)
  | subtract (q : subtractElapsed.State)
  | done (ok : Bool)
  deriving Fintype

private def startupDispatch : SuccessorCap.State → StartupState
  | .done valid => if valid then .subtract subtractElapsed.body.entry else .done false
  | q => .scan q

/-- Finite startup controller shared by all word widths and all processor numbers. -/
def startupCode : StackCode (ISA.Port 6 0) StartupState
  | .scan q => (SuccessorCap.code q).rename startupPorts startupDispatch
  | .subtract q => (subtractElapsed.body.code q).rename id
      (fun next => next.elim (.done true) StartupState.subtract)
  | .done ok => .halt ok

/-- An over-budget predecessor is rejected with all its register words intact. Otherwise
the genuine word subtractor replaces the cap with `limit-elapsed`, preserving the incoming
clock and the new full local block. -/
theorem startup_run {w : ℕ} (H limit elapsed q persist : Word w) (log : PrivateRAM.WriteLog w) :
    ∃ T ≤ 8*w+2 + 150*(w+1)^2, StackRuns startupCode T (.scan (.left true))
      (ISA.bank Fin.elim0 persist (startupRegisters H limit elapsed q) log)
      (.done (decide (elapsed ≤ limit)))
      (ISA.bank Fin.elim0 persist (if elapsed ≤ limit
        then chargeRegisters H (packed w (limit.val-elapsed.val)) elapsed q
        else startupRegisters H limit elapsed q) log) := by
  let reg := startupRegisters H limit elapsed q
  let s := ISA.bank Fin.elim0 persist reg log
  have scan := SuccessorCap.run_lift startupPorts startupPorts_injective startupDispatch
    (target := startupCode) (by intro u hu; cases u <;> first | rfl | simp [SuccessorCap.code] at hu)
    s (by change (wordBits elapsed).length = (wordBits limit).length; simp) rfl rfl
  change StackRuns startupCode (8 * (wordBits elapsed).length + 2) (.scan (.left true)) s
    (startupDispatch (.done (decide (value (wordBits elapsed) ≤ value (wordBits limit))))) s at scan
  simp only [length_wordBits, value_wordBits] at scan
  by_cases hv : elapsed ≤ limit
  · obtain ⟨t, ht, r⟩ := Arithmetic.runs Arithmetic.sub (1 : Fin 6) 1 2 Fin.elim0 persist reg log
    let label (u : Option subtractElapsed.State) : StartupState := u.elim (.done true) StartupState.subtract
    have hc := r.lift id Function.injective_id label s (target := startupCode) (by
      intro u hu; cases u with | none => contradiction | some _ => rfl)
    have hid (b : Stacks (ISA.Port 6 0)) : installStacks id s b = b :=
      funext fun p => installStacks_at Function.injective_id s b p
    rw [hid, hid] at hc
    have he : Function.update reg 1 (packed w (Arithmetic.sub.eval (reg 1).val (reg 2).val)) =
        chargeRegisters H (packed w (limit.val-elapsed.val)) elapsed q := by
      funext i; fin_cases i <;> rfl
    have hv' : elapsed.val ≤ limit.val := hv
    simp only [hv', decide_true, startupDispatch, ↓reduceIte] at scan
    exact ⟨8*w+2+t, Nat.add_le_add_left ht _, by
      simpa only [he, hv, decide_true, ↓reduceIte, label, Option.elim_none, Option.elim_some,
        s, reg] using scan.trans hc⟩
  · have hv' : ¬elapsed.val ≤ limit.val := hv
    exact ⟨8*w+2, Nat.le_add_right .., by simpa [startupDispatch, hv, hv', s, reg] using scan⟩

end TeamTapeHandoff

end BorderVNP
end Computability
end OAI
