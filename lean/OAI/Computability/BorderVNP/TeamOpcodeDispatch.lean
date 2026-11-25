import OAI.Computability.BorderVNP.TeamOpcode
import OAI.Computability.VPVNP.RAMTapeSuccessorEnds

/-! # Physical word instructions in a signed RAM block

The fixed control dispatches each native arithmetic instruction on bit stacks. Division and
remainder first scan and restore the *original* divisor, including when it is also the output
register. Binary guesses, shared-memory loads/stores and private calls reach distinct typed
exits. No instruction consults shared memory during this preparation.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamOpcode.Dispatch

open VPVNP.RAMTape VPVNP.BurstRAM VPVNP.BurstRAM.PrivateRAM

variable {p r k m w : ℕ}

/-- Control states for the ordinary dispatcher, the divisor check and its typed exits. -/
inductive Label (P : Program p r k m) where
  | enter (pc : Fin p)
  | preflight (pc : Fin p) (operand : Fin r) (q : SuccessorEnds.State)
  | select (idReg address length : Fin r) (next : Fin p) (q : TeamOpcodeSelect.State m)
  | isa (q : ISA.State P.base)
  | exit (out : Exit p r m)
  deriving Fintype

/-- The arithmetic preparation table, independent of the runtime word width. -/
def rows (P : Program p r k m) : StackCode (ISA.Port r k) (Label P)
  | .enter pc => match P.tag pc with
    | .sign b next => .goto (.exit (.sign b next))
    | .call j a l next => .goto (.exit (.call j a l next))
    | .callReg idReg a l next => .goto (.select idReg a l next .enter)
    | .native => let i := P.base.code pc
                 if permitted i then match divisor i with
                   | some y => .goto (.preflight pc y (.read false false))
                   | none => .goto (.isa (ISA.entry P.base pc))
                 else .goto (.exit (.native .reject))
  | .preflight pc _ (.done _ nz) =>
    .goto (if nz then .isa (ISA.entry P.base pc) else .exit (.native .reject))
  | .preflight pc operand q =>
    (SuccessorEnds.code (.reg operand) (.work 15) q).rename id (Label.preflight pc operand)
  | .select _ a l next (.done j) => .goto (.exit (selectedExit j a l next))
  | .select idReg a l next q => (TeamOpcodeSelect.code m idReg q).rename id (Label.select idReg a l next)
  | .isa q => match ISA.resume? P.base q with
    | none => (ISA.code P.base q).rename id Label.isa
    | some cb => .goto (.exit (.native cb))
  | .exit _ => .halt true

private theorem install_id {K : Type*} (base small : Stacks K) : installStacks id base small = small := by
  funext i; exact installStacks_at Function.injective_id ..

private theorem native_run (P : Program p r k m) (pub : Fin k → Word w) (s : State w p r) :
    let i := P.base.code s.pc
    let cb := ISA.exitFor i ((ISA.jumpTest i s.logged).getD false)
    ∃ t ≤ 100*(w+1)^2 + 3, StackRuns (rows P) t (.isa (ISA.entry P.base s.pc))
      (ISA.configBank pub s.logged) (.exit (.native cb)) (ISA.configBank pub (ISA.post i pub s.logged)) := by
  intro i cb
  obtain ⟨t, ht, run⟩ := ISA.dispatch_step P.base pub s.logged
  have hc (q) (h : (ISA.code P.base q).returns = false) :
      rows P (.isa q) = (ISA.code P.base q).rename id Label.isa := by
    simp only [rows, ISA.resume_none_of_continuing _ _ h]
  have lifted := run.lift id Function.injective_id Label.isa (ISA.configBank pub s.logged) hc
  simp only [install_id] at lifted
  let b := ISA.configBank pub (ISA.post i pub s.logged)
  have last : StackRuns (rows P) 1 (.isa (ISA.callback P.base cb)) b (.exit (.native cb)) b :=
    .cons (.goto (by simp [rows])) (.nil ..)
  change t ≤ 100*(w+1)^2*(0+1)+2 at ht
  exact ⟨t+1, by omega, lifted.trans last⟩

private theorem preflight_run (P : Program p r k m) (pub : Fin k → Word w) (s : State w p r) (y : Fin r) :
    let z := s.reg y
    let endLabel : Label P := if z ≠ 0 then .isa (ISA.entry P.base s.pc) else .exit (.native .reject)
    StackRuns (rows P) (4*w+3) (.preflight s.pc y (.read false false)) (ISA.configBank pub s.logged)
      endLabel (ISA.configBank pub s.logged) := by
  intro z endLabel
  let bank := ISA.configBank pub s.logged
  let scanner := SuccessorEnds.code (ISA.Port.reg y : ISA.Port r k) (.work 15)
  have hc (q) (h : (scanner q).returns = false) :
      rows P (.preflight s.pc y q) = (scanner q).rename id (Label.preflight s.pc y) := by
    cases q <;> first | rfl | contradiction
  have hr := SuccessorEnds.word_run (ISA.Port.reg y) (.work 15) (by intro h; cases h) bank z rfl rfl
  have lift := hr.lift id Function.injective_id (Label.preflight s.pc y) bank hc
  simp only [install_id] at lift
  have hz : decide (0 < z.val) = decide (z ≠ 0) := by simp [Fin.pos_iff_ne_zero]
  have tail : StackRuns (rows P) 1 (.preflight s.pc y (.done (decide (z.val+1 < 2^w)) (decide (0<z.val))))
      bank endLabel bank := by
    refine .cons (.goto ?_) (.nil ..)
    simp only [rows, hz, decide_eq_true_eq, endLabel]
  exact lift.trans tail

/-- The actual named-stack table produces the native instruction's signed/probe/call exit
and the correct post-instruction register bank in a quadratic number of elementary steps. -/
theorem step (P : Program p r k m) (pub : Fin k → Word w) (s : State w p r) :
    let prepared := prepare P pub s
    ∃ t ≤ 110*(w+1)^2, StackRuns (rows P) t (.enter s.pc) (ISA.configBank pub s.logged)
      (.exit prepared.1) (ISA.configBank pub prepared.2) := by
  intro result
  have spare : 4*w + 7 ≤ 10*(w+1)^2 := by nlinarith [Nat.zero_le (w*w)]
  have cap : 1 ≤ 110*(w+1)^2 := by nlinarith
  cases tag : P.tag s.pc with
  | sign b pc =>
    simp only [result, prepare, tag]
    exact ⟨1, cap, .cons (.goto (by simp [rows, tag])) (.nil ..)⟩
  | call j a l pc =>
    simp only [result, prepare, tag]
    exact ⟨1, cap, .cons (.goto (by simp [rows, tag])) (.nil ..)⟩
  | callReg idReg addr len pc =>
    let bank := ISA.configBank pub s.logged
    let j := TeamOpcodeSelect.select m (s.reg idReg).val
    have run := TeamOpcodeSelect.run_linked m idReg bank (s.reg idReg) rfl rfl
      (rows P) (Label.select idReg addr len pc) (by
        intro q hc; cases q <;> first | rfl | simp [TeamOpcodeSelect.code] at hc)
    have first : StackRuns (rows P) 1 (.enter s.pc) bank (.select idReg addr len pc .enter) bank :=
      .cons (.goto (by simp [rows,tag])) (.nil ..)
    have last : StackRuns (rows P) 1 (.select idReg addr len pc (.done j)) bank (.exit (selectedExit j addr len pc)) bank :=
      .cons (.goto rfl) (.nil ..)
    exact ⟨1+(4*w+6)+1,by nlinarith [Nat.zero_le (w*w)],by simpa only [result,prepare,tag] using (first.trans run).trans last⟩
  | native =>
    let i := P.base.code s.pc
    by_cases allow : permitted i = true
    · cases hd : divisor i with
      | none =>
        have hg : enabled i s = true := by simp [enabled, allow, hd]
        obtain ⟨t, ht, run⟩ := native_run P pub s
        refine ⟨t+1, by nlinarith, .cons (.goto (q' := .isa (ISA.entry P.base s.pc)) ?_) ?_⟩
        · simp only [rows, tag, ← show i = P.base.code s.pc from rfl, allow, ↓reduceIte, hd]
        · simpa only [result, prepare, tag, ← show i = P.base.code s.pc from rfl, hg, ↓reduceIte] using run
      | some y =>
        have pre := preflight_run P pub s y
        dsimp only at pre
        have hg : enabled i s = decide (s.reg y ≠ 0) := by simp [enabled, allow, hd]
        by_cases nz : s.reg y ≠ 0
        · obtain ⟨t, ht, run⟩ := native_run P pub s
          refine ⟨(4*w+3+t)+1, by nlinarith, .cons (.goto (q' := .preflight s.pc y (.read false false)) ?_) ?_⟩
          · simp only [rows, tag, ← show i = P.base.code s.pc from rfl, allow, ↓reduceIte, hd]
          · rw [ite_eq_left nz] at pre
            have valid : enabled i s = true := hg.trans (decide_eq_true nz)
            simpa only [result, prepare, tag, ← show i = P.base.code s.pc from rfl, valid, ↓reduceIte] using pre.trans run
        · refine ⟨4*w+3+1, by nlinarith, .cons (.goto (q' := .preflight s.pc y (.read false false)) ?_) ?_⟩
          · simp only [rows, tag, ← show i = P.base.code s.pc from rfl, allow, ↓reduceIte, hd]
          · simpa only [result, prepare, tag, ← show i = P.base.code s.pc from rfl, hg, nz, decide_false,
              Bool.false_eq_true, ↓reduceIte] using pre
    · have dis : permitted i = false := Bool.eq_false_iff.mpr allow
      have hg : enabled i s = false := by simp [enabled, dis]
      refine ⟨1, cap, .cons (.goto (q' := .exit (.native .reject)) ?_) ?_⟩
      · simp only [rows, tag]; change (if permitted i then _ else _) = _; simp [dis]
      · simp only [result, prepare, tag, ← show i = P.base.code s.pc from rfl, hg, Bool.false_eq_true, ↓reduceIte]
        exact .nil ..

end TeamOpcode.Dispatch

end BorderVNP
end Computability
end OAI
