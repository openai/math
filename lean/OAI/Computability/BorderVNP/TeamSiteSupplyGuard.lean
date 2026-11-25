import OAI.Computability.BorderVNP.TeamSiteEvents
import OAI.Computability.BorderVNP.TeamSiteChunk

/-! # Terminal and callback cases of the processor guard

The pre-instruction countdown examines the same burst length used by the
prepared opcode. After it has admitted that opcode, every bounded native
private routine has a branch on every supply. The only rejecting callbacks
are a native rejection or a private interval exceeding the word address space.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamSite.SupplyRun

open VPVNP RAMTape BurstRAM TeamSiteEvents TeamSiteChoices TeamTapeHandoff

variable {Q Γ : Type} {w p r k a m g : ℕ}

/-- Typed exit produced by the real processor's pre-instruction guard. -/
abbrev exit (P : TeamOpcode.Program p r k a) (pub : Fin k → Word w)
    (s : TeamOpcode.State w p r) (c : Window w) :=
  (TeamLocalClock.Loop.result P pub s c.block c.global c.elapsed c.cap).1

/-- Decode the event belonging to the prepared callback. -/
noncomputable def decode (P : TeamOpcode.Program p r k a) (pub : Fin k → Word w)
    (lib : Fin a → Macro Q Γ m g) (fuel : ℕ) (s : TeamOpcode.State w p r)
    (c : Window w) (supply : Supply) :=
  let prep := TeamOpcode.prepare P pub s
  generate lib fuel c.cap.val prep.2 prep.1 supply

/-- Whenever dispatch selects an actual private callback, the pre-instruction
guard charged exactly the length in that callback's live register bank. -/
theorem preparedBurst (P : TeamOpcode.Program p r k a) (pub : Fin k → Word w)
    (s : TeamOpcode.State w p r) {j : Fin a} {addr len : Fin r} {next : Fin p}
    (out : (TeamOpcode.prepare P pub s).1 = .call j addr len next) :
    (TeamOpcode.prepare P pub s).2.reg len = opcodeBurst P s := by
  cases tag : P.tag s.pc with
  | sign => simp [TeamOpcode.prepare,tag] at out
  | native =>
    by_cases ok : TeamOpcode.enabled (P.base.code s.pc) s = true <;> simp [TeamOpcode.prepare,tag,ok] at out
  | call i ad le pc =>
    simp only [TeamOpcode.prepare,tag,TeamOpcode.Exit.call.injEq] at out
    rcases out with ⟨rfl,rfl,rfl,rfl⟩
    simp [TeamOpcode.prepare,tag,opcodeBurst,TeamOpcode.State.logged]
  | callReg idReg ad le pc =>
    cases hs : TeamOpcodeSelect.select a (s.reg idReg).val with
    | none => simp [TeamOpcode.prepare,tag,hs,TeamOpcode.selectedExit] at out
    | some i =>
      simp only [TeamOpcode.prepare,tag,hs,TeamOpcode.selectedExit,Option.elim_some,
        TeamOpcode.Exit.call.injEq] at out
      rcases out with ⟨rfl,rfl,rfl,rfl⟩
      simp [TeamOpcode.prepare,tag,opcodeBurst,TeamOpcode.State.logged]

/-- The pre-instruction guard and the prepared opcode read the same burst length. -/
theorem kind_burst (P : TeamOpcode.Program p r k a) (s : TeamOpcode.State w p r) :
    (match TeamLocalClock.Loop.kind P s.pc with
      | .burst len => s.reg len
      | _ => 0) = opcodeBurst P s := by
  cases tag : P.tag s.pc with
  | sign | call | callReg => simp [TeamLocalClock.Loop.kind, tag, opcodeBurst]
  | native => cases h : P.base.code s.pc <;> simp [TeamLocalClock.Loop.kind,tag,h,opcodeBurst]

private theorem guarded_callback (P : TeamOpcode.Program p r k a) (pub : Fin k → Word w)
    (s : TeamOpcode.State w p r) (c : Window w) (q : Word w) (out : TeamOpcode.Exit p r a) :
    (TeamLocalClock.Loop.afterGuard P pub s c.block c.global c.elapsed q c.cap).1 = .callback out ↔
      out = (TeamOpcode.prepare P pub s).1 ∧ c.Fits q.val := by
  rw [show c.Fits q.val ↔ decision c.block.val c.global.val q.val = .execute from (decision_execute_iff ..).symm]
  cases h : decision c.block.val c.global.val q.val <;> simp [TeamLocalClock.Loop.afterGuard,h,eq_comm]

/-- A callback can only appear after executing its entire local and global charge.
Its prepared exit and read limit match the live table and its source registers. -/
theorem callback_info (P : TeamOpcode.Program p r k a) (pub : Fin k → Word w)
    (s : TeamOpcode.State w p r) (c : Window w) (out : TeamOpcode.Exit p r a)
    (h : exit P pub s c = .callback out) :
    out = (TeamOpcode.prepare P pub s).1 ∧ c.Fits (opcodeBurst P s).val ∧ (opcodeBurst P s).val ≤ c.cap.val := by
  have eq := kind_burst P s
  cases hk : TeamLocalClock.Loop.kind P s.pc with
  | accept | reject => simp [exit, TeamLocalClock.Loop.result,hk] at h
  | ordinary =>
    simp only [hk] at eq
    rw [← eq]
    have hd := (guarded_callback P pub s c 0 out).mp (by simpa only [exit, TeamLocalClock.Loop.result,hk] using h)
    exact ⟨hd.1,hd.2,Nat.zero_le _⟩
  | burst len =>
    simp only [hk] at eq
    by_cases hc : s.reg len ≤ c.cap
    · have hd := (guarded_callback P pub s c (s.reg len) out).mp (by
        simpa only [exit, TeamLocalClock.Loop.result,hk,hc,↓reduceIte] using h)
      rw [← eq]
      exact ⟨hd.1,hd.2,hc⟩
    · simp [exit, TeamLocalClock.Loop.result,hk,hc] at h

/-- Handoff occurs before any instruction update and keeps the actual fetched PC. -/
theorem handoff_pc (P : TeamOpcode.Program p r k a) (pub : Fin k → Word w)
    (s : TeamOpcode.State w p r) (c : Window w) (pc : Fin p) (h : exit P pub s c = .handoff pc) : pc = s.pc := by
  cases hk : TeamLocalClock.Loop.kind P s.pc with
  | accept | reject => simp [exit,TeamLocalClock.Loop.result,hk] at h
  | ordinary =>
    cases hd : decision c.block.val c.global.val 0 <;>
      simp [exit,TeamLocalClock.Loop.result,hk,TeamLocalClock.Loop.afterGuard,hd] at h
    exact h.symm
  | burst len =>
    by_cases hc : s.reg len ≤ c.cap
    · cases hd : decision c.block.val c.global.val (s.reg len).val <;>
        simp [exit,TeamLocalClock.Loop.result,hk,hc,TeamLocalClock.Loop.afterGuard,hd] at h
      exact h.symm
    · simp [exit,TeamLocalClock.Loop.result,hk,hc] at h

/-- Failure of a prepared callback before taking any physical choices. -/
inductive Invalid (bank : PrivateRAM.LogConfig w p r) : TeamOpcode.Exit p r a → Prop
  | nativeReject : Invalid bank (.native .reject)
  | nativeReturn (src : Fin r) : Invalid bank (.native (.returnState src))
  | badAddress (j : Fin a) (addr len : Fin r) (pc : Fin p)
      (overflow : 2^w < (bank.reg addr).val + (bank.reg len).val) :
      Invalid bank (.call j addr len pc)

/-- A missing event at a real admitted callback has a concrete local rejection cause.
Private timeout is ruled out by the native path clock for every legal input burst. -/
theorem invalid_of_none (P : TeamOpcode.Program p r k a) (pub : Fin k → Word w)
    (lib : Fin a → Macro Q Γ m g) (fuel : ℕ) (s : TeamOpcode.State w p r)
    (c : Window w) (supply : Supply) (admit : exit P pub s c = .callback (TeamOpcode.prepare P pub s).1)
    (hg : decode P pub lib fuel s c supply = none)
    (bounded : ∀ j vs, vs.length ≤ c.cap.val → (lib j).bounded fuel (vs : List (Word w))) :
    Invalid (TeamOpcode.prepare P pub s).2 (TeamOpcode.prepare P pub s).1 := by
  let b := (TeamOpcode.prepare P pub s).2
  have cap := (callback_info P pub s c _ admit).2.2
  have no : ¬ ∃ act, ((TeamOpcode.prepare P pub s).1.action (macros lib fuel) b).action = some act ∧
      act.extra ≤ c.cap.val := by
    intro ok
    have yes := (generate_isSome_iff lib fuel c.cap.val b _ supply bounded).mpr ok
    change (decode P pub lib fuel s c supply).isSome at yes
    simp [hg] at yes
  cases h : (TeamOpcode.prepare P pub s).1 with
  | sign => simp [h,TeamOpcode.Exit.action,TeamRAM.Instr.action,TeamTranscript.Action.extra] at no
  | native cb =>
    cases cb with
    | next | choose | read | write => simp [h, TeamOpcode.Exit.action, TeamOpcode.nativeAction, ISA.Callback.action,
        TeamRAM.Instr.action,TeamTranscript.Action.extra] at no
    | reject => exact .nativeReject
    | returnState src => exact .nativeReturn src
    | accept =>
      have terminal : P.fetch pub (macros lib fuel) s = .accept := by
        rw [← TeamOpcode.prepare_action,h]; rfl
      have hk := (accept_iff ..).mp terminal
      simp [exit,TeamLocalClock.Loop.result,hk] at admit
  | call j addr len pc =>
    have lim : (b.reg len).val ≤ c.cap.val := by
      rw [show b.reg len = opcodeBurst P s from preparedBurst P pub s h]; exact cap
    apply Invalid.badAddress
    by_contra! ok
    apply no
    rw [h]
    refine ⟨.burst (b.reg addr).val (b.reg len).val, ?_,lim⟩
    change (if (b.reg addr).val + (b.reg len).val ≤ 2^w then some _ else none) = some _
    exact ite_eq_left ok

end TeamSite.SupplyRun

end BorderVNP
end Computability
end OAI
