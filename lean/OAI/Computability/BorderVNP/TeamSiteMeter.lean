import OAI.Computability.BorderVNP.TeamSiteLoop

/-! # Physical clock admission for actual adaptive RAM events

The extra cost is read from the pre-instruction architectural state. When a
native instruction supplies a valid action, its logical burst is exactly the
clock operand. Both countdowns and the cumulative tick have their integer values
without wraparound after a successful physical charge.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamSite

open VPVNP RAMTape BurstRAM TeamTapeHandoff RAMTape.PublicExprMachine

variable {w p r k a : ℕ}

/-- The processor's remaining block, remaining global ticks, elapsed ticks and burst cap. -/
structure Window (w : ℕ) where
  /-- Ticks still available at this processor. -/
  block : Word w
  /-- Ticks still available globally. -/
  global : Word w
  /-- Time of the last logical instruction. -/
  elapsed : Word w
  /-- Maximum private burst length. -/
  cap : Word w

/-- The current cumulative logical cap fits the timestamp word. -/
def Window.Safe (c : Window w) : Prop := c.elapsed.val+c.global.val < 2^w

/-- The current instruction and all its probes fit both countdowns. -/
def Window.Fits (c : Window w) (q : ℕ) : Prop := 1+q ≤ c.block.val ∧ 1+q ≤ c.global.val

/-- Update the countdowns and timestamp after an entire admitted instruction. -/
def Window.charge (c : Window w) (q : ℕ) : Window w :=
  ⟨packed w (c.block.val-(1+q)), packed w (c.global.val-(1+q)), packed w (c.elapsed.val+(1+q)), c.cap⟩

/-- Exact integer values of the physically stored words after an admitted charge. -/
theorem Window.charged_values (c : Window w) (q : ℕ) (safe : c.Safe) (fits : c.Fits q) :
    (c.charge q).block.val = c.block.val-(1+q) ∧
    (c.charge q).global.val = c.global.val-(1+q) ∧
    (c.charge q).elapsed.val = c.elapsed.val+(1+q) ∧ (c.charge q).Safe := by
  obtain ⟨hb,hg⟩ := fits
  change c.elapsed.val+c.global.val < 2^w at safe
  have b := c.block.isLt
  have t : c.elapsed.val+(1+q) < 2^w := by omega
  simp only [charge, Safe, packed, Fin.val_ofNat, Nat.mod_eq_of_lt (by omega : c.block.val-(1+q) < 2^w),
    Nat.mod_eq_of_lt (by omega : c.global.val-(1+q) < 2^w), Nat.mod_eq_of_lt t, true_and]
  omega

/-- The first timestamp of a successful ordinary or private call. -/
def Window.first (c : Window w) : Word w := packed w (c.elapsed.val+1)

/-- The first probe timestamp fits even for a burst using the last available ticks. -/
theorem Window.first_val (c : Window w) {q : ℕ} (safe : c.Safe) (fits : c.Fits q) :
    c.first.val = c.elapsed.val+1 := by
  obtain ⟨_,hg⟩ := fits
  change c.elapsed.val+c.global.val < 2^w at safe
  exact Nat.mod_eq_of_lt (by omega)

/-- The actual clock and register bank between instructions. -/
def Window.bank (c : Window w) (pub : Fin k → Word w) (s : TeamOpcode.State w p r) :=
  TeamLocalClock.bank pub s c.block c.global c.elapsed c.cap

/-- The staged register, clock and timestamp bank during a typed callback. -/
def Window.callbackBank (c : Window w) (pub : Fin k → Word w) (reg : Fin r → Word w)
    (tick : Word w) : Stacks (TeamLocalClock.Port r k) :=
  TeamLocalClock.banks pub (p := 1) ⟨0,0,reg,[]⟩ (chargeRegisters c.block c.global c.elapsed 0)
    c.cap (wordBits tick)

/-- The extra charge read before the instruction alters any register. -/
def opcodeBurst (P : TeamOpcode.Program p r k a) (s : TeamOpcode.State w p r) : Word w :=
  match P.tag s.pc with
  | .call _ _ len _ | .callReg _ _ len _ => s.reg len
  | _ => 0

private theorem native_extra {cb : ISA.Callback p r} (s : PrivateRAM.LogConfig w p r)
    {act : TeamTranscript.Action (Word w)}
    (h : (TeamOpcode.nativeAction (cb.action s)).action = some act) : act.extra = 0 := by
  cases cb <;> simp only [ISA.Callback.action, TeamOpcode.nativeAction, TeamRAM.Instr.action,
    Option.some.injEq, reduceCtorEq] at h <;> subst_vars <;> rfl

/-- Each successful action charges the same burst length in the finite ISA and the
abstract native RAM, including zero-length private calls. -/
theorem opcodeBurst_eq (P : TeamOpcode.Program p r k a) (pub : Fin k → Word w)
    (lib : TeamOpcode.Macros w a) (s : TeamOpcode.State w p r) (act : TeamTranscript.Action (Word w))
    (ha : (P.fetch pub lib s).action = some act) : (opcodeBurst P s).val = act.extra := by
  rw [← TeamOpcode.prepare_action] at ha
  cases tag : P.tag s.pc with
  | sign b next =>
    simp only [TeamOpcode.prepare, tag, TeamOpcode.Exit.action, TeamRAM.Instr.action, Option.some.injEq] at ha
    subst act; simp [opcodeBurst, tag, TeamTranscript.Action.extra]
  | native =>
    simp only [TeamOpcode.prepare, tag] at ha
    split at ha
    · simpa [opcodeBurst, tag] using (native_extra _ ha).symm
    · simp [TeamOpcode.Exit.action, TeamOpcode.nativeAction, ISA.Callback.action, TeamRAM.Instr.action] at ha
  | call j addr len next =>
    simp only [TeamOpcode.prepare, tag, TeamOpcode.Exit.action, TeamRAM.Instr.action] at ha
    split at ha
    · cases ha; simp [opcodeBurst, tag, TeamTranscript.Action.extra, TeamOpcode.State.logged]
    · contradiction

  | callReg idReg addr len next =>
    cases hs : TeamOpcodeSelect.select a (s.reg idReg).val with
    | none => simp [TeamOpcode.prepare, tag, hs, TeamOpcode.selectedExit, TeamOpcode.Exit.action,
        TeamOpcode.nativeAction, ISA.Callback.action, TeamRAM.Instr.action] at ha
    | some j =>
      simp only [TeamOpcode.prepare, tag, hs, TeamOpcode.selectedExit, Option.elim_some,
        TeamOpcode.Exit.action, TeamRAM.Instr.action] at ha
      split at ha
      · cases ha; simp [opcodeBurst, tag, TeamTranscript.Action.extra, TeamOpcode.State.logged]
      · contradiction

/-- The prepared bank cannot expose a write log or a private persistent word. -/
theorem prepared_clean (P : TeamOpcode.Program p r k a) (pub : Fin k → Word w) (s : TeamOpcode.State w p r) :
    (TeamOpcode.prepare P pub s).2.persistent = 0 ∧ (TeamOpcode.prepare P pub s).2.writes = [] := by
  cases tag : P.tag s.pc with
  | sign | call | callReg => simp [TeamOpcode.prepare, tag, TeamOpcode.State.logged]
  | native =>
    simp only [TeamOpcode.prepare, tag]
    split
    · rename_i ok
      cases hi : P.base.code s.pc <;> simp [ISA.post, TeamOpcode.State.logged]
      simp [hi, TeamOpcode.enabled, TeamOpcode.permitted] at ok
    · exact ⟨rfl,rfl⟩

/-- The unclocked accept instruction is exactly the kind intercepted by the physical
loop before it spends a tick. -/
theorem accept_iff (P : TeamOpcode.Program p r k a) (pub : Fin k → Word w)
    (lib : TeamOpcode.Macros w a) (s : TeamOpcode.State w p r) :
    P.fetch pub lib s = .accept ↔ TeamLocalClock.Loop.kind P s.pc = .accept := by
  rw [← TeamOpcode.prepare_action]
  cases tag : P.tag s.pc with
  | sign | call => simp [TeamOpcode.prepare, tag, TeamOpcode.Exit.action, TeamLocalClock.Loop.kind]
  | callReg idReg addr len next =>
    cases hs : TeamOpcodeSelect.select a (s.reg idReg).val <;>
      simp [TeamOpcode.prepare,tag,hs,TeamOpcode.selectedExit,TeamOpcode.Exit.action,
        TeamLocalClock.Loop.kind,TeamOpcode.nativeAction,ISA.Callback.action]
  | native =>
    simp only [TeamOpcode.prepare, tag, TeamLocalClock.Loop.kind]
    split
    · cases hi : P.base.code s.pc <;>
        simp [ISA.exitFor, TeamOpcode.Exit.action, TeamOpcode.nativeAction, ISA.Callback.action]
    · rename_i disabled
      cases hi : P.base.code s.pc <;> simp [TeamOpcode.Exit.action, TeamOpcode.nativeAction, ISA.Callback.action]
      simp [hi, TeamOpcode.enabled, TeamOpcode.permitted, TeamOpcode.divisor] at disabled

/-- On a valid memory action below the private cap, the clock always executes its
normal local/global countdown guard with precisely the logical extra. -/
theorem result_action (P : TeamOpcode.Program p r k a) (pub : Fin k → Word w)
    (lib : TeamOpcode.Macros w a) (s : TeamOpcode.State w p r) (c : Window w)
    (act : TeamTranscript.Action (Word w)) (ha : (P.fetch pub lib s).action = some act) (bound : act.extra ≤ c.cap.val) :
    TeamLocalClock.Loop.result P pub s c.block c.global c.elapsed c.cap =
      TeamLocalClock.Loop.afterGuard P pub s c.block c.global c.elapsed (opcodeBurst P s) c.cap := by
  have hb : opcodeBurst P s ≤ c.cap := by
    change (opcodeBurst P s).val ≤ c.cap.val
    rwa [opcodeBurst_eq P pub lib s act ha]
  cases tag : P.tag s.pc with
  | sign => simp [TeamLocalClock.Loop.result, TeamLocalClock.Loop.kind, tag, opcodeBurst]
  | call j addr len next | callReg j addr len next =>
    have hq : s.reg len ≤ c.cap := by simpa [opcodeBurst, tag] using hb
    simp [TeamLocalClock.Loop.result, TeamLocalClock.Loop.kind, tag, opcodeBurst, hq]
  | native =>
    rw [← TeamOpcode.prepare_action] at ha
    cases hi : P.base.code s.pc <;>
      simp [TeamLocalClock.Loop.result, TeamLocalClock.Loop.kind, tag, hi, opcodeBurst]
    all_goals simp [TeamOpcode.prepare, TeamOpcode.enabled, TeamOpcode.permitted, TeamOpcode.divisor,
          ISA.exitFor, TeamOpcode.Exit.action, TeamOpcode.nativeAction, ISA.Callback.action, tag, hi, TeamRAM.Instr.action] at ha

end TeamSite

end BorderVNP
end Computability
end OAI
