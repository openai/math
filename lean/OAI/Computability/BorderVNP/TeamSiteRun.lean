import OAI.Computability.BorderVNP.TeamSiteCallback

/-! # Replaying a complete charged RAM event in the physical instruction loop

Starting at a fetch label, the finite processor charges its real countdown,
executes the complete native callback and restores the instruction boundary.
Its only new record bytes and consumed choices are precisely those specified
by the native event.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamSite

open VPVNP RAMTape TeamPrivateFragment TeamTapeHandoff
open BurstRAM (Word wordBits)
open RAMSerialization (WordRecord)
open TeamRAM (Event)
open TeamEventRecords (physicalSlots)

variable {Q Γ : Type} {w p r k a m g H : ℕ} {hw : 2 ≤ w+1}

/-- Uniform cost of fetching, charging, executing and clearing one callback. -/
def instructionBudget (w m g fuel q : ℕ) : ℕ :=
  1050*(w+1)^2 + Work.eventBudget w m g fuel q + (w+1)

/-- Complete sequence of physically stored slots from a chronological list of events. -/
abbrev chunkSlots (t : ℕ) (es : List (Event w)) := TeamEventRecords.historySlots t es

/-- The sort buffer uses two records per logical probe, within its reserved ticks. -/
theorem slots_length_le (t : ℕ) (e : Event w) : (physicalSlots t e).length ≤ 2*(1+e.action.extra) := by
  have pairs {v : ℕ} (xs : List (TeamRecords.Record (Word v))) :
      (xs.flatMap TeamRecords.pair).length = 2*xs.length := by
    induction xs with
    | nil => rfl
    | cons x xs ih =>
      rw [List.flatMap_cons, List.length_append, List.length_cons, ih]
      change 2+2*xs.length = 2*(xs.length+1); omega
  simp only [physicalSlots, TeamEventRecords.physicalFields, List.length_map, pairs]
  apply Nat.mul_le_mul_left
  simp only [TeamEventRecords.eventFields, List.length_zipWith, TeamEventRecords.access_length]
  cases e.action with
  | ordinary x => cases x <;> simp [TeamTranscript.Action.extra]
  | burst x q => simp [TeamTranscript.Action.extra]

private theorem old_length_le {S : Type*} (i : TeamRAM.Instr w S) (e : Event w) (s : S)
    (act : i.action = some e.action) (go : i.advance e.choices e.old = some (s,e.sign)) :
    e.old.length ≤ 1+e.action.extra := by
  rw [← TeamEventRecords.arity_of_advance i e s act go 0, TeamEventRecords.access_length]
  cases e.action with
  | ordinary x => cases x <;> simp [TeamTranscript.Action.extra]
  | burst x q => simp [TeamTranscript.Action.extra]

private theorem charged_result (P : TeamOpcode.Program p r k a) (pub : Fin k → Word w)
    (M : TeamOpcode.Macros w a) (s : TeamOpcode.State w p r) (c : Window w) (e : Event w)
    (act : (P.fetch pub M s).action = some e.action) (cap : e.action.extra ≤ c.cap.val)
    (fits : c.Fits e.action.extra) :
    TeamLocalClock.Loop.result P pub s c.block c.global c.elapsed c.cap =
      (.callback (TeamOpcode.prepare P pub s).1,
       (c.charge e.action.extra).callbackBank pub (TeamOpcode.prepare P pub s).2.reg c.first) := by
  let q := opcodeBurst P s
  have hq : q.val = e.action.extra := opcodeBurst_eq P pub M s _ act
  have gate : decision c.block.val c.global.val q.val = .execute := (decision_execute_iff ..).2 (hq ▸ fits)
  rw [result_action P pub M s c _ act cap, TeamLocalClock.Loop.afterGuard, gate]
  change (TeamLocalClock.Loop.Exit.callback _, TeamLocalClock.banks _ _ _ _ _) = _
  rw [Prod.mk.injEq, and_iff_right rfl]
  funext u
  obtain ⟨persist,writes⟩ := prepared_clean P pub s
  cases u with
  | isa j => simp [TeamLocalClock.banks, Window.callbackBank, ISA.configBank, persist, writes]
  | meter j => simp [TeamLocalClock.banks, Window.callbackBank, Window.charge, ← hq, q]
  | stamp | copyScratch | maxBurst => rfl

/-- Clearing a callback timestamp restores the actual canonical fetch bank, with the
returned register state and already charged countdowns. -/
theorem reset_clock (c : Window w) (pub : Fin k → Word w) (s : TeamOpcode.State w p r) (tick : Word w)
    {d : ℕ} (b : Stacks (Port r k d)) (h : b ∘ Port.clock = c.callbackBank pub s.reg tick) :
    Function.update b (.clock .stamp) [] ∘ Port.clock = c.bank pub s := by
  funext u
  by_cases hu : u = .stamp
  · subst u; simp [Window.bank, TeamLocalClock.bank, TeamLocalClock.banks]
  · have ne : (Port.clock u : Port r k d) ≠ .clock .stamp := fun e => hu (Port.clock.inj e)
    rw [Function.comp_apply, Function.update_of_ne ne, show b (.clock u) = c.callbackBank pub s.reg tick u from congrFun h u]
    cases u <;> first | rfl | contradiction

/-- One full charged native instruction, with no hidden choices in dispatch or reset.
The output is ready for any subsequent instruction on the same bank. -/
theorem event_run (P : TeamOpcode.Program p r k a) (lib : Fin a → Macro Q Γ m g) (fuel : ℕ)
    (pub : Fin k → Word w) (s next : TeamOpcode.State w p r) (c : Window w) (sg : Option Bool)
    (e : Event w) (rs : List (WordRecord (w+1))) (base : Stacks (Port r k (m*g))) (rest : List Bool)
    (safe : c.Safe) (fits : c.Fits e.action.extra) (cap : e.action.extra ≤ c.cap.val)
    (act : (P.fetch pub (fun j => (lib j).eval fuel) s).action = some e.action)
    (go : (P.fetch pub (fun j => (lib j).eval fuel) s).advance e.choices e.old = some (next,e.sign))
    (clock : base ∘ Port.clock = c.bank pub s) (ready : Work.Ready hw H rs base)
    (space : rs.length+2*c.block.val ≤ 4*H) :
    ∃ n out, n ≤ instructionBudget w m g fuel e.action.extra ∧
      StackRuns (replay (Loop.code P lib)) n (.clock sg (.enter s.pc),eventBits e++rest) base
        (.clock (Loop.times sg (signBit e.sign)) (.enter next.pc),rest) out ∧
      Work.Ready hw H (rs++physicalSlots (c.elapsed.val+1) e) out ∧
      out ∘ Port.clock = (c.charge e.action.extra).bank pub next ∧
      (rs++physicalSlots (c.elapsed.val+1) e).length + 2*(c.charge e.action.extra).block.val ≤ 4*H := by
  let M : TeamOpcode.Macros w a := fun j => (lib j).eval fuel
  let prep := TeamOpcode.prepare P pub s
  let win := c.charge e.action.extra
  let ticks := c.first
  let cb := win.callbackBank pub prep.2.reg ticks
  let mid := installStacks Port.clock base cb
  have cr := charged_result P pub M s c e act cap fits
  obtain ⟨n,hn,guard⟩ := Loop.clock_run P lib sg pub s c.block c.global c.elapsed c.cap safe base clock (eventBits e++rest)
  rw [cr] at guard
  have cm : mid ∘ Port.clock = cb := funext fun u => installStacks_at (fun _ _ he => Port.clock.inj he) ..
  rw [← TeamOpcode.prepare_action] at act go
  have first := c.first_val safe fits
  obtain ⟨hblock,_,htime,hs⟩ := c.charged_values e.action.extra safe fits
  have tickBound : ticks.val+e.action.extra ≤ 2^w := by
    have he := (c.charge e.action.extra).elapsed.isLt
    change c.first.val + _ ≤ _; rw [first]; omega
  have count := old_length_le _ _ _ act go
  have room := fits.1
  obtain ⟨t,b,ht,callback,hr,cbank⟩ := Work.callback_run P lib fuel sg prep.1 prep.2 e next win ticks pub
    (ready.installClock cb) cm act go cap tickBound (by omega) rest
  have reset := Loop.reset_run P lib (Loop.times sg (signBit e.sign)) next.pc b rest
  have tickLen : (b (.clock .stamp)).length = w := (congrArg List.length (congrFun cbank .stamp)).trans (BurstRAM.length_wordBits _)
  rw [tickLen] at reset
  rw [show ticks.val = c.elapsed.val+1 from first] at hr
  refine ⟨_,_,Nat.add_le_add_right (Nat.add_le_add hn ht) _, (guard.trans callback).trans reset,hr.reset,
    reset_clock win pub next ticks b cbank,?_⟩
  rw [List.length_append,hblock]
  have hlen := slots_length_le (c.elapsed.val+1) e
  omega

end TeamSite

end BorderVNP
end Computability
end OAI
