import OAI.Computability.VPVNP.PairTraversalControllerPrepare
import OAI.Computability.VPVNP.PairTraversalControllerRoute
import OAI.Computability.VPVNP.PairTraversalControllerBody
import OAI.Computability.VPVNP.PairTraversalControllerMemory

/-!
# Native active, reset and terminal bursts of the descriptor controller

The live operand and dispatch trace contains only reads and ticks. An active
call then replays the exact reference worker trace and returns the encoded
successor site. The two boundary cases leave the external memory untouched.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.TraversalController

open BurstRAM BurstRAM.PrivateRAM PrimedInputRAM PrimedStackRAM CompressorRecords
open TraversalControllerInputs TraversalControllerOrdinal TraversalRows
set_option maxRecDepth 12000

open scoped Fin.CommRing
open private value_outside from OAI.Computability.VPVNP.PairTraversalControllerFormula

variable {w : ℕ}

/-- A reference worker occupies the physical layer selected by the controller. -/
def Pass.Located (pub : Fin 11 → Word w) (m : Memory w) (L p : ℕ) : Pass w → Prop
  | .tag fields n => p < L ∧ tagParams pub m (p % L) = fields ∧ (siteCount pub m (p % L)).val = n
  | .leaf fields n => L ≤ p ∧ p % L = 0 ∧ leafParams pub m = fields ∧
    (siteCount pub m (p % L)).val = n
  | .fiber fields _ n => L ≤ p ∧ p % L ≠ 0 ∧ fiberParams pub m (p % L - 1) = fields ∧
    (siteCount pub m (p % L)).val = n

/-- The controller route that runs the worker appropriate to a tag, leaf-row, or
placement-fiber pass. -/
def Pass.route : Pass w → Native.Route
  | .tag .. => .role
  | .leaf .. => .leaf
  | .fiber .. => .fiber

/-- Translate the chosen pass's local worker labels into the corresponding native controller
addresses. -/
def Pass.labels (P : Pass w) : P.body.Label → Fin Native.P :=
  match P with
  | .tag .. => Native.rolePC
  | .leaf .. => Native.leafPC
  | .fiber .. => Native.fiberPC

private theorem Pass.linked (P : Pass w) (pub : Fin 11 → Word w) :
    Flow.Linked (Native.machine pub) P.body P.labels Native.nextPC Native.rejectPC := by
  cases P with
  | tag => exact Native.linked_role pub
  | leaf => exact Native.linked_leaf pub
  | fiber => exact Native.linked_fiber pub

private theorem Pass.start_label (P : Pass w) : P.route.pc = P.labels P.body.entry := by
  cases P <;> rfl

private theorem Pass.at_route {pub : Fin 11 → Word w} {m : Memory w} {L N p i : ℕ}
    {rs : Regs w R} {P : Pass w} (read : Readback pub m L N p i rs) (hloc : P.Located pub m L p)
    (level : 0 < L) (phase : p < 2 * L) (digit : i ≤ N) (active : i < P.count)
    (fit : 2 * L * (N + 1) < 2 ^ w) : Native.route rs = P.route ∧ P.Bank rs := by
  rw [read.route_eq level phase.le digit fit, ite_eq_left phase]
  cases P with
  | tag fields n =>
    change i < n at active
    obtain ⟨hp, hbank, hc⟩ := hloc
    exact ⟨by rw [hc, ite_eq_left active, ite_eq_left hp]; rfl, read.role.trans hbank⟩
  | leaf fields n =>
    change i < n at active
    obtain ⟨hp, hj, hbank, hc⟩ := hloc
    exact ⟨by rw [hc, ite_eq_left active, ite_eq_right (Nat.not_lt_of_ge hp), ite_eq_left hj]; rfl,
      read.leaf.trans hbank⟩
  | fiber fields cap n =>
    change i < n at active
    obtain ⟨hp, hj, hbank, hc⟩ := hloc
    exact ⟨by rw [hc, ite_eq_left active, ite_eq_right (Nat.not_lt_of_ge hp), ite_eq_right hj]; rfl,
      (read.fiber hj).trans hbank⟩

/-- Number of register-setup instructions needed to evaluate the controller's traversal
formulas. -/
def setupLen : ℕ := (RegisterSetup.lines formulas).length

/-- Bounds and read-only behavior of the administrative event prefix before a worker, including
its exact probe count and empty choice tape. -/
structure Admin (es : List (Event w)) : Prop where
  clock : es.length ≤ setupLen + 7
  probes : countProbes es = 257
  bits : choiceBits es = []
  readOnly : ∀ a v, Event.write a v ∉ es
  replay : ∀ m : Memory w, after m es = m

private theorem prepare_step (pub : Fin 11 → Word w) (m : Memory w) (L N p i : ℕ)
    (hL : (terminalField pub m 1).val = L) (hN : (siteCount pub m 0).val = N)
    (level : 0 < L) (digit : i ≤ N) (fit : 2 * L * (N + 1) < 2 ^ w)
    (stFit : pack N p i < 2 ^ w) :
    let st := (pack N p i : Word w)
    let M := Native.machine pub
    ∃ es rs, Admin es ∧ Readback pub m L N p i rs ∧ (∀ j, rs (scratchRegs j) = 0) ∧
      es = Native.prefixTrace pub st m rs ∧
      ∀ fuel, execute M.program (fuel + es.length) (M.program.start st) m [] =
        (execute M.program fuel ⟨(Native.route rs).pc, st, rs, fun _ => 0⟩ m []).map
          (Flow.prependEvents es) := by
  obtain ⟨es, rs, vals, zeros, len, probes, bits, writes, replay, run, origin⟩ :=
    Native.prepare_trace pub (pack N p i : Word w) m
  have pitchFit : N + 1 < 2 ^ w := (Nat.le_mul_of_pos_left _ (by omega : 0 < 2 * L)).trans_lt fit
  have ticks : (Native.route rs).ticks ≤ 4 := by cases Native.route rs <;> decide
  have lim : es.length ≤ setupLen + 7 := by
    change _ ≤ (RegisterSetup.lines formulas).length + 7
    omega
  exact ⟨es, rs, ⟨lim, probes.trans TraversalRoles.ControllerMemory.controller_setup_loads,
    bits, writes, replay⟩, readback pub m L N p i rs hL hN level digit pitchFit stFit vals,
    zeros, origin, fun fuel => run fuel []⟩

private theorem finish_next (pub : Fin 11 → Word w) (st : Word w) (rs : Regs w R) (m : Memory w)
    (extra : ℕ) : execute (Native.machine pub).program (extra + 1)
      ⟨Native.nextPC, st, rs, fun _ => 0⟩ m [] = some ⟨[], some (rs (value 7))⟩ := by
  simp [execute, Machine.program, Native.code_next, Instr.run]

/-- A complete active burst adds the fixed read-only operand prefix to the
actual native tag or row report and advances by exactly one site. -/
theorem active_step_trace (pub : Fin 11 → Word w) (m : Memory w) (L N p i : ℕ)
    (hL : (terminalField pub m 1).val = L) (hN : (siteCount pub m 0).val = N)
    (level : 0 < L) (phase : p < 2 * L) (digit : i ≤ N) (fit : 2 * L * (N + 1) < 2 ^ w)
    (P : Pass w) (hloc : P.Located pub m L p) (active : i < P.count) (small : Report w)
    (reference : P.At (i : Word w) m small) :
    ∃ es, Admin es ∧ (∃ rs, es = Native.prefixTrace pub (pack N p i : Word w) m rs) ∧
      ∀ fuel, setupLen + 7 + P.clock ≤ fuel →
      execute (Native.machine pub).program fuel
        ((Native.machine pub).program.start (pack N p i : Word w)) m [] =
        some ⟨es ++ small.events, some (pack N p (i + 1) : Word w)⟩ := by
  let M := Native.machine pub
  let st := (pack N p i : Word w)
  have stFit := (pack_lt phase digit).trans fit
  obtain ⟨es, rs, admin, read, zero, origin, enter⟩ :=
    prepare_step pub m L N p i hL hN level digit fit stFit
  obtain ⟨route, bank⟩ := Pass.at_route read hloc level phase digit active fit
  obtain ⟨out, body, bits, clock, frame⟩ := Pass.lift reference pub st rs bank read.site zero
  have next : out (value 7) = (pack N p (i + 1) : Word w) :=
    (frame _ (value_outside 7)).trans read.next
  refine ⟨es, admin, ⟨rs, origin⟩, fun fuel enough => ?_⟩
  let extra := fuel - es.length - small.events.length - 1
  have exactFuel : fuel = (small.events.length + (extra + 1)) + es.length := by
    have := admin.clock
    dsimp only [extra]
    omega
  have work := body.execute (P.linked pub) (Native.code_reject pub) (fun _ => 0) (extra + 1) []
  rw [bits, List.nil_append, finish_next, next] at work
  rw [exactFuel, enter, route, Pass.start_label, work]
  simp [Flow.prependEvents]

theorem active_step (pub : Fin 11 → Word w) (m : Memory w) (L N p i : ℕ)
    (hL : (terminalField pub m 1).val = L) (hN : (siteCount pub m 0).val = N)
    (level : 0 < L) (phase : p < 2 * L) (digit : i ≤ N) (fit : 2 * L * (N + 1) < 2 ^ w)
    (P : Pass w) (hloc : P.Located pub m L p) (active : i < P.count) (small : Report w)
    (reference : P.At (i : Word w) m small) :
    ∃ es, Admin es ∧ ∀ fuel, setupLen + 7 + P.clock ≤ fuel →
      execute (Native.machine pub).program fuel
        ((Native.machine pub).program.start (pack N p i : Word w)) m [] =
        some ⟨es ++ small.events, some (pack N p (i + 1) : Word w)⟩ := by
  obtain ⟨es, admin, _, run⟩ := active_step_trace
    pub m L N p i hL hN level phase digit fit P hloc active small reference
  exact ⟨es, admin, run⟩

/-- Closing a level costs one read-only burst. The next level starts at zero
and the final level advances to the terminal sentinel. -/
theorem reset_step_trace (pub : Fin 11 → Word w) (m : Memory w) (L N p i : ℕ)
    (hL : (terminalField pub m 1).val = L) (hN : (siteCount pub m 0).val = N)
    (level : 0 < L) (phase : p < 2 * L) (digit : i ≤ N) (fit : 2 * L * (N + 1) < 2 ^ w)
    (endSite : i = (siteCount pub m (p % L)).val) :
    ∃ es, Admin es ∧ (∃ rs, es = Native.prefixTrace pub (pack N p i : Word w) m rs) ∧
      ∀ fuel, setupLen + 8 ≤ fuel →
      execute (Native.machine pub).program fuel
        ((Native.machine pub).program.start (pack N p i : Word w)) m [] =
        some ⟨es, some (pack N (p + 1) 0 : Word w)⟩ := by
  obtain ⟨es, rs, admin, read, _, origin, enter⟩ := prepare_step pub m L N p i hL hN level digit fit
    ((pack_lt phase digit).trans fit)
  have hr := read.route_eq level phase.le digit fit
  rw [ite_eq_left phase, ite_eq_right (by omega)] at hr
  refine ⟨es, admin, ⟨rs, origin⟩, fun fuel enough => ?_⟩
  let extra := fuel - es.length - 1
  have exactFuel : fuel = extra + 1 + es.length := by have := admin.clock; dsimp only [extra]; omega
  rw [exactFuel, enter, hr]
  simp [Native.Route.pc, execute, Machine.program, Native.code_reset, Instr.run, read.reset,
    Flow.prependEvents]

theorem reset_step (pub : Fin 11 → Word w) (m : Memory w) (L N p i : ℕ)
    (hL : (terminalField pub m 1).val = L) (hN : (siteCount pub m 0).val = N)
    (level : 0 < L) (phase : p < 2 * L) (digit : i ≤ N) (fit : 2 * L * (N + 1) < 2 ^ w)
    (endSite : i = (siteCount pub m (p % L)).val) :
    ∃ es, Admin es ∧ ∀ fuel, setupLen + 8 ≤ fuel →
      execute (Native.machine pub).program fuel
        ((Native.machine pub).program.start (pack N p i : Word w)) m [] =
        some ⟨es, some (pack N (p + 1) 0 : Word w)⟩ := by
  obtain ⟨es, admin, _, run⟩ := reset_step_trace
    pub m L N p i hL hN level phase digit fit endSite
  exact ⟨es, admin, run⟩

/-- Accept once after both complete passes, with all worker memory intact. -/
theorem stop_step_trace (pub : Fin 11 → Word w) (m : Memory w) (L N : ℕ)
    (hL : (terminalField pub m 1).val = L) (hN : (siteCount pub m 0).val = N)
    (level : 0 < L) (fit : 2 * L * (N + 1) < 2 ^ w) :
    ∃ es, Admin es ∧ (∃ rs, es = Native.prefixTrace pub (pack N (2 * L) 0 : Word w) m rs) ∧
      ∀ fuel, setupLen + 8 ≤ fuel →
      execute (Native.machine pub).program fuel
        ((Native.machine pub).program.start (pack N (2 * L) 0 : Word w)) m [] =
        some ⟨es, none⟩ := by
  obtain ⟨es, rs, admin, read, _, origin, enter⟩ := prepare_step pub m L N (2 * L) 0 hL hN level
    (Nat.zero_le _) fit (by simpa [pack] using fit)
  have hr := read.route_eq level le_rfl (Nat.zero_le _) fit
  rw [ite_eq_right (Nat.lt_irrefl _)] at hr
  refine ⟨es, admin, ⟨rs, origin⟩, fun fuel enough => ?_⟩
  let extra := fuel - es.length - 1
  have exactFuel : fuel = extra + 1 + es.length := by have := admin.clock; dsimp only [extra]; omega
  rw [exactFuel, enter, hr]
  simp [Native.Route.pc, execute, Machine.program, Native.code_accept, Instr.run,
    Flow.prependEvents]

theorem stop_step (pub : Fin 11 → Word w) (m : Memory w) (L N : ℕ)
    (hL : (terminalField pub m 1).val = L) (hN : (siteCount pub m 0).val = N)
    (level : 0 < L) (fit : 2 * L * (N + 1) < 2 ^ w) :
    ∃ es, Admin es ∧ ∀ fuel, setupLen + 8 ≤ fuel →
      execute (Native.machine pub).program fuel
        ((Native.machine pub).program.start (pack N (2 * L) 0 : Word w)) m [] =
        some ⟨es, none⟩ := by
  obtain ⟨es, admin, _, run⟩ := stop_step_trace
    pub m L N hL hN level fit
  exact ⟨es, admin, run⟩

end PairSimulation.TraversalController

end VPVNP
end Computability
end OAI
