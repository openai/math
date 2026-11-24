import OAI.Computability.VPVNP.RAMProcessorLocal

/-!
# Complete private execution through the next external action

The bounded scan executes the instruction table repeatedly. It retains the
exact local event prefix needed to identify the corresponding native report.
Only an actual read, write, finish or rejection returns control to the caller.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RAMTape.LocalProcessor

open BurstRAM PrivateRAM

variable {w p r k : ℕ}

/-- Result at the boundary of a private instruction scan, including its callback,
configuration, remaining fuel and choices, and chronological event prefix. -/
structure Yield (w p r : ℕ) where
  /-- Callback reached by the scan. The scan also returns the rejecting callback when it
  exhausts fuel or a required choice bit. -/
  exit : ISA.Callback p r
  /-- Private program counter, registers, persistent state and write log at the scan boundary,
  before the caller handles the callback. -/
  cfg : LogConfig w p r
  /-- Instruction fuel left after the scan. Fetching the instruction that requests an external
  action consumes one unit. -/
  fuel : ℕ
  /-- Unused suffix of the binary choice stream after the private branches in this segment. -/
  bits : List Bool
  /-- Ticks and chosen branch bits from the private instructions preceding the callback, in
  execution order. -/
  prefixEvents : List (Event w)

/-- Add an earlier instruction event to the front of a scan's chronological prefix. -/
def Yield.prepend (e : Event w) (y : Yield w p r) : Yield w p r :=
  {y with prefixEvents := e :: y.prefixEvents}

/-- Run private instructions up to the next read, write, return, accept or reject callback.
Follow jumps and consume branch bits while recording their events, and reject on exhausted
fuel or choices. -/
def scan (T : Template p r k) (pub : Fin k → Word w) : ℕ → LogConfig w p r → List Bool → Yield w p r
  | 0, c, bs => ⟨.reject, c, 0, bs, []⟩
  | f+1, c, bs =>
    let out := instructionPost T pub c
    match instructionExit T c with
    | .next j => (scan T pub f {out with pc := j} bs).prepend .tick
    | .choose yes no => match bs with
      | [] => ⟨.reject, out, f, [], []⟩
      | b :: tail => (scan T pub f {out with pc := if b then yes else no} tail).prepend (.choice b)
    | cb => ⟨cb, out, f, bs, []⟩

private def continuation : ISA.Callback p r → Bool
  | .next _ | .choose _ _ => true
  | _ => false

private theorem boundary (T : Template p r k) (cb : ISA.Callback p r) (h : continuation cb = false)
    (s : Stacks (Port r k)) :
    StackStep (code T) (.instr (ISA.callback T cb)) s (.exit cb) s := by
  apply StackStep.goto
  cases cb <;> simp_all [code, ISA.resume_callback, continuation]

/-- The physical controller reaches the declared exit with the exact bank
and suffix, including when fuel or choices run out. -/
theorem scan_run (T : Template p r k) (pub : Fin k → Word w) (f : ℕ)
    (c : LogConfig w p r) (bs : List Bool) (limit : ℕ) (hl : c.writes.length+f ≤ limit) :
    let out := scan T pub f c bs
    ∃ ticks ≤ f*(ISA.prepareBound w limit + 4)+1, StackRuns (code T) ticks (.begin c.pc)
      (store pub c f bs) (.exit out.exit) (store pub out.cfg out.fuel out.bits) := by
  induction f generalizing c bs with
  | zero => exact ⟨1, by simp, cutoff ..⟩
  | succ f ih =>
    let out := instructionPost T pub c
    have hg : out.writes.length ≤ c.writes.length+1 := ISA.post_writes_length_le ..
    obtain ⟨d, hd, fetchRun⟩ := fetch T pub c f bs
    have hm : ISA.prepareBound w c.writes.length ≤ ISA.prepareBound w limit :=
      Nat.mul_le_mul_left _ (by omega)
    have ht {t : ℕ} (h : t ≤ f*(ISA.prepareBound w limit+4)+1) :
        d+(t+1) ≤ (f+1)*(ISA.prepareBound w limit+4)+1 := by rw [Nat.succ_mul]; omega
    have hd' : d+1 ≤ (f+1)*(ISA.prepareBound w limit+4)+1 := by rw [Nat.succ_mul]; omega
    dsimp only
    cases he : instructionExit T c with
    | next j =>
      rw [he] at fetchRun
      let after := {out with pc := j}
      obtain ⟨t, ht', run⟩ := ih after bs (by change out.writes.length+f ≤ limit; omega)
      refine ⟨_, ht ht', ?_⟩
      simpa only [scan, he, Yield.prepend] using
        fetchRun.trans (.cons (next_step T j _) run)
    | choose yes no =>
      rw [he] at fetchRun
      cases bs with
      | nil =>
        refine ⟨_, hd', ?_⟩
        simpa only [scan, he] using fetchRun.trans (.cons (short_choice T yes no pub out f) (.nil ..))
      | cons b bs =>
        let after := {out with pc := if b then yes else no}
        obtain ⟨t, ht', run⟩ := ih after bs (by change out.writes.length+f ≤ limit; omega)
        refine ⟨_, ht ht', ?_⟩
        simpa only [scan, he, Yield.prepend] using
          fetchRun.trans (.cons (branch_step T yes no pub out f b bs) run)
    | read dst addr j | write addr src j | returnState src | accept | reject =>
      rw [he] at fetchRun
      refine ⟨_, hd', ?_⟩
      simpa only [scan, he] using fetchRun.trans (.cons (boundary T _ rfl _) (.nil ..))

end RAMTape.LocalProcessor

end VPVNP
end Computability
end OAI
