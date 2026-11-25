import OAI.Computability.BorderVNP.TeamBurstProbeStep
import OAI.Computability.BorderVNP.TeamBurstProbeEntry
import OAI.Computability.BorderVNP.TeamMemoryCallback
import OAI.Computability.BorderVNP.TeamLocalClockLoop
import OAI.Computability.BorderVNP.TeamPrivateCompiler

/-! # Physical ports shared by one processor's instruction loop

Every memory callback and every private burst appends to the same physical record
buffer. Private calls receive the burst reader's own input stack. Ordinary loads,
stores and calls use the timestamp supplied by the real clock guard.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamSite

open VPVNP RAMTape BurstRAM

variable {r k m g d : ℕ}

/-- Persistent registers, the shared record emitter, and disjoint private scratch. -/
inductive Port (r k d : ℕ) where
  | clock (p : TeamLocalClock.Port r k)
  | burst (p : TeamBurstProbeStep.Port)
  | guard (p : TeamBurstGuard.Port)
  | high | privateTemp
  | track (p : TeamPrivateTape.Port d)
  deriving DecidableEq, Fintype

/-- The emitter used by ordinary and consecutive memory probes. -/
abbrev probe (p : TeamProbeEmit.Port) : Port r k d := .burst (.probe p)

/-- The adaptive RAM's word-register bank, shared with the clocked dispatcher. -/
abbrev isa (p : ISA.Port r k) : Port r k d := .clock (.isa p)

/-- Wire a load or store to the actual registers, cumulative timestamp and record buffer. -/
def memory : TeamMemoryCallback.Port r k → Port r k d
  | .inl p => isa p
  | .inr (.inl p) => probe p
  | .inr (.inr false) => .clock .stamp
  | .inr (.inr true) => .clock .copyScratch

/-- The ordinary callback's distinct named ports have distinct physical locations. -/
theorem memory_injective : Function.Injective (memory (r := r) (k := k) (d := d)) := by
  rintro (p | p | b) (q | q | c) h <;>
    first | cases b <;> cases c <;> simp_all [memory] | cases b <;> simp_all [memory] |
      cases c <;> simp_all [memory] | simp_all [memory]

/-- The native private input is the bit string physically assembled by the burst.
The tape workspaces and the loader's reversal scratch are inaccessible to ordinary RAM opcodes. -/
def privateTape : TeamPrivateInput.NativePort m g → Port r k (m*g)
  | .inl false => .burst .privateInput
  | .inl true => .privateTemp
  | .inr p => .track p

/-- The loader and native machine use pairwise distinct physical ports. -/
theorem privateTape_injective : Function.Injective (privateTape (r := r) (k := k) (m := m) (g := g)) := by
  rintro (b | p) (c | q) h <;>
    first | cases b <;> cases c <;> simp_all [privateTape] | cases b <;> simp_all [privateTape] |
      cases c <;> simp_all [privateTape] | simp_all [privateTape]

/-- Lift the actual prepared-register and countdown execution into the shared site bank.
It leaves the probe buffer and all private data exactly as it found them. -/
theorem clock_step {w p m : ℕ} (P : TeamOpcode.Program p r k m) (pub : Fin k → Word w)
    (s : TeamOpcode.State w p r) (block left elapsed max : Word w)
    (safe : elapsed.val+left.val < 2^w) (base : Stacks (Port r k d))
    (hc : base ∘ Port.clock = TeamLocalClock.bank pub s block left elapsed max) :
    let x := TeamLocalClock.Loop.result P pub s block left elapsed max
    ∃ n ≤ 1050*(w+1)^2, StackRuns (fun q => (TeamLocalClock.Loop.rows P q).rename Port.clock id) n
      (.enter s.pc) base (.exit x.1) (installStacks Port.clock base x.2) := by
  intro x
  obtain ⟨n, hn, h⟩ := TeamLocalClock.Loop.step P pub s block left elapsed max safe
  refine ⟨n, hn, ?_⟩
  have lift := h.lift Port.clock (fun _ _ he => Port.clock.inj he) id base
    (target := fun q => (TeamLocalClock.Loop.rows P q).rename Port.clock id) (fun _ _ => rfl)
  have he := installStacks_eq (fun _ _ he => Port.clock.inj he) base
    (TeamLocalClock.bank pub s block left elapsed max) (congrFun hc)
  simpa only [id_eq, he] using lift

end TeamSite

end BorderVNP
end Computability
end OAI
