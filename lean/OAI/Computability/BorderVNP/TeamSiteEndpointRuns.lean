import OAI.Computability.BorderVNP.TeamSiteEndpoint
import OAI.Computability.BorderVNP.TeamLocalClockStartupExact

/-!
# Exact physical endpoint bounds and record-buffer preservation

A computed processor exit uses its actual register words and the candidate
already present on its incident successor port. Validation preserves every
stack of the signed instruction loop, including the records still to be sorted.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamSite.Endpoint

open VPVNP RAMTape BurstRAM RAMTape.PublicExprMachine TeamLocalClock TeamPrivateFragment

variable {w p r k a m g d : ℕ} {Q Γ : Type}

private theorem finish_ready (base : Stacks (Port r k d)) (core : Stacks (TeamLocalClock.Port r k))
    (hclock : ∀ i, base (.site (.clock i)) = core i) (payload : base .payload = [])
    (tmp : base .tmp = []) :
    base ∘ finish = Finish.bank core [] (base .outgoing) := by
  funext u
  cases u <;> first | rfl | exact hclock _ | exact payload | exact tmp

private theorem finish_site (base : Stacks (Port r k d)) (next : Stacks (Finish.Port r k))
    (clock : ∀ i, next (.clock i) = base (.site (.clock i))) (u : TeamSite.Port r k d) :
    installStacks finish base next (.site u) = base (.site u) := by
  cases u with
  | clock i => exact (installStacks_at finish_injective base next (.clock i)).trans (clock i)
  | _ => apply installStacks_outside; intro x; cases x <;> simp [finish]

/-- The Boolean condition tested by the endpoint's physical rows for the actual successor stream. -/
def valid (mode : Finish.Mode p) (last : Bool) (regs : Fin r → Word w) (elapsed : Word w)
    (candidate : List Bool) : Bool :=
  if last then mode.halted else decide ((Finish.frame mode regs elapsed).bits = candidate)

/-- At any inner-loop exit the physical sender compares its computed frame or checks finality.
It preserves *all* of the instruction loop's stacks for record closure and sorting. Its runtime
is bounded independently of the length and contents of a malformed successor guess. -/
theorem close_run (P : TeamOpcode.Program p r k a) (lib : Fin a → Macro Q Γ m g)
    (sg : Option Bool) (live : Option (Fin p)) (last : Bool)
    (pub : Fin k → Word w) (s : PrivateRAM.LogConfig w p r) (block left elapsed max : Word w)
    (stamp bits : List Bool) (base : Stacks (Port r k (m*g)))
    (hclock : ∀ i, base (.site (.clock i)) = banks pub s (TeamTapeHandoff.chargeRegisters block left elapsed 0) max stamp i)
    (payload : base .payload = []) (tmp : base .tmp = []) :
    ∃ t ≤ (7*r+40)*(w+1), ∃ out, StackRuns (replay (code P lib)) t
      (.loop last (.close sg live),bits) base
      (finishLabel sg (valid (closeMode live) last s.reg elapsed (base .outgoing)),bits) out ∧
      ∀ i, out (.site i) = base (.site i) := by
  let mode := closeMode live
  let core := banks pub s (TeamTapeHandoff.chargeRegisters block left elapsed 0) max stamp
  have enter : StackRuns (code P lib) 1 (.loop last (.close sg live)) base (.finish sg (.enter mode last)) base :=
    .cons (.goto rfl) (.nil ..)
  have ready := finish_ready base core hclock payload tmp
  cases last with
  | true =>
    have hf := finish_run P lib sg (Finish.last_run mode (Finish.bank core [] (base .outgoing))) base ready bits
    rw [installStacks_eq finish_injective base _ (congrFun ready)] at hf
    refine ⟨_, ?_, _, (replay_segment enter bits).trans hf, fun _ => rfl⟩
    nlinarith [Nat.zero_le r, Nat.zero_le w]
  | false =>
    obtain ⟨st, hr, preserves⟩ := Finish.successor_run mode pub s block left elapsed max stamp (base .outgoing)
    have hf := finish_run P lib sg hr base ready bits
    refine ⟨_, ?_, _, (replay_segment enter bits).trans hf, fun i =>
      finish_site base st (fun u => (preserves u).trans (hclock u).symm) i⟩
    have hm := min_le_left (1+(r+2)*w) (base .outgoing).length
    nlinarith [Nat.zero_le r, Nat.zero_le w]

/-- Installed startup for any verified incoming frame gives its precise physical bank, exit and
time bound. Incoming frame decoding and dispatch do not consume any signed choice. -/
theorem predecessor_run (P : TeamOpcode.Program p r k a) (lib : Fin a → Macro Q Γ m g)
    (last : Bool) (fits : p ≤ 2^w) (pub : Fin k → Word w) (f : TeamTapeHandoff.Frame w r)
    (H limit max : Word w) (suffix bits : List Bool) (base : Stacks (Port r k (m*g)))
    (ready : base ∘ startup = Startup.input pub H limit max (f.bits ++ suffix)) :
    ∃ t ≤ Startup.budget r w + 1, StackRuns (replay (code P lib)) t
      (.startup last (Startup.entry p r),bits) base (afterStartup last (Startup.result p f limit),bits)
      (installStacks startup base (Startup.decoded pub f H (Startup.remaining p f limit) max suffix)) := by
  obtain ⟨t, ht, hr⟩ := Startup.run p fits pub f H limit max suffix
  exact ⟨_, by omega, startup_run P lib last hr base ready bits⟩

/-- The public first processor enters the same signed loop at the public PC in two elementary
steps. The public register bank and incident suffix are preserved. -/
theorem first_run (P : TeamOpcode.Program p r k a) (lib : Fin a → Macro Q Γ m g)
    (last : Bool) (pub : Fin k → Word w) (pc : Fin p) (regs : Fin r → Word w)
    (H limit max : Word w) (suffix bits : List Bool) (base : Stacks (Port r k (m*g)))
    (ready : base ∘ startup =
      Startup.decoded pub (TeamTapeHandoff.initial (packed w pc.val) regs) H limit max suffix) :
    StackRuns (replay (code P lib)) 2 (.startup last (.first pc),bits) base
      (.loop last (.clock (some false) (.enter pc)),bits) base := by
  have run := Startup.first_run pub pc regs H limit max suffix
  have installed := startup_run P lib last run base ready bits
  rw [installStacks_eq startup_injective base _ (congrFun ready)] at installed
  exact installed

end TeamSite.Endpoint

end BorderVNP
end Computability
end OAI
