import OAI.Computability.BorderVNP.TeamSiteEndpointLive

/-!
# Actual rejecting instruction-loop paths at a live processor

An explicit loop rejection is redirected to the invalid endpoint. An internal
callback may halt and reject at its own label. Both cases consume precisely the
loop's choice prefix, and neither can reach a verified zero-weight endpoint.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamSite.Endpoint

open VPVNP RAMTape BurstRAM RAMTape.PublicExprMachine TeamPrivateFragment TeamLocalClock TeamTapeHandoff

variable {w p r k a m g : ℕ} {Q Γ : Type}

/-- Redirect the explicit reject label, or retain an internal rejecting callback halt.
A verified zero-weight close is excluded by its observable close label. -/
theorem loop_terminal (P : TeamOpcode.Program p r k a) (lib : Fin a → Macro Q Γ m g)
    (last : Bool) (q : TeamSite.Loop.Label P Q m g) (h : TeamSite.Loop.code P lib q = .halt false)
    (bad : ∀ sg live, q ≠ .close sg live) (base : Stacks (Port r k (m*g))) (bits : List Bool) :
    ∃ t ≤ 1, ∃ z, StackRuns (replay (code P lib)) t (.loop last q,bits) base (z,bits) base ∧
      code P lib z = .halt false ∧ ∀ sg, z ≠ .done sg := by
  by_cases reject : q = .reject
  · subst q
    exact ⟨1,le_rfl,.invalid,loop_reject P lib last base bits,rfl,fun _ he => by contradiction⟩
  · refine ⟨0,Nat.zero_le _,.loop last q,.nil ..,?_,fun _ he => by contradiction⟩
    have row : code P lib (.loop last q) = (TeamSite.Loop.code P lib q).rename Port.site (Label.loop last) := by
      cases q with
      | reject => contradiction
      | close sg live => exact False.elim (bad sg live rfl)
      | _ => rfl
    rw [row,h]; rfl

/-- Decode the actual live incoming frame, replay the complete rejecting instruction
prefix and retain exactly its unused choices. The terminal is distinct from every
successful finish, including a zero-weight private return. -/
theorem live_reject (P : TeamOpcode.Program p r k a) (lib : Fin a → Macro Q Γ m g)
    (last : Bool) (fits : p ≤ 2^w) (pub : Fin k → Word w) (start : TeamOpcode.State w p r)
    (H limit elapsed max : Word w) (safe : elapsed ≤ limit) (suffix script rest : List Bool)
    (base : Stacks (Port r k (m*g)))
    (ready : base ∘ startup =
      Startup.input pub H limit max ((Frame.live (packed w start.pc.val) start.reg elapsed).bits ++ suffix))
    (steps : ℕ) (q : TeamSite.Loop.Label P Q m g) (final : Stacks (TeamSite.Port r k (m*g)))
    (run : StackRuns (replay (TeamSite.Loop.code P lib)) steps
      (.clock (some false) (.enter start.pc),script)
      (installStacks TeamSite.Port.clock (base ∘ Port.site)
        (TeamLocalClock.bank pub start H (packed w (limit.val-elapsed.val)) elapsed max)) (q,rest) final)
    (halt : TeamSite.Loop.code P lib q = .halt false) (bad : ∀ sg live, q ≠ .close sg live) :
    ∃ t ≤ Startup.budget r w + 1 + steps + 1, ∃ z out, StackRuns (replay (code P lib)) t
      (.startup last (Startup.entry p r),script) base (z,rest) out ∧ code P lib z = .halt false ∧
      (∀ sg, z ≠ .done sg) ∧ ∀ i, out (.site i) = final i := by
  let f := Frame.live (packed w start.pc.val) start.reg elapsed
  let decoded := Startup.decoded pub f H (packed w (limit.val-elapsed.val)) max suffix
  let mid := installStacks startup base decoded
  obtain ⟨t,ht,first⟩ := predecessor_run P lib last fits pub f H limit max suffix script base ready
  have hv : (packed w start.pc.val).val = start.pc.val := packed_val (lt_of_lt_of_le start.pc.isLt fits)
  have hl : TeamLocalClockPC.lookup p start.pc.val = .live start.pc := by
    simpa only [hv] using TeamLocalClockPC.lookup_packed start.pc fits
  simp only [f, Startup.result, Frame.elapsed, safe, ite_true, hl, afterStartup, Startup.remaining,
    hv, start.pc.isLt, and_self] at first
  have hmid := startup_site base pub start.pc (packed w start.pc.val) start.reg H
    (packed w (limit.val-elapsed.val)) elapsed max suffix
  have body := loop_segment P lib last run mid hmid
  obtain ⟨u,hu,z,hr,hz,distinct⟩ := loop_terminal P lib last q halt bad (installStacks Port.site mid final) rest
  exact ⟨t+steps+u,by omega,z,_,(first.trans body).trans hr,hz,distinct,
    fun i => installStacks_at (fun _ _ he => Port.site.inj he) mid final i⟩

end TeamSite.Endpoint

end BorderVNP
end Computability
end OAI
