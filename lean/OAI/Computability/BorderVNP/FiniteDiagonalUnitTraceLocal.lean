import OAI.Computability.BorderVNP.FiniteDiagonalUnitTraceProduct
import OAI.Computability.BorderVNP.DiagonalNativeUnitPacket

/-! # Reindexing the bounded unit traces of one physical processor

At a zero reference tag the startup and unit test are deterministic on actual
memory. The unique accepting trace exists exactly at the prescribed pin and
incident exterior condition. Its native field weight is one.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace FiniteDiagonal

open VPVNP BurstRAM TeamContraction RoutingISA RoutingISA.Evaluator RoutingISA.Pins
open scoped Classical

variable {w m g : ℕ} {Q Γ : Type} {K : Type*} [Field K]

open private withoutAccept from OAI.Computability.BorderVNP.DiagonalNativeUnitStartup

/-- The unique bounded successful trace of a zero-tag execution represents the
truth of its physical test and carries field value one. -/
theorem unitTrace_of_test {L : Layout} (fields : ProcessorFields L) (pub : Arg → Word w)
    (bank : Bank w) (eval : Code) (fallsThrough : eval.withoutAccept = true)
    (lib : Fin 8 → TeamSite.Macro Q Γ m g) (ret : FieldProcessor.Returns Q Γ K m 8) (fuel : ℕ)
    {ct ticks burst clock : ℕ} (budget : ct ≤ ticks) {ok : Prop} {post : NatState → Prop}
    (test : TestRun pub (TeamSiteEvents.macros lib fuel) (withStartup eval)
      bank (processorMemory fields w) ct ok post)
    (zero : ∀ {es t mt}, Runs pub (TeamSiteEvents.macros lib fuel) (withStartup eval)
      bank (processorMemory fields w) es t mt → Runs pub (TeamSiteEvents.macros lib fuel)
      (withStartup unit) bank (processorMemory fields w) es t mt) :
    let M := processorMachine (withStartup eval) pub (TeamSiteEvents.macros lib fuel) bank fields
    Nonempty (NativePath M ticks burst clock ≃ PLift ok) ∧
      ∀ p : NativePath M ticks burst clock,
        FieldProcessor.pathProduct (withStartup eval).program pub lib ret fuel ⟨0,bank⟩ p.val = 1 := by
  intro M
  have runs (p : NativePath M ticks burst clock) : ∃ t mt, Runs pub (TeamSiteEvents.macros lib fuel)
      (withStartup eval) bank (processorMemory fields w) p.val t mt :=
    ((Code.execute_iff_runs (withoutAccept fallsThrough)).mp p.property.1).1
  have yes (p : NativePath M ticks burst clock) : ok := by
    obtain ⟨_,_,run⟩ := runs p
    exact (test.sound run).1
  refine ⟨⟨Equiv.ofBijective (fun p => (⟨yes p⟩ : PLift ok)) ⟨?_,?_⟩⟩,?_⟩
  · intro p q _
    obtain ⟨_,_,rp⟩ := runs p
    obtain ⟨_,_,rq⟩ := runs q
    exact Subtype.ext ((zero rp).unique_of_deterministic (by decide) (zero rq)).1
  · intro h
    obtain ⟨es,t,mt,run,_,_⟩ := test.complete h.down
    have lim := (startup_unit_effects eval test zero ⟨(es,t,mt),run⟩).1
    exact ⟨⟨es, run.execute, lim.cost.trans budget, fun e he => (lim.length e he).trans (Nat.zero_le _),
      fun e he => (lim.choices e he).trans (Nat.zero_le _)⟩,Subsingleton.elim ..⟩
  · intro p
    obtain ⟨_,_,run⟩ := runs p
    exact startup_unit_pathProduct eval lib ret fuel run (zero run)

end FiniteDiagonal

end BorderVNP
end Computability
end OAI
