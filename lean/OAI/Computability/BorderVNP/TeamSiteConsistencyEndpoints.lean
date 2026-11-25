import OAI.Computability.BorderVNP.TeamSiteConsistencyPaths
import OAI.Computability.BorderVNP.TeamSiteConsistencyEndpointBounds
import OAI.Computability.BorderVNP.TeamSiteEndpointTimes

/-! # Direct local endpoint checks for a concrete team history

Each processor inspects its own guarded charged run, the actual handoff bytes and
the raw memory checks. On the last processor only the halt flag is tested. The
final timestamp, total clock, maximal burst and private choice length are recovered
from the physically checked instructions, with no access to a future native path.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamSiteConsistency.Setup

open VPVNP RAMTape RAMTape.PublicExprMachine TeamRAM TeamTapeHandoff TeamSite TeamContraction
open BurstRAM (Word)
variable {teams w p r k a e m g : ℕ} {Q Γ : Type}
variable (cfg : Setup teams w p r k a e)

/-- Prescribed public incoming state of the first physical processor. -/
def first : Frame w r := initial (packed w cfg.start.pc.val) cfg.start.reg

/-- Conditions observed locally at the raw endpoints. Their final halt-bit check
does not compare the cumulative timestamp against the complete event list. -/
def EndpointChecks (z : RawHistory teams r w e) : Prop :=
  (∀ j, EndpointRow cfg.program cfg.pub cfg.lib cfg.block cfg.limit cfg.cap
    (predecessor cfg.first z.frames j) (z.blocks j) (z.frames j)) ∧
  (∀ j, j.val+1 = teams → (z.frames j).halted = true) ∧
  z.WireChecks cfg.first cfg.input cfg.width cfg.sorter

private def finalIndex : Fin teams := ⟨teams-1,by have := cfg.positive; omega⟩

private theorem last_output (z : RawHistory teams r w e) :
    (List.ofFn z.frames).getLast? = some (z.frames cfg.finalIndex) := by
  have hne : List.ofFn z.frames ≠ [] := mt List.ofFn_eq_nil_iff.mp cfg.positive.ne'
  rw [List.getLast?_eq_some_getLast hne,List.getLast_ofFn]
  rfl

/-- The endpoint-only local verifier is equivalent to full physical-history validity,
and its true guards imply every one of the declared native resource bounds. -/
theorem endpointChecks_iff_fuel (z : RawHistory teams r w e) (lib : Fin a → Macro Q Γ m g) (fuel : ℕ)
    (hlib : cfg.lib = TeamSiteEvents.macros lib fuel) (clock : max 1 (fuel-1) ≤ cfg.privateClock) :
    cfg.EndpointChecks z ↔ let es := (List.ofFn z.blocks).flatten
      z.Valid cfg.program cfg.pub cfg.lib cfg.start cfg.block cfg.limit cfg.cap cfg.input cfg.width cfg.sorter
        es (es.map Event.choices) ∧ Within cfg.limit.val cfg.cap.val cfg.privateClock es := by
  let es := (List.ofFn z.blocks).flatten
  let j := cfg.finalIndex
  have endj : j.val+1 = teams := by dsimp [j,finalIndex]; have := cfg.positive; omega
  have last := cfg.last_output z
  have point := endpointRows_iff_pointwise cfg.program cfg.pub cfg.lib cfg.block cfg.limit cfg.cap cfg.first z.blocks z.frames
  constructor
  · rintro ⟨rows,halt,wires⟩
    have hs := point.mpr rows
    have hf := hs.final_frame (zero := rfl) last (halt j endj)
    have finalHalted : ∀ f, (List.ofFn z.frames).getLast? = some f → f.halted = true := by
      intro f he; rw [hf, Option.some.injEq] at he; subst f; rfl
    have charged := hs.charged cfg.pcs finalHalted
    have time := hs.last_elapsed last
    change (z.frames j).elapsed.val = 0+cost es at time
    have stop := (rows j).elapsed_cost.2
    have ne : List.ofFn z.blocks ≠ [] := mt List.ofFn_eq_nil_iff.mp cfg.positive.ne'
    have loc := hs.local_initial cfg.pcs ne finalHalted
    rw [hlib] at loc
    have choices := local_choice_bounds_pred cfg.program cfg.pub lib fuel loc
    refine ⟨⟨⟨rfl,charged,hf⟩,rfl,wires⟩,?_,endpoint_bursts hs,fun e he => (choices e he).trans clock⟩
    exact (Nat.zero_add _ ▸ time.symm).trans_le stop
  · rintro ⟨⟨⟨_,charged,hf⟩,_,wires⟩,_⟩
    refine ⟨point.mp charged.endpoints,?_,wires⟩
    intro i hi
    have eq : i = j := Fin.ext (by omega)
    subst i
    have he := Option.some.inj (last.symm.trans hf)
    rw [he]; rfl

/-- A same-clock form for callers already allowing the halting check in their
private choice envelope. -/
theorem endpointChecks_iff (z : RawHistory teams r w e) (lib : Fin a → Macro Q Γ m g)
    (hlib : cfg.lib = TeamSiteEvents.macros lib cfg.privateClock) (clock : 0 < cfg.privateClock) :
    cfg.EndpointChecks z ↔ let es := (List.ofFn z.blocks).flatten
      z.Valid cfg.program cfg.pub cfg.lib cfg.start cfg.block cfg.limit cfg.cap cfg.input cfg.width cfg.sorter
        es (es.map Event.choices) ∧ Within cfg.limit.val cfg.cap.val cfg.privateClock es :=
  cfg.endpointChecks_iff_fuel z lib cfg.privateClock hlib (by omega)

end TeamSiteConsistency.Setup

end BorderVNP
end Computability
end OAI
