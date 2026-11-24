import OAI.Computability.VPVNP.RAMTapeSiteProcessorPorts

/-! # Recovering call-loop port names from the shared processor bank -/

namespace OAI
namespace Computability
namespace VPVNP

namespace RAMTape.SiteProcessorPorts

open BurstRAM LiveProgram

/-- Partial inverse of the shared aliases. A `none` identifies a guard or public
stack lying outside the call loop's image. -/
def origin (r k : ℕ) : SiteCutBank.Port → Option (SiteProcessor.Port r k)
  | .inr (.word .receive i) => if i = 1 then some (.credit (.budget .cost)) else
      if i = 2 then some (.isa .persistent) else none
  | .inr (.word .send i) => if i = 1 then some (.test (.word .targetCost)) else
      if i = 2 then some (.test (.word .targetState)) else none
  | .inr (.running .receive) => some (.test (.bit .running))
  | .inr (.running .send) => some (.test (.bit .targetRunning))
  | .inr .outPresent => some (.test (.bit .hasTarget))
  | .inl (.inr .fuel) => some (.credit .publicFuel)
  | .inl (.inr .globalCap) => some (.credit .globalCap)
  | .inl (.inr .callCredit) => some (.credit (.budget .site))
  | .inl (.inr .startCost) => some (.test (.word .lower))
  | .inl (.inr .endCost) => some (.test (.word .boundary))
  | .inl (.inr .addressWord) => some (.record (.field 1))
  | .inl (.inr .headerWord) => some (.record (.field 2))
  | .inl (.inl (.inr .zeros)) => some (.record .zeros)
  | .inl (.inl (.inr .remaining)) => some (.record .remaining)
  | .inl p => if p = ProcessorPublic.bucketPort then some (.credit .publicH) else none
  | _ => none

variable {k : ℕ} (r : ℕ) (expr : Fin k → PublicExpr)

private theorem external_origin (p : SiteProcessor.Port r k) :
    ∀ i, external r p = some i → origin r k i = some p := by
  have present {p : SiteProcessor.Port r k} {i : SiteCutBank.Port} (hi : external r p = some i)
      (h : origin r k i = some p) : ∀ j, external r p = some j → origin r k j = some p := by
    intro j hj
    rwa [← Option.some.inj (hi.symm.trans hj)]
  have absent {p : SiteProcessor.Port r k} (hp : external r p = none) :
      ∀ i, external r p = some i → origin r k i = some p := by simp [hp]
  cases p with
  | isa i => cases i <;> first | exact present rfl rfl | exact absent rfl
  | credit i =>
    cases i with
    | budget j => cases j <;> first | exact present rfl rfl | exact absent rfl
    | _ => first | exact present rfl rfl | exact absent rfl
  | test i =>
    cases i with
    | word j => cases j <;> first | exact present rfl rfl | exact absent rfl
    | bit j => cases j <;> exact present rfl rfl
    | _ => exact absent rfl
  | record i =>
    cases i with
    | field j =>
      by_cases h₁ : j = 1
      · subst j; exact present rfl rfl
      by_cases h₂ : j = 2
      · subst j; exact present rfl rfl
      exact absent (by simp [external, h₁, h₂])
    | _ => first | exact present rfl rfl | exact absent rfl
  | scratch _ => exact absent rfl

/-- Every two distinct logical ports of a call occupy different physical stacks. -/
theorem callPorts_injective : Function.Injective (callPorts r expr) := by
  intro p q h
  cases hp : external r p with
  | none =>
    cases hq : external r q with
    | none => simpa [callPorts, hp, hq, native] using h
    | some j => exact (native_ne_cut r expr p j (by simpa [callPorts, hp, hq] using h)).elim
  | some i =>
    cases hq : external r q with
    | none => exact (native_ne_cut r expr q i (by simpa [callPorts, hp, hq] using h.symm)).elim
    | some j =>
      have hij := cut_injective r expr (by simpa [callPorts, hp, hq] using h)
      subst j
      exact Option.some.inj ((external_origin r p i hp).symm.trans (external_origin r q i hq))

/-- Any public or guard register whose inverse entry is vacant survives an entire call. -/
theorem callPorts_ne_cut_of_origin_none (p : SiteProcessor.Port r k) (i : SiteCutBank.Port)
    (hi : origin r k i = none) : callPorts r expr p ≠ cut r expr i := by
  cases hp : external r p with
  | none => simpa [callPorts, hp] using native_ne_cut r expr p i
  | some j =>
    intro h
    have hji := cut_injective r expr (by simpa [callPorts, hp] using h)
    subst j
    simpa [hi] using external_origin r p i hp

end RAMTape.SiteProcessorPorts

end VPVNP
end Computability
end OAI
