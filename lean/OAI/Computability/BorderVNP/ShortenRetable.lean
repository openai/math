import OAI.Computability.BorderVNP.ShortenPlacedStep
import OAI.Computability.BorderVNP.CrossingDescent

/-! # Replaying a public geometric step after specialization

A placed pack has quotient coordinates, charged wires and midpoints that
are independent of its scalar tables. The fixed geometric program can
choose its moves on reference-field packs and the finite field can use
those very choices on the same public layouts.
-/

namespace OAI
namespace Computability
namespace BorderVNP

set_option maxHeartbeats 2000000

namespace Shortening

open Crossing Epoch CombiningStep
open scoped Classical

variable {D d next k m : ℕ} {P I B : Type} [Fintype I] [Fintype B] {bits : P → ℕ}
variable {K E : Type*}

/-- Give a publicly placed pack new scalar tables on its existing layout. -/
def PlacedPack.retable (p : PlacedPack D P bits K I d) (t : p.pack.layout.Tables E) :
    PlacedPack D P bits E I d where
  pack := ⟨p.pack.layout,t⟩
  site := p.site
  charged := p.charged
  midpoint := p.midpoint

variable [Field K] [Field E] [NeZero D] {child : Fin k → PlacedPack D P bits K I d}
variable (step : PlacedStep m B next child) (t : ∀ i, (child i).pack.layout.Tables E)

/-- Retain the chosen bin, permutation, orientation and quotient charts on
every old wire, including the selected lifts at both ends of each seed. -/
noncomputable def PlacedStep.retable : PlacedStep m B next (fun i => (child i).retable (t i)) where
  bin := step.bin
  perm := step.perm
  positive := step.positive
  placed := ⟨step.placed.old,step.placed.chart,step.placed.project,step.placed.lift,
    step.placed.nonexpanding,step.placed.projects,step.placed.bin_length,step.placed.invariant⟩

variable (e : PaidIdentity K D m) (y : e.Entry → E)
variable (hy : ∀ f : MvPolynomial e.Entry ℤ,
  MvPolynomial.eval₂Hom (Int.castRingHom K) e.entry f = 0 →
    MvPolynomial.eval₂Hom (Int.castRingHom E) y f = 0)

/-- A reduction keeps the entire original geometric output on each attained
histogram. Only the scalar tables are replaced. -/
theorem PlacedStep.retable_result (q : step.Index e) :
    (step.retable t).result (e.specialize y hy) q =
      (step.result e q).retable ((step.retable t).result (e.specialize y hy) q).pack.table := rfl

/-- Hence the same charge and concentration estimates apply over the
selected finite field, using the original reference-field constants. -/
theorem PlacedStep.retable_measures (q : step.Index e) :
    ((step.retable t).result (e.specialize y hy) q).length = (step.result e q).length ∧
    ((step.retable t).result (e.specialize y hy) q).concentration = (step.result e q).concentration :=
  ⟨rfl,rfl⟩

end Shortening

end BorderVNP
end Computability
end OAI
