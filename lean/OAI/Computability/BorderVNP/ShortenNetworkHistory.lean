import OAI.Computability.BorderVNP.ShortenNetworkCut
import Mathlib.Algebra.BigOperators.Fin

/-!
# Adaptive profile choices

An epoch may choose different charged cables, placements and profiles after
each previous choice. A path records public profiles, while the sums over
private wires stay inside the concrete networks at the leaves.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Shortening

open Crossing
open scoped BigOperators Classical

/-- A placed pack with its local coefficient tables and specified free ports. -/
structure Pack (D : ℕ) (P : Type*) (bits : P → ℕ) (R : Type*) where
  /-- The sites, cables and attachments in this pack. -/
  layout : Network D P bits
  /-- Local factors read their incident indices. -/
  table : layout.Tables R

variable {D : ℕ} {P : Type*} {bits : P → ℕ} {R : Type*} [CommSemiring R]

/-- Tensor on the surviving external connections. -/
noncomputable def Pack.tensor (p : Pack D P bits R) := p.layout.value p.table

/-- Local data supplied by a grouped shortening at a particular pack. -/
structure Replacement (p : Pack D P bits R) where
  /-- Cables selected by public geometry and previous choices. -/
  cables : Finset p.layout.Edge
  /-- Number of joint profiles of the matched bundles. -/
  count : ℕ
  /-- Wiring of each profile between the retained endpoint slots. -/
  profile : Fin count → Network D (p.layout.CutPorts cables) (p.layout.cutWidths cables)
  /-- Local tables in the profile wiring, including selector constraints. -/
  entry : ∀ i, (profile i).Tables R
  /-- The grouped identity on all exposed strings before attaching exterior factors. -/
  joint : ∀ s, p.layout.cutEquality cables s = ∑ i, (profile i).value (entry i) s

/-- The pack obtained by actual cable removal and insertion of a profile network. -/
noncomputable def Replacement.branch {p : Pack D P bits R} (r : Replacement p)
    (i : Fin r.count) : Pack D P bits R where
  layout := (p.layout.cut r.cables).sew (r.profile i)
  table := (p.layout.cut r.cables).sewTables (r.profile i)
    (p.layout.cutTables r.cables p.table) (r.entry i)

/-- A replacement preserves the tensor as an ordinary finite sum. -/
theorem Replacement.sum_branches {p : Pack D P bits R} (r : Replacement p) (x : Ports bits) :
    p.tensor x = ∑ i, (r.branch i).tensor x :=
  p.layout.value_replace r.cables p.table r.profile r.entry r.joint x

/-- A finite tree of adaptive replacements, indexed by the current pack.
Each successor's wiring can depend on the complete profile path leading to it. -/
inductive History : Pack D P bits R → Type _ where
  /-- Stop with the current concrete network. -/
  | stop (p : Pack D P bits R) : History p
  /-- Apply an exact change of representation, such as splitting a cable into
  ordered intervals, without adding a choice to the public path. -/
  | refinePack {p q : Pack D P bits R} (eq : ∀ x, p.tensor x = q.tensor x)
      (next : History q) : History p
  /-- Perform a replacement and continue independently along every profile branch. -/
  | step {p : Pack D P bits R} (r : Replacement p)
      (next : ∀ i : Fin r.count, History (r.branch i)) : History p

/-- One output network per full profile path, retaining multiplicities. -/
noncomputable def History.outputs {p : Pack D P bits R} : History p → List (Pack D P bits R)
  | .stop q => [q]
  | .refinePack _ next => next.outputs
  | .step r next => (List.ofFn (fun i : Fin r.count => (next i).outputs)).flatten

/-- The tensor of a finite pack equals the ordinary sum of the tensors of
its output packs, even when the replacement at a successor cuts selector
cables introduced along its own profile path. -/
theorem History.sum_outputs {p : Pack D P bits R} (history : History p) (x : Ports bits) :
    p.tensor x = (history.outputs.map (fun q => q.tensor x)).sum := by
  induction history with
  | stop q => simp [outputs]
  | refinePack eq _ ih => exact (eq x).trans ih
  | step r next ih =>
    rw [r.sum_branches x]
    simp only [outputs, List.map_flatten, List.sum_flatten, List.map_ofFn, List.sum_ofFn]
    exact Finset.sum_congr rfl fun i _ => ih i

end Shortening

end BorderVNP
end Computability
end OAI
