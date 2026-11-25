import OAI.Computability.BorderVNP.PackedCompleteRouteSubdivision
import OAI.Computability.BorderVNP.PackedCompleteInnerHistory
import OAI.Computability.BorderVNP.PackedHistoryNormalizedProcessor
import OAI.Computability.BorderVNP.PackedHistoryBounds

/-! # The actual crossing widths of every returned compiled boundary -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace PackedHistoryCircuit.Normalized

open Crossing BorderVNP.Epoch BorderVNP.Epoch.Round Cover Shortening Packing Adaptive PublicCapacity
open scoped Classical BorderVNP.Epoch.Cube
attribute [local instance] portFintype

universe u
variable {D m : ℕ} [NeZero D] {K : Type u} [Field K] {e : PaidIdentity K D m} {S : SiteSchedule e}
    {start T : ℕ} {P : Type} [Fintype P] {bits : P → ℕ}

namespace EnrichedOuter.Boundary

variable {t : ℕ} {shape : ℕ → Shape} {deep : S.floor+1+S.drop*T ≤ start} {ht : t<T}
    {budget V E cap : ℕ → ℕ} {w : ℕ} {endShape : shape (t+1) = ⟨V S.rounds,E S.rounds⟩}
    {nodes : ∀ i : Fin S.rounds, S.source.Node S.last (S.high (offset S start t)) V E w S.fanIn i}
    (C : Compilation (bits := bits) deep ht budget V E cap w endShape nodes)
    (c : Fin (fan S) → Admissible (Good (S := S) (start := start) (bits := bits) (shape := shape) (w := w) budget) t)

/-- The node's input subdivision, each installed motion, and the selected terminal rounding
turn complete incoming routes into an exact outgoing charge mask on this particular histogram. -/
theorem Compilation.exactCrossings (hc : ∀ i, (c i).val.route.CoversCrossings)
    (q : (C.epoch.choice c).Index) : ((C.epoch.choice c).term q).val.route.ExactCrossings := by
  let run := C.epoch.run c
  have leaf (i : Fin (fan S)) : (run.flat i).val.placed.CoversCrossings := by
    let initial := run.initialSites i
    have pre : (routes deep ht c i).CoversCrossings :=
      SiteRoutes.CoversCrossings.reindex _ (hc i) _
    have charge : initial.routes.CoversCrossings :=
      SiteRoutes.CoversCrossings.of_heq (p := (c i).val.pack) (p' := initial.pack) (routes deep ht c i)
        initial.routes (S.start_level _) (run.originalPack i) (run.originalRoutes i) pre
    rw [show (run.flat i).val.placed = initial.routes.initialPlacedPack S.radius_pos from initial.realizes]
    exact initial.routes.initialPlaced_coversCrossings S.radius_pos charge
  have terminal := C.program.terminal_coversCrossings run.flat leaf q
  have mask : (run.output.out q).routes.flatten.ExactCrossings :=
    fun a => run.active_iff_crossing q terminal a
  let s := (run.output.out q).routes.flatten
  have transport {a z : ℕ} {p : Pack D (Port (fan S) P (t+1)) (width bits (fan S) (t+1)) K}
      (eqn : a = z) (r : SiteRoutes p (Cube D) a S.budget) (mask : r.ExactCrossings) :
      (reindexRoutes eqn r).ExactCrossings := by subst z; exact mask
  exact transport (levels S deep ht).2.1 s mask

end EnrichedOuter.Boundary

namespace SelectedSchedule

open EnrichedOuter

variable {deep : S.floor+1+S.drop*T ≤ start} {budget : ℕ → ℕ} {cap : ℕ → ℕ → ℕ} {w : ℕ}
    (C : Compiled bits deep budget cap w)
    (bottom : Admissible (Boundary.Good (S := S) (start := start) (bits := bits)
      (shape := boundaryShape S start) (w := w) budget) 0)

/-- Every attained boundary of the selected named processor marks exactly its genuine
crossing cables when the original seed uses its physical nonlocal mask. -/
theorem Compiled.history_exactCrossings (seed : bottom.val.route.ExactCrossings) (j : ℕ)
    (q : (packHistory bottom C.machine.epoch j).Index) :
    ((packHistory bottom C.machine.epoch j).term q).val.route.ExactCrossings := by
  refine history_induction bottom C.machine.epoch (fun _ z => z.val.route.ExactCrossings) seed ?_ j q
  intro t c hc
  by_cases ht : t<T
  · rw [show C.machine.epoch t c = (C.atLevel t ht).epoch.choice c from dite_eq_left ht]
    exact (C.atLevel t ht).exactCrossings c (fun i a => (hc i a).2)
  · let empty : ProfileSum (Admissible (Boundary.Good (S := S) (start := start) (bits := bits)
        (shape := boundaryShape S start) (w := w) budget) (t+1)) := ⟨Empty,inferInstance,Empty.elim⟩
    rw [show C.machine.epoch t c = empty from dite_eq_right ht]
    exact fun a => Empty.elim a

/-- The measured nonlocal width in the decay theorem counts every crossing of the actual
flattened terminal layout, exactly once per cable and with its full stored width. -/
theorem Compiled.history_intercellWidth (seed : bottom.val.route.ExactCrossings) (j : ℕ)
    (q : (packHistory bottom C.machine.epoch j).Index) :
    let z := ((packHistory bottom C.machine.epoch j).term q).val
    (Diagonal.ExternalSew.intercellWidth (flattenPack j z.pack).layout
      (fun v => reduceMove (depth S start j) (z.route.origin v)) : ℝ) = z.route.nonlocalWidth :=
  ((packHistory bottom C.machine.epoch j).term q).val.route.intercellWidth_eq (C.history_exactCrossings bottom seed j q)

end SelectedSchedule
end PackedHistoryCircuit.Normalized

end BorderVNP
end Computability
end OAI
