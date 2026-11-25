import OAI.Computability.BorderVNP.PackedCompiledEpochBoxRoster
import OAI.Computability.BorderVNP.PackedOuterBoxRoster
import OAI.Computability.BorderVNP.PackedHistoryNormalizedProcessor
import OAI.Computability.BorderVNP.PackedSelectedEpochNodeFrames

/-! # The padded box roster on the selected schedule

Starting from the initial factor tables, each epoch extends the site array
with relay slots and appends the scheduled template rectangles. Every private
history of the selected machine realizes this array at its physical site rows.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace PackedHistoryCircuit.Normalized.SelectedSchedule

open Crossing Cover BorderVNP.Epoch BorderVNP.Epoch.Round Shortening Shortening.Adaptive
open Packing Packing.Inherited PublicCapacity EnrichedOuter CellSparse Diagonal.ExternalSew
open scoped Classical BorderVNP.Epoch.Cube
attribute [local instance] portFintype
set_option maxHeartbeats 2000000
set_option maxRecDepth 3000

variable {D m : ℕ} [NeZero D] {K : Type} [Field K] {e : PaidIdentity K D m}
    (S : SiteSchedule e) (start : ℕ) (number : e.Entry → ℕ)
    (initialRoster : Fin (boundaryShape S start 0).sites → List (List Factor))

/-- Fixed table bodies on the full outer site rectangle, including every unused slot. -/
noncomputable def historyRoster : (t : ℕ) → Fin (boundaryShape S start t).sites → List (List Factor)
  | 0 => initialRoster
  | t+1 => BoxRoster.steps (b := S.rounds) (k := S.fanIn) (V := fun j => (before S start t j).sites)
      e number (fun i => seedCount S start t i.val) (fun _ => rfl)
      (BoxRoster.subdivided (s := boundaryShape S start t) (interiors S)
        (historyRoster t)) S.rounds

omit [NeZero D] in
private theorem steps_congr {b k : ℕ} {V : ℕ → ℕ} {n₁ n₂ : Fin b → ℕ} (h : n₁ = n₂)
    (r₁ : ∀ i, V (i.val+1) = StaticRows.siteCapacity e (k*V i.val) (n₁ i))
    (r₂ : ∀ i, V (i.val+1) = StaticRows.siteCapacity e (k*V i.val) (n₂ i))
    (base : Fin (V 0) → List (List Factor)) :
    BoxRoster.steps e number n₁ r₁ base = BoxRoster.steps e number n₂ r₂ base := by
  subst n₂
  rfl

variable {S start} {P : Type} [Fintype P] {bits : P → ℕ} {T w : ℕ}
    {deep : S.floor+1+S.drop*T ≤ start} {budget : ℕ → ℕ} {cap : ℕ → ℕ → ℕ}

/-- Every attained history realizes the same scheduled table roster as the initial
tables propagate through the actual private programs and returned site directories. -/
theorem Compiled.historyBoxRoster (C : Compiled bits deep budget cap w)
    (rows : ∀ n hn, (C.machine n hn).F.SiteRows) (number : e.Entry → ℕ)
    (bottom : Admissible (Boundary.Good (S := S) (start := start) (bits := bits)
      (shape := boundaryShape S start) (w := w) budget) 0)
    (base : Site.Programs bottom.val.pack.layout)
    (initialRoster : Fin (boundaryShape S start 0).sites → List (List Factor))
    (initial : BoxRoster.Realizes bottom.val.rows.site (fun v => (base v).program.boxes) initialRoster)
    (t : ℕ) (ht : t ≤ T) (q : (packHistory bottom C.machine.epoch t).Index) :
    BoxRoster.Realizes ((packHistory bottom C.machine.epoch t).term q).val.rows.site
      (fun v => (C.machine.historyPrivatePrograms rows number bottom base t ht q v).program.boxes)
      (historyRoster S start number initialRoster t) := by
  refine C.machine.historyPrivatePrograms_roster rows number (historyRoster S start number initialRoster)
    bottom base initial ?_ t ht q
  intro n hn c old previous z
  let oldRoster := historyRoster S start number initialRoster n
  let extended := BoxRoster.subdivided (s := boundaryShape S start n) (interiors S) oldRoster
  let native := SourcePath.NamedRun.rosterSeeds S.source S.last (S.high (offset S start n))
  have counts : native = fun i => seedCount S start n i.val := funext (stageSeeds_offset S deep hn)
  have rect (i : Fin S.rounds) : (before S start n (i.val+1)).sites =
      StaticRows.siteCapacity e (S.fanIn*(before S start n i.val).sites) (native i) := by
    rw [congrFun counts i]
    rfl
  have step := (C.atLevel n hn).epochBoxRoster (rows n hn) number rect c old oldRoster previous z
  have agree := steps_congr (k := S.fanIn) (V := fun j => (before S start n j).sites)
    number counts rect (fun _ => rfl) extended
  change BoxRoster.Realizes _ _ (BoxRoster.steps (k := S.fanIn) (V := fun j => (before S start n j).sites)
    e number (fun i : Fin S.rounds => seedCount S start n i.val) (fun _ => rfl) extended S.rounds)
  rw [← agree]
  exact step

end PackedHistoryCircuit.Normalized.SelectedSchedule

end BorderVNP
end Computability
end OAI
