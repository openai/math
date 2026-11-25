import OAI.Computability.BorderVNP.PackedInheritedWorkReturn
import OAI.Computability.BorderVNP.PackedHistoryNormalizedCompilation
import OAI.Computability.BorderVNP.PackedHistoryOuterPrivateSites

/-! # Returning the private program widths of the actual compiled site epoch -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace PackedHistoryCircuit.Normalized.EnrichedOuter.Boundary.Compilation

open Crossing Cover BorderVNP.Epoch BorderVNP.Epoch.Round Shortening Shortening.Adaptive Shortening.PublicCapacity
open Packing Packing.Inherited Packing.Inherited.WorkWords
open VPVNP.VerifierNetwork (Frame)
open scoped Classical BorderVNP.Epoch.Cube
attribute [local instance] portFintype
set_option maxHeartbeats 2000000

variable {D m : ℕ} [NeZero D] {K P : Type} [Field K] [Fintype P] {bits : P → ℕ}
    {e : PaidIdentity K D m} {S : SiteSchedule e} {shape : ℕ → Shape}
    {start T t w : ℕ} {budget V E cap : ℕ → ℕ}
    {deep : S.floor+1+S.drop*T ≤ start} {ht : t<T} {endShape : shape (t+1) = ⟨V S.rounds,E S.rounds⟩}
    {nodes : ∀ i : Fin S.rounds, S.source.Node S.last (S.high (offset S start t)) V E w S.fanIn i}
    (A : Compilation (bits := bits) deep ht budget V E cap w endShape nodes)

local notation "stagePins" => S.source.StatePins S.last (S.high (offset S start t)) V E w
local notation "outer" => Pins S start shape w
local notation "child" => WithWidths (outer t) (Shape.sites (shape t)) w
local notation "rootPins" => WithWidths (stagePins S.rounds) (V S.rounds) w

/-- The actual geometric post-frame with the two root width columns retained. -/
noncomputable def widthPost : Frame ((Fin (fan S) × child) ⊕ rootPins)
    (WithWidths (outer (t+1)) (shape (t+1)).sites w) := returnFrame A.post (congrArg Shape.sites endShape)

theorem widthPost_size : A.widthPost.size = A.post.size := returnFrame_size ..

/-- Geometric outputs of the width-augmented post-frame are the original assigned outputs. -/
theorem widthPost_geo (x : Fin (fan S) × child → Bool) (y : rootPins → Bool) (j : outer (t+1)) :
    A.widthPost.eval (Sum.elim x y) (.inl j) = A.post.eval (Sum.elim (fun a => x (a.1,.inl a.2)) (y ∘ Sum.inl)) j :=
  returnFrame_geom ..

variable (rows : A.epoch.F.SiteRows)
    (c : Fin (fan S) → Admissible (Good (S := S) (start := start) (bits := bits) (shape := shape) (w := w) budget) t)
    (old : ∀ i, Site.Programs (c i).val.pack.layout) (number : e.Entry → ℕ) (q : A.epoch.F.Hist (A.epoch.run c).flat)

/-- The precise last-stage programs before relabelling the ports and returning the site routes. -/
noncomputable def rootPrivate :=
  let F := A.epoch.F
  let flat := (A.epoch.run c).flat
  let nested := nestedPrivatePrograms (fun z => (A.epoch.view 0 z).pack) S.rounds flat
    (A.epoch.installedPrivatePrograms rows c old)
  F.replayPrivatePrograms A.epoch.saveNames rows number S.rounds le_rfl (leavesEquiv S.fanIn _ S.rounds flat) nested q

/-- Relabelling the external ports and changing the finite port enumeration preserve the
whole executable program at every physical site of this same histogram. -/
theorem widthPost_program (v : (A.epoch.term c q).val.pack.layout.Site) :
    (A.epoch.privatePrograms rows c old number q v).program = (A.rootPrivate rows c old number q v).program := rfl

/-- On the complete augmented root assignment, each occupied output word reads the work
or extent of the actual flattened program. Every vacant row retains its zero word. -/
theorem widthPost_covers (x : Fin (fan S) × child → Bool) (y : rootPins → Bool) (b : Bool)
    (read : WorkWords.Covers (((A.returned c).run.root q).val.names.sites)
      (fun v => let program := (A.rootPrivate rows c old number q v).program
                if b then program.size else program.work) (assignedColumn b) y) :
    WorkWords.Covers (A.epoch.term c q).val.rows.site
      (fun v => let program := (A.epoch.privatePrograms rows c old number q v).program
                if b then program.size else program.work) (assignedColumn b)
      (A.widthPost.eval (Sum.elim x y)) := by
  let p := flattenPack S.rounds (A.epoch.F.terminal (A.epoch.run c).flat q).pack
  let dir := ((A.returned c).run.root q).val.names
  let nativeRows : Rows ⟨V S.rounds,E S.rounds⟩ p.layout := (Terminal.boundaryRows dir).flatten
  let amount (v : p.layout.Site) := if b then (A.rootPrivate rows c old number q v).program.size
    else (A.rootPrivate rows c old number q v).program.work
  have h := returnFrame_covers (p := p) A.post x y endShape nativeRows amount b read
  change WorkWords.Covers ((A.returned c).rows q).site amount (assignedColumn b) (A.widthPost.eval (Sum.elim x y))
  rw [(A.returned c).rows_eq q]
  exact h

end PackedHistoryCircuit.Normalized.EnrichedOuter.Boundary.Compilation

end BorderVNP
end Computability
end OAI
