import OAI.Computability.BorderVNP.PackedCompiledInputBoxRoster
import OAI.Computability.BorderVNP.PackedNamedBoxReplay

/-! # The public box roster on every return of a compiled outer epoch

The native histogram consumes the subdivided child array and fills the fixed
rectangles of its paid templates. Its returned site numbers preserve this
array across the final port flattening.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace PackedHistoryCircuit.Normalized.EnrichedOuter.Boundary.Compilation

open Crossing Cover BorderVNP.Epoch BorderVNP.Epoch.Round Shortening Shortening.Adaptive Shortening.PublicCapacity
open Shortening.StaticRows Packing Packing.Inherited CellSparse
open scoped Classical
attribute [local instance] portFintype
set_option maxHeartbeats 2000000
set_option maxRecDepth 3000

private theorem returnedRoster {D : ℕ} {K : Type*} {P : Type} {bits : P → ℕ} (p : Pack D P bits K)
    {s s' : Shape} (hs : s' = s) (rows : Rows s p.layout)
    {body : p.layout.Site → List (List Factor)} {known : Fin s.sites → List (List Factor)}
    (h : BoxRoster.Realizes rows.site body known) :
    BoxRoster.Realizes (returnedRows (p := p) hs rows).site body (known ∘ finCongr (congrArg Shape.sites hs)) := by
  subst s'
  exact h

variable {D m start T t w : ℕ} [NeZero D] {K P : Type} [Field K] [Fintype P] {bits : P → ℕ}
    {e : PaidIdentity K D m} {S : SiteSchedule e} {shape : ℕ → Shape}
    {deep : S.floor+1+S.drop*T ≤ start} {ht : t<T} {budget V E cap : ℕ → ℕ}
    {endShape : shape (t+1) = ⟨V S.rounds,E S.rounds⟩}
    {nodes : ∀ i : Fin S.rounds, S.source.Node S.last (S.high (offset S start t)) V E w S.fanIn i}
    (A : Compilation (bits := bits) deep ht budget V E cap w endShape nodes)

local notation "d" => offset S start t
local notation "counts" => SourcePath.NamedRun.rosterSeeds S.source S.last (S.high d)

/-- Every actual histogram of the compiled outer epoch returns the same public
roster when all children realize the given padded input roster. -/
theorem epochBoxRoster (rows : A.epoch.F.SiteRows) (number : e.Entry → ℕ)
    (rect : ∀ i : Fin S.rounds, V (i.val+1) = siteCapacity e (S.fanIn*V i.val) (counts i))
    (c : Fin (fan S) → Admissible (Good (S := S) (start := start) (bits := bits) (shape := shape) (w := w) budget) t)
    (old : ∀ i, Site.Programs (c i).val.pack.layout)
    (known : Fin (shape t).sites → List (List Factor))
    (hprev : ∀ i, BoxRoster.Realizes (c i).val.rows.site (fun v => (old i v).program.boxes) known)
    (q : A.epoch.F.Hist (A.epoch.run c).flat) :
    BoxRoster.Realizes (A.epoch.term c q).val.rows.site
      (fun v => (A.epoch.privatePrograms rows c old number q v).program.boxes)
      (SourcePath.NamedRun.boxRoster (src := S.source) (last := S.last) (high := S.high d)
        (k := S.fanIn) (V := V) number rect
        (BoxRoster.subdivided ⌈S.budget/S.radius⌉₊ known ∘ finCongr (A.input c).siteWidth) S.rounds
        ∘ finCongr (congrArg Shape.sites endShape)) := by
  let flat := (A.epoch.run c).flat
  let initial := A.epoch.installedPrivatePrograms rows c old
  let input := BoxRoster.subdivided ⌈S.budget/S.radius⌉₊ known ∘ finCongr (A.input c).siteWidth
  have leaf := fun i => A.installedBoxRoster rows c old i known (hprev i)
  have root := A.program.flatPrivatePrograms_roster rows number rect input flat initial leaf q
  let p := flattenPack S.rounds (A.epoch.F.terminal flat q).pack
  let dir := ((A.returned c).run.root q).val.names
  let nativeRows : Rows ⟨V S.rounds,E S.rounds⟩ p.layout := (Terminal.boundaryRows dir).flatten
  change BoxRoster.Realizes ((A.returned c).rows q).site _ _
  rw [(A.returned c).rows_eq q]
  exact returnedRoster p endShape nativeRows root

end PackedHistoryCircuit.Normalized.EnrichedOuter.Boundary.Compilation

end BorderVNP
end Computability
end OAI
