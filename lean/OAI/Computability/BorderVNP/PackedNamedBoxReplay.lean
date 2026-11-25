import OAI.Computability.BorderVNP.PackedNamedBoxRoster

/-! # The complete factor roster on a selected named inner history -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace PackedHistoryCircuit.Normalized.SourcePath.NamedRun

open Crossing Shortening Shortening.Adaptive Shortening.StaticRows Epoch Epoch.Round Cover
open Packing Packing.Inherited Packing.Inherited.BoxRoster CellSparse Diagonal.ExternalSew Diagonal.CellEntries
open scoped Classical BorderVNP.Epoch.Cube
attribute [local instance] portFintype
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

universe u
variable {D m b k : ℕ} [NeZero D] {K P : Type} [Field K] [Fintype P] {bits : P → ℕ}
    {e : PaidIdentity K D m} {h H ν : ℝ} {src : SourcePath b e h H ν} {last high : ℕ}
    {V E cap : ℕ → ℕ} {w : ℕ} {Extra : ℕ → Type u}
    {keep : ∀ j, src.NamedAt last high V E w P bits k Extra j → Prop} {hk : 0 < k}
    {nodes : ∀ i : Fin b, src.Node last high V E w k i}
    (r : src.NamedRun last high V E w cap keep hk nodes)
local notation3 "States" => NamedState.Admissible (src.NamedGood last high V E w cap keep)
variable (rows : r.program.SiteRows) (number : e.Entry → ℕ)
variable (rect : ∀ i : Fin b, V (i.val+1) = siteCapacity e (k*V i.val)
    (rosterSeeds src last high i))
variable (base : Fin (V 0) → List (List Factor))

/-- Every attained original histogram has the same public slot array, with
the actual original factors in the repeated input rows and all holes preserved. -/
theorem replayPrivatePrograms_roster (n : ℕ) (hn : n ≤ b) (flat : Fin (k^n) → States 0)
    (initial : ∀ z, Site.Programs (flat z).val.placed.pack.layout)
    (leaf : ∀ z, Realizes (flat z).val.names.sites (fun v => (initial z v).program.boxes) base)
    (q : (r.program.system.histories n hn (leavesEquiv k _ n flat)).Index) :
    let state := RowTrace.state r.program.system n hn (leavesEquiv k _ n flat) q
    let input := nestedPrivatePrograms (fun a : States 0 => a.val.placed.pack) n flat initial
    Realizes state.val.names.sites
      (fun v => (r.program.replayPrivatePrograms r.saveNames rows number n hn (leavesEquiv k _ n flat) input q v).program.boxes)
      (boxRoster (src := src) (last := last) (high := high) (k := k) (V := V) number rect base n) := by
  intro state input
  let valid := fun (n : ℕ) (x : States n) (pr : Site.Programs x.val.placed.pack.layout) =>
    Realizes x.val.names.sites (fun v => (pr v).program.boxes) (boxRoster (src := src) (last := last) (high := high) (k := k) (V := V) number rect base n)
  have start : Program.LeavesWithin (view := fun _ (a : States _) => a.val.placed) valid n (leavesEquiv k _ n flat) input :=
    Program.nestedLeaves_within (fun _ (a : States _) => a.val.placed) valid n flat initial leaf
  exact r.program.replayPrivatePrograms_invariant r.saveNames rows number valid
    (fun i c q old h => r.savePrivatePrograms_roster rows number rect base i c q old h) n hn _ input start q

/-- The actual terminal flatten keeps every prescribed public row at its native
site index, including unused slots and original private table references. -/
theorem flatPrivatePrograms_roster (flat : Fin (k^b) → States 0) (initial : ∀ z, Site.Programs (flat z).val.placed.pack.layout)
    (leaf : ∀ z, Realizes (flat z).val.names.sites (fun v => (initial z v).program.boxes) base)
    (q : r.program.Hist flat) :
    let state := RowTrace.state r.program.system b le_rfl (leavesEquiv k _ b flat) q
    Realizes state.val.names.sites
      (fun v => (r.program.flatPrivatePrograms r.saveNames rows number flat initial q v).program.boxes)
      (boxRoster (src := src) (last := last) (high := high) (k := k) (V := V) number rect base b) := by
  intro state
  exact r.replayPrivatePrograms_roster rows number rect base b le_rfl flat initial leaf q

end PackedHistoryCircuit.Normalized.SourcePath.NamedRun

end BorderVNP
end Computability
end OAI
