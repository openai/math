import OAI.Computability.BorderVNP.PackedProgramBoxRoster
import OAI.Computability.BorderVNP.PackedHistoryCompilerRows
import OAI.Computability.BorderVNP.PackedHistoryPrivateNamedRows
import OAI.Computability.BorderVNP.PackedInheritedWorkNames
import OAI.Computability.BorderVNP.PackedHistoryLeafPrograms

/-! # The fixed table roster at the actual saved named rows

A public rectangle carries the same site ordinals across a dense cable save.
The next fixed roster repeats the child rectangle and appends every seed's
immutable factor table. This construction is independent of the histogram.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace PackedHistoryCircuit.Normalized.SourcePath.NamedRun

open Crossing Shortening Shortening.Adaptive Shortening.StaticRows Shortening.PublicParallel Epoch Epoch.Round
open Cover Packing Packing.Inherited Packing.Inherited.BoxRoster CellSparse Diagonal.ExternalSew Diagonal.CellEntries
open scoped Classical BorderVNP.Epoch.Cube
attribute [local instance] portFintype
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

private theorem savedRoster {D d ns ne : ℕ} {K P : Type}
    {fin fin' : Fintype P} {bits : P → ℕ} (p saved : PlacedPack D P bits K (Cube D) d)
    (dir : Directory p ns ne) (dst : Directory saved ns ne) (stored : saved = p.dense dir.cables)
    (ids : HEq dst dir.dense) (old : @Site.Programs D P fin bits p.pack.layout)
    (known : Fin ns → List (List Factor))
    (h : Realizes dir.sites (fun v => (old v).program.boxes) known) :
    Realizes dst.sites (fun v => (carryPrivatePrograms p saved dir.cables stored (fin := fin) (fin' := fin') old v).program.boxes) known := by
  subst saved
  obtain rfl := eq_of_heq ids
  exact h

universe u
variable {D m b k : ℕ} [NeZero D] {K P : Type} [Field K] [Fintype P] {bits : P → ℕ}
    {e : PaidIdentity K D m} {h H ν : ℝ} {src : SourcePath b e h H ν} {last high : ℕ}
    {V E cap : ℕ → ℕ} {w : ℕ} {Extra : ℕ → Type u}
    {keep : ∀ j, src.NamedAt last high V E w P bits k Extra j → Prop} {hk : 0<k}
    {nodes : ∀ i : Fin b, src.Node last high V E w k i}
    (r : src.NamedRun last high V E w cap keep hk nodes)
/-- Exact number of complete public template populations at each inner level. -/
noncomputable def rosterSeeds (src : SourcePath b e h H ν) (last high : ℕ) (i : Fin b) : ℕ :=
  Fintype.card (Shortening.PublicDenseReceipt.Seed (src.pattern i).bins (src.asPath.depth last high (i.val+1)))

local notation3 "States" => NamedState.Admissible (src.NamedGood last high V E w cap keep)

variable (rows : r.program.SiteRows) (number : e.Entry → ℕ)
variable (rect : ∀ i : Fin b, V (i.val+1) = siteCapacity e (k*V i.val) (rosterSeeds src last high i))
variable (base : Fin (V 0) → List (List Factor))

/-- Publicly fixed factor arrays on the consecutive named rectangles. The
initial array may contain the supplied opaque original factors. -/
noncomputable abbrev boxRoster : (j : ℕ) → Fin (V j) → List (List Factor) := BoxRoster.steps (b := b) (k := k) (V := V) e number (rosterSeeds src last high) rect base

/-- Exact all-slot table roster after the actual named program's second
stable save, under its attained histogram. -/
theorem savePrivatePrograms_roster (i : Fin b) (c : Fin k → States i.val) (q : (r.program.stage i c).Index e)
    (old : ∀ j, Site.Programs (c j).val.placed.pack.layout)
    (good : ∀ j, Realizes (c j).val.names.sites (fun v => (old j v).program.boxes) (boxRoster (src := src) (last := last) (high := high) (k := k) (V := V) number rect base i.val)) :
    Realizes (r.program.advance i c q).val.names.sites
      (fun v => (r.program.savePrivatePrograms r.saveNames rows number i c q old v).program.boxes)
      (boxRoster (src := src) (last := last) (high := high) (k := k) (V := V) number rect base (i.val+1)) := by
  let st := r.program.stage i c
  let srcID := parallelName (fun j => (c j).val.names.sites)
  let dir := r.directory i c q
  let slots := siteRows e st.input srcID (r.directorySeed i).toEmbedding
  let pr := st.privatePrograms e q old (rows.sites i c q) dir.cables (rows.ports (i.val+1)) (rows.seeds i) number
  let cuts := fun v => Layer.orderedCuts st.input (CutCircuit.denseRows (raw (fun j => (c j).val.placed)).layout st.slot)
    (rows.ports (i.val+1)) v e st.label st.perm (rows.seeds i) st.orient (0,false) q dir.cables
  let known := BoxRoster.parallel (k := k) fun _ => boxRoster (src := src) (last := last) (high := high) (k := k) (V := V) number rect base i.val
  have hold : Realizes srcID (fun v => (old v.1 v.2).program.boxes) known := Realizes.parallel good
  have ha := sewn_realizes e number st.input st.label st.perm st.orient (0,false) q (rows.seeds i)
    srcID (r.directorySeed i) (rows.sites i c q) dir.cables (rows.ports (i.val+1))
    (fun v => (old v.1 v.2).program) cuts known hold
  have he (v) : (pr v).program = roundSites e st.input st.label st.perm st.orient (0,false) q
      (rows.seeds i) number (rows.sites i c q) dir.cables (rows.ports (i.val+1))
      (fun v => (old v.1 v.2).program) cuts v :=
    st.privatePrograms_program e q old _ _ _ _ _ v
  have ht : Realizes slots (fun v => (pr v).program.boxes) (BoxRoster.sewn e number known) := by
    simpa only [he] using ha
  have hn := ht.reindex dir.sites (finCongr (rect i)) (fun v => Fin.ext ((r.directorySeed_spec i c q).1 v))
  have hs := savedRoster (fin' := portFintype) (st.result e q) (r.program.advance i c q).val.placed dir
    (r.program.advance i c q).val.names (r.stored i c q) (r.saved_names i c q) pr _ hn
  simp only [boxRoster,BoxRoster.steps,dite_eq_left i.isLt]
  convert! hs using 2

end PackedHistoryCircuit.Normalized.SourcePath.NamedRun

end BorderVNP
end Computability
end OAI
