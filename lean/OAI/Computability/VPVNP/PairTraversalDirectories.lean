import OAI.Computability.VPVNP.PairTraversalBuildExecution
import OAI.Computability.VPVNP.PairTraversalNativeLayer
import OAI.Computability.VPVNP.PairTraversalSelectedOrder
import OAI.Computability.VPVNP.PairTraversalStageSize

/-!
# Connecting the placement directories to the native traversal table

The native Appendix E scan records each old identifier under its placed new
site. Those directories, a common zero count for the leaves, and the end of
the raw arena supply all inputs to the traversal-table writer. The source
records retain the physical numbering of the chosen compression branch.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.TraversalRows

open BurstRAM CompressorRecords LocalHistory NetworkKernel Compression
open scoped Fin.CommRing

variable {w : ℕ} {A : Type*} [CommRing A] {Label : Type} [Fintype Label] {κ : Label → A}
variable {N Y : Network}

/-- A completed numerical placement pass with its concrete raw memory regions.
The native owner map is the term's actual placement in the two site orders. -/
structure Directory {N : Network} (t : Term A N) (old : Order N.Site) (next : Order t.output.Site)
    (mem : Memory w) (limit : ℕ) where
  /-- Six public directory words locating the old-site, output-site, count, and preimage row
  data for a selected pass. -/
  pub : Fin 6 → Word w
  oldCount : (pub 0).val = old.length
  newCount : (pub 2).val = next.length
  regions : RowRegions pub
  inputEnd : (pub 5).val + (pub 2).val * (pub 4).val ≤ limit
  collected : PreimagesAt pub (encodedPlacement old.entries.symm next.entries.symm t.place)
    mem old.length
  capacity : ∀ v : Word w, v < pub 2 →
    (preimagePrefix (encodedPlacement old.entries.symm next.entries.symm t.place) v
      old.length).length ≤ (pub 4).val

/-- Expose the per-site child count and preimage-row start as source pointers for the selected
directory reader. -/
def Directory.source {t : Term A N} {old : Order N.Site} {next : Order t.output.Site}
    {mem : Memory w} {limit : ℕ} (dir : Directory t old next mem limit) (r : TermParsers κ t) :
    Source w (stepLayer old next r) :=
  ⟨fun i => countAt dir.pub (i.val : Word w), fun i => rowAt dir.pub (i.val : Word w)⟩

open Classical in
theorem Directory.ready {t : Term A N} {old : Order N.Site} {next : Order t.output.Site}
    {mem : Memory w} {limit : ℕ} (dir : Directory t old next mem limit) (r : TermParsers κ t)
    (ho : ∀ v, r.order.children v = old.restrict (fun u => v = t.place u)) :
    (dir.source r).Ready mem limit := by
  let physical : Word w → Word w := encodedPlacement old.entries.symm next.entries.symm t.place
  have hfit₀ : old.length ≤ 2 ^ w := dir.oldCount ▸ (dir.pub 0).isLt.le
  have hfit₁ : next.length ≤ 2 ^ w := dir.newCount ▸ (dir.pub 2).isLt.le
  have rows := raw_rows_of_preimages old next r physical
    (encodedPlacement_represents old next t.place hfit₀ hfit₁) ho dir.pub mem dir.oldCount
    dir.newCount dir.collected
  have hv (i : Fin next.length) : (i.val : Word w) < dir.pub 2 := by
    change i.val % (2 ^ w) < (dir.pub 2).val
    rw [Nat.mod_eq_of_lt (i.isLt.trans_le hfit₁), dir.newCount]
    exact i.isLt
  have before (i : Fin next.length) := preimage_input_before dir.regions dir.inputEnd (hv i)
  refine ⟨rows, fun i => (before i).1, fun i => ?_⟩
  have hlen := (rows i).1.symm.trans (dir.collected.rows _ (hv i)).1
  rw [List.length_map] at hlen
  exact (Nat.add_le_add_left (hlen.trans_le (dir.capacity _ (hv i))) _).trans (before i).2

/-- Persistent directories of all non-leaf terms on this particular branch. -/
def Directories (mem : Memory w) (limit : ℕ) {N Y : Network} (c : TermChain A N Y)
    (ords : ChainOrders c) (old : Order N.Site) : Type :=
  match c with
  | .done _ => PUnit
  | .more t _ tail => Directory t old ords.1 mem limit × Directories mem limit tail ords.2 ords.1

/-- Collect the child-count and preimage-row source pointers along the chain of selected
compression directories. -/
noncomputable def directorySources {mem : Memory w} {limit : ℕ} {N Y : Network}
    (c : TermChain A N Y)
    (r : ChainParsers κ c) (ords : ChainOrders c) (old : Order N.Site)
    (dirs : Directories mem limit c ords old) : Sources w (stepLayers c r ords old) := by
  induction c with
  | done => exact PUnit.unit
  | more t data tail ih => exact ⟨dirs.1.source r.1, ih r.2 ords.2 ords.1 dirs.2⟩

theorem directories_ready {mem : Memory w} {limit : ℕ} (c : TermChain A N Y)
    (r : ChainParsers κ c) (ords : ChainOrders c) (old : Order N.Site)
    (dirs : Directories mem limit c ords old) (ho : OrderedChildren c r ords old) :
    SourcesReady mem limit (stepLayers c r ords old) (directorySources c r ords old dirs) := by
  induction c with
  | done => trivial
  | more _ _ _ ih => exact ⟨dirs.1.ready r.1 ho.1, ih r.2 ords.2 ords.1 dirs.2 ho.2⟩

variable {k : Type*} [Field k] {S : BlockSchedule k} (B : S.Templates) (f : B.Entry → A)
variable (hf : B.IsSolution f) {lanes : ℕ} (T : ℕ) (hT : T * S.laneBits ≤ lanes)
variable (X : State (S.degreeExponent 0) lanes) (z : (B.execute f hf T hT X).Choices)

/-- The source-count and source-list pointers of an actual selected branch
satisfy all the native writer's preconditions. -/
theorem selected_sources_ready (mem : Memory w) (base : ℕ) (zero : Word w)
    (hzero : mem zero.val = 0) (hz : zero.val < base) :
    let E := B.execute f hf T hT X
    let data := B.records f hf T hT X
    let c := E.termChain data z
    let parsers := selectedParsers B f hf T hT X z
    let ords := branchOrders E data z
    ∀ dirs : Directories mem base c ords (siteOrder X),
      SourcesReady mem base (selectedLayers B f hf T hT X z)
        ⟨leafSource (siteOrder X) zero, directorySources c parsers ords (siteOrder X) dirs⟩ := by
  intro E data c parsers ords dirs
  exact ⟨leafSource_ready _ _ _ hzero hz, directories_ready c parsers ords _ dirs
    (selectedParsers_ordered B f hf T hT X z)⟩

end PairSimulation.TraversalRows

end VPVNP
end Computability
end OAI
