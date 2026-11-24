import OAI.Computability.VPVNP.PairTraversalReferenceFootprint
import OAI.Computability.VPVNP.PairTraversalSiteReads

/-!
# Raw input addresses of the selected traversal passes

The tag and leaf workers only write. Each fiber worker reads a count and the
corresponding identifiers from the retained placement directory. Every prefix
of the descriptor scan preserves these raw inputs, including between two
sites of the same layer.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.TraversalController

open BurstRAM BurstRAM.PrivateRAM CompressorRecords LocalHistory Compression NetworkKernel
open TraversalRows TraversalRoles DirectoryRun TraversalControllerInputs
open scoped Fin.CommRing

variable {w : ℕ}

private theorem reads_append {data : ℕ → Prop} {rs ss : List (Report w)}
    (h : SourceTransport.Reads data (eventLog rs)) (k : SourceTransport.Reads data (eventLog ss)) :
    SourceTransport.Reads data (eventLog (rs ++ ss)) := by
  intro a v mem
  rw [show eventLog (rs ++ ss) = eventLog rs ++ eventLog ss from List.flatMap_append] at mem
  exact (List.mem_append.mp mem).elim (h a v) (k a v)

private theorem reads_of_calls {data : ℕ → Prop} {rs : List (Report w)}
    (h : ∀ i : Fin rs.length, SourceTransport.Reads data rs[i.val].events) :
    SourceTransport.Reads data (eventLog rs) := by
  intro a v mem
  obtain ⟨r, hr, he⟩ := List.mem_flatMap.mp mem
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hr
  exact h ⟨i,hi⟩ a v he

open private events from OAI.Computability.VPVNP.PairTraversalLeafWorker

/-- Every tag worker has an empty external read set. -/
theorem tag_reads {p : Fin 4 → Word w} {count : ℕ} {m : Memory w} {rs : List (Report w)}
    (h : (Pass.tag p count).Run m rs) (data : ℕ → Prop) :
    SourceTransport.Reads data (eventLog rs) := by
  apply reads_of_calls
  intro i a v mem
  have eqn := Option.some.inj ((h.atSite i).symm.trans (Native.visit_native p _ _))
  rw [eqn] at mem
  simp [Native.events] at mem

/-- Every leaf worker has an empty external read set, including its header writes. -/
theorem leaf_reads (cap base count : ℕ) {m : Memory w} {rs : List (Report w)}
    (h : (Pass.leaf (LeafWorker.directory w cap base) count).Run m rs) (data : ℕ → Prop) :
    SourceTransport.Reads data (eventLog rs) := by
  apply reads_of_calls
  intro i a v mem
  let entry := after m (eventLog (rs.take i.val))
  have native := LeafWorker.native cap base i.val 14 entry (by decide)
  have eqn := Option.some.inj ((h.atSite i).symm.trans native)
  rw [eqn] at mem
  simp [events] at mem

open private ready_under from OAI.Computability.VPVNP.PairTraversalDirectoryRun
open private row_end_le from OAI.Computability.VPVNP.PairTraversalRows

/-- Every site in a fiber layer reads its retained count and source identifiers
strictly below the original raw-directory limit. -/
theorem fiber_reads (p : Fin 6 → Word w) (cap previous base : ℕ) (L : Layer)
    (raw m : Memory w) (limit : ℕ)
    (ready : (⟨fun i => countAt p (i.val : Word w), fun i => rowAt p (i.val : Word w)⟩ :
      Source w L).Ready raw limit)
    (ag : ∀ x < limit, m x = raw x) (below : limit ≤ base)
    (capacity : ∀ i, (L.ids i).length ≤ cap) (fit : endPos cap base L < 2 ^ w)
    (rs : List (Report w))
    (run : (Pass.fiber (workerData p cap previous base) cap L.count).Run m rs) :
    SourceTransport.Reads (· < limit) (eventLog rs) := by
  have frame := fiber_prefix p cap previous base L raw m limit ready ag below capacity fit rs run
  apply reads_of_calls
  intro i
  let j : Fin L.count := ⟨i.val, i.isLt.trans_eq run.length⟩
  let entry := after m (eventLog (rs.take i.val))
  let data := workerData p cap previous base
  let src := (rowAt p (i.val : Word w)).val
  let node := address cap base i.val
  have seen : ∀ x < limit, entry x = raw x := fun x hx =>
    (frame i.val i.isLt.le x (Or.inl (hx.trans_le below))).trans (ag x hx)
  have rows := (ready_under ready seen le_rfl).rows j
  have hs : SiteWorker.source data (i.val : Word w) = (src : Word w) :=
    Fin.ext (Nat.mod_eq_of_lt (rowAt p (i.val : Word w)).isLt).symm
  have hn : SiteWorker.node data (i.val : Word w) = (node : Word w) := by
    change (base : Word w) + (i.val : Word w) * ((cap + 2 : ℕ) : Word w) =
      ((base + (cap + 2) * i.val : ℕ) : Word w)
    simp only [Nat.cast_add, Nat.cast_mul]
    rw [mul_comm]
  have hc : (entry (SiteWorker.counter data (i.val : Word w)).val).val = (L.ids j).length := by
    change (entry (countAt p (i.val : Word w)).val).val = _
    simpa only [List.length_map] using rows.1
  have srcBelow : src + (L.ids j).length ≤ limit := ready.sourceBefore j
  have cntBelow : (SiteWorker.counter data (i.val : Word w)).val < limit := ready.countBefore j
  have within : node + 2 + (L.ids j).length < 2 ^ w := by
    have := row_end_le cap base L j
    have := capacity j
    dsimp only [node, j] at *
    omega
  have one := SiteWorker.native_reads data (i.val : Word w) entry src node (L.ids j).length
    (7 * cap + 25) hs hn hc (srcBelow.trans (below.trans (Nat.le_add_right _ _))) within
    (by have := capacity j; omega) (run.atSite i)
  intro a v mem
  rcases one a v mem with atCount | inRow
  · exact atCount ▸ cntBelow
  · exact inRow.2.trans_le srcBelow

/-- Tagging any number of layers uses no external reads. -/
theorem tag_chain_reads {offset cap base : ℕ} {ls : List TaggedLayer}
    {m : Memory w} {rs : List (Report w)} (h : RolePasses offset cap base ls m rs)
    (data : ℕ → Prop) :
    SourceTransport.Reads data (eventLog rs) := by
  induction h with
  | nil => exact fun _ _ he => (List.not_mem_nil he).elim
  | cons one _ ih => exact reads_append (tag_reads one data) ih

open private Segments.head_tail from OAI.Computability.VPVNP.PairTraversalReferenceFootprint

variable {A : Type*} [CommRing A] {Label : Type} [Fintype Label] {κ : Label → A}
variable {N Y : Network}

/-- The same raw-directory limit applies to every later fiber layer, even as
the base of the new descriptors advances. -/
theorem fiber_chain_reads (raw : Memory w) (limit : ℕ) (c : TermChain A N Y) (r : ChainParsers κ c)
    (ords : ChainOrders c) (old : Order N.Site) (dirs : Directories raw limit c ords old)
    (ho : OrderedChildren c r ords old) (cap previous base : ℕ) (m : Memory w)
    (below : limit ≤ base) (ag : ∀ x < limit, m x = raw x)
    (hc : ∀ L ∈ stepLayers c r ords old, ∀ i, (L.ids i).length ≤ cap)
    (fit : base + words cap (stepLayers c r ords old) < 2 ^ w)
    (rs : List (Report w))
    (run : DirectoryRun.Segments (workers c ords old dirs cap previous base) m rs) :
    SourceTransport.Reads (· < limit) (eventLog rs) := by
  induction c generalizing previous base m rs with
  | done => cases run; exact fun _ _ he => (List.not_mem_nil he).elim
  | more t data tail ih =>
    let L := stepLayer old ords.1 r.1
    let ls := stepLayers tail r.2 ords.2 ords.1
    let next := endPos cap base L
    have bound : base + words cap (stepLayers (.more t data tail) r ords old) =
        next + words cap ls := by
      simp [L, ls, next, stepLayers, endPos, address, words, Nat.mul_add, Nat.add_assoc]
    obtain ⟨one, rest, rfl, hr, ht⟩ := Segments.head_tail run
    rw [bound] at fit
    have within : next < 2 ^ w := (Nat.le_add_right _ _).trans_lt fit
    have ready := dirs.1.ready r.1 ho.1
    have head := fiber_reads dirs.1.pub cap previous base L raw m limit ready ag below
      (hc _ List.mem_cons_self) within one hr
    have frame := fiber_prefix dirs.1.pub cap previous base L raw m limit ready ag below
      (hc _ List.mem_cons_self) within one hr
    apply reads_append head
    exact ih r.2 ords.2 ords.1 dirs.2 ho.2 base next (after m (eventLog one))
      (below.trans (Nat.le_add_right _ _))
      (fun x hx => (frame.full x (Or.inl (hx.trans_le below))).trans (ag x hx))
      (fun l hl => hc l (List.mem_cons_of_mem L hl)) fit rest ht

variable {k : Type*} [_root_.Field k] {S : BlockSchedule k} (B : S.Templates) (f : B.Entry → A)
variable (hf : B.IsSolution f) {n : ℕ} (T : ℕ) (hT : T * S.laneBits ≤ n)
variable (X : State (S.degreeExponent 0) n) (z : (B.execute f hf T hT X).Choices)
variable (base : ℕ) (raw : Memory w)
variable (ds : let vs := executeLevels B f hf T hT X z
  (i : Fin vs.length) → LevelDirectory vs[i] raw base)

/-- Complete reference read footprint of the selected tag and descriptor
passes, starting from the retained branch directories. -/
theorem selected_reference_reads (offset : ℕ) (ts rs : List (Report w))
    (tags : RolePasses offset B.recordLimit base (selected B f hf T hT X z) raw ts)
    (rows : DirectoryRun.Segments (selectedJobs B f hf T hT X z base raw ds)
      (after raw (eventLog ts)) rs)
    (fit : offset + base + tagWords B.recordLimit (selected B f hf T hT X z) < 2 ^ w) :
    SourceTransport.Reads (· < base) (eventLog (ts ++ rs)) := by
  refine reads_append (tag_chain_reads tags (· < base)) ?_
  let E := B.execute f hf T hT X
  let data := B.records f hf T hT X
  let c := E.termChain data z
  let ords := branchOrders E data z
  let old := siteOrder X
  let r := selectedParsers B f hf T hT X z
  let dirs := selectedDirectories B f hf T hT X z raw base ds
  let cap := B.recordLimit
  let L := leafLayer old
  let ls := stepLayers c r ords old
  let next := endPos cap base L
  let m := after raw (eventLog ts)
  have tagFrame := tag_chain_prefix tags fit.le
  have ag (x : ℕ) (hx : x < base) : m x = raw x :=
    tagFrame.full x (Or.inl (hx.trans_le (Nat.le_add_left _ _)))
  have eqSize : tagWords cap (selected B f hf T hT X z) =
      words cap (selectedLayers B f hf T hT X z) :=
    congrArg (words cap) (selected_layers B f hf T hT X z)
  have size : base + words cap (selectedLayers B f hf T hT X z) < 2 ^ w := by
    change offset + base + tagWords cap (selected B f hf T hT X z) < _ at fit
    rw [eqSize] at fit
    omega
  have bound : base + words cap (selectedLayers B f hf T hT X z) = next + words cap ls := by
    change base + words cap (L :: ls) = _
    simp [next, endPos, address, words, Nat.mul_add, Nat.add_assoc]
  rw [bound] at size
  change DirectoryRun.Segments (.leaf cap base old.length ::
    workers c ords old dirs cap base next) m rs at rows
  obtain ⟨one, rest, rfl, hr, ht⟩ := Segments.head_tail rows
  have leaf := leaf_prefix cap base old.length m one hr ((Nat.le_add_right _ _).trans_lt size)
  refine reads_append (leaf_reads cap base old.length hr (· < base)) ?_
  exact fiber_chain_reads raw base c r ords old dirs (selectedParsers_ordered B f hf T hT X z)
    cap base next _ (Nat.le_add_right _ _)
    (fun x hx => (leaf.full x (Or.inl hx)).trans (ag x hx))
    (fun l hl => selected_capacity B f hf T hT X z l (List.mem_cons_of_mem L hl)) size rest ht

end PairSimulation.TraversalController

end VPVNP
end Computability
end OAI
