import OAI.Computability.VPVNP.PairTraversalDirectories
import OAI.Computability.VPVNP.PairTraversalLayerSegment
import OAI.Computability.VPVNP.PairTraversalLeafWorker

/-!
# Reset-entry construction of a selected branch's traversal descriptors

The cursor-leaf pass writes the two header words directly. Each subsequent
pass translates one of the completed Appendix E placement directories using
one native burst per new site. Registers are reset on entry, and the persistent
site counter is initialized to zero at the beginning of each layer.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.TraversalRows.DirectoryRun

open BurstRAM CompressorRecords NetworkKernel LocalHistory Compression
open scoped Fin.CommRing

variable {w : ℕ}

/-- Public parameters for one of the two fixed descriptor workers. -/
inductive Worker (w : ℕ) where
  | leaf (cap base count : ℕ)
  | fiber (pub : Fin 6 → Word w) (cap previous base count : ℕ)

/-- A layer is evaluated from the first site using zero-initialized private registers. -/
def Worker.Run (m : Memory w) (rs : List (Report w)) : Worker w → Prop
  | .leaf cap base count =>
    let P := (LeafWorker.program.template (some 0)).instantiate w (LeafWorker.directory w cap base)
    runSegment P.program 14 (some 0) m (List.replicate count []) = some rs
  | .fiber pub cap previous base count =>
    let P := (SiteWorker.program.template (some 6)).instantiate w (workerData pub cap previous base)
    runSegment P.program (7 * cap + 25) (some 0) m (List.replicate count []) = some rs

/-- The memory output of each stage is the memory input of the next. -/
inductive Segments : List (Worker w) → Memory w → List (Report w) → Prop
  | nil (m : Memory w) : Segments [] m []
  | cons {head : Worker w} {tail : List (Worker w)} {m : Memory w} {rs ss : List (Report w)}
      (run : head.Run m rs) (rest : Segments tail (after m (eventLog rs)) ss) :
      Segments (head :: tail) m (rs ++ ss)

variable {A : Type*} [CommRing A] {Label : Type} [Fintype Label] {κ : Label → A}
variable {N Y : Network}

/-- Six public words per term identify the live raw records. Consecutive
layers use contiguous rows and point into their predecessor's rows. -/
def workers {N Y : Network} {raw : Memory w} {limit : ℕ} (c : TermChain A N Y)
    (ords : ChainOrders c)
    (old : Order N.Site) (dirs : Directories raw limit c ords old) (cap previous base : ℕ) :
    List (Worker w) :=
  match c with
  | .done _ => []
  | .more _ _ tail => .fiber dirs.1.pub cap previous base ords.1.length ::
    workers tail ords.2 ords.1 dirs.2 cap base (address cap base ords.1.length)

private theorem append_memory (m : Memory w) (rs ss : List (Report w)) :
    after m (eventLog (rs ++ ss)) = after (after m (eventLog rs)) (eventLog ss) := by
  simp only [eventLog, List.flatMap_append, after, List.foldl_append]

private theorem append_probes (rs ss : List (Report w)) :
    countProbes (eventLog (rs ++ ss)) = countProbes (eventLog rs) + countProbes (eventLog ss) := by
  simp only [eventLog, List.flatMap_append, BurstRAM.countProbes_append]

/-- All native input words below the raw directory boundary survive updates
to the traversal arena. -/
private theorem ready_under {L : Layer} {r : Source w L} {raw m : Memory w} {limit base : ℕ}
    (hr : r.Ready raw limit) (ag : ∀ x < limit, m x = raw x) (below : limit ≤ base) :
    r.Ready m base := by
  refine ⟨fun i => ?_, fun i => (hr.countBefore i).trans_le below,
    fun i => (hr.sourceBefore i).trans below⟩
  refine ⟨(congrArg Fin.val (ag _ (hr.countBefore i))).trans (hr.rows i).1, fun j => ?_⟩
  have h : j.val < (L.ids i).length := by simpa only [List.length_map] using j.isLt
  exact (ag _ ((Nat.add_lt_add_left h _).trans_le (hr.sourceBefore i))).trans ((hr.rows i).2 j)

private theorem write_below (L : Layer) (cap previous base : ℕ) (m : Memory w) (x : ℕ)
    (hx : x < base) : writeLayer cap previous base L m x = m x := by
  apply writeLayer_unchanged
  rintro ⟨i, hlo, _⟩
  exact hx.not_ge ((Nat.le_add_right base ((cap + 2) * i.val)).trans hlo)

/-- Realize every non-leaf layer directly from the actual branch directories. -/
theorem run_fibers {raw : Memory w} {limit : ℕ} (c : TermChain A N Y) (r : ChainParsers κ c)
    (ords : ChainOrders c) (old : Order N.Site) (dirs : Directories raw limit c ords old)
    (ho : OrderedChildren c r ords old) (cap previous base : ℕ) (m : Memory w)
    (below : limit ≤ base) (ag : ∀ x < limit, m x = raw x)
    (hc : ∀ L ∈ stepLayers c r ords old, ∀ i, (L.ids i).length ≤ cap)
    (fit : base + words cap (stepLayers c r ords old) < 2 ^ w) :
    let ls := stepLayers c r ords old
    ∃ rs, Segments (workers c ords old dirs cap previous base) m rs ∧
      after m (eventLog rs) = build cap previous base ls m ∧
      rs.length = (ls.map Layer.count).sum ∧
      countProbes (eventLog rs) = (ls.map Layer.probeCount).sum := by
  induction c generalizing previous base m with
  | done => exact ⟨[], .nil _, rfl, rfl, rfl⟩
  | more t data tail ih =>
    let L := stepLayer old ords.1 r.1
    let rest := stepLayers tail r.2 ords.2 ords.1
    let next := endPos cap base L
    have hf : next + words cap rest < 2 ^ w := by
      simpa [next, L, rest, stepLayers, endPos, address, words, Nat.mul_add,
        Nat.add_assoc] using fit
    have room : next < 2 ^ w := (Nat.le_add_right _ _).trans_lt hf
    have hcap : ∀ i, (L.ids i).length ≤ cap := hc L List.mem_cons_self
    have hr := ready_under (dirs.1.ready r.1 ho.1) ag below
    obtain ⟨rs, run, _, mem, probes, calls, _⟩ := run_numbered_layer _ _ L cap previous base _ _ m
      (directory_worker dirs.1.pub L cap previous base hr.sourceBefore hcap room)
      hr.rows hr.countBefore hr.sourceBefore hcap room
    have hn : limit ≤ next := below.trans (Nat.le_add_right _ _)
    have ag' (x : ℕ) (hx : x < limit) : after m (eventLog rs) x = raw x := by
      rw [mem, write_below L cap previous base m x (hx.trans_le below), ag x hx]
    obtain ⟨ss, runs, mem', calls', probes'⟩ := ih r.2 ords.2 ords.1 dirs.2 ho.2 base next
      (after m (eventLog rs)) hn ag' (fun l hl => hc l (List.mem_cons_of_mem _ hl)) hf
    refine ⟨rs ++ ss, .cons (head := .fiber dirs.1.pub cap previous base ords.1.length) run runs,
      ?_, ?_, ?_⟩
    · rw [append_memory, mem', mem]
      rfl
    · rw [List.length_append, calls, calls']
      rfl
    · rw [append_probes, probes, probes']
      rfl

variable {k : Type*} [Field k] {S : BlockSchedule k} (B : S.Templates) (f : B.Entry → A)
variable (hf : B.IsSolution f) {n : ℕ} (T : ℕ) (hT : T * S.laneBits ≤ n)
variable (X : State (S.degreeExponent 0) n) (z : (B.execute f hf T hT X).Choices)

/-- A full native construction on the selected compressor branch. The leaf
worker writes both header words itself. No preinitialized zero cell is needed.
The total number of bursts is the exact selected row count. -/
theorem selected_run (base : ℕ) (raw m : Memory w) (ag : ∀ x < base, m x = raw x)
    (fit : base + words B.recordLimit (selectedLayers B f hf T hT X z) < 2 ^ w) :
    let E := B.execute f hf T hT X
    let data := B.records f hf T hT X
    let c := E.termChain data z
    let ords := branchOrders E data z
    let old := siteOrder X
    let cap := B.recordLimit
    let ls := selectedLayers B f hf T hT X z
    ∀ dirs : Directories raw base c ords old,
      ∃ rs, Segments (.leaf cap base old.length ::
          workers c ords old dirs cap base (address cap base old.length)) m rs ∧
        after m (eventLog rs) = build cap base base ls m ∧
        rs.length = (ls.map Layer.count).sum ∧
        countProbes (eventLog rs) ≤ (2 * cap + 3) * (ls.map Layer.count).sum := by
  intro E data c ords old cap ls dirs
  let r := selectedParsers B f hf T hT X z
  let L := leafLayer old
  let rest := stepLayers c r ords old
  let next := endPos cap base L
  have eq : ls = L :: rest := rfl
  have hcap := selected_capacity B f hf T hT X z
  have hf' : next + words cap rest < 2 ^ w := by
    change base + words cap (L :: rest) < 2 ^ w at fit
    simpa [next, endPos, address, words, Nat.mul_add,
        Nat.add_assoc] using fit
  obtain ⟨rs, run, _, mem, calls, probes, _⟩ := LeafWorker.run_layer old cap base base m 14
    ((Nat.le_add_right _ _).trans_lt hf') (by decide)
  have hn : base ≤ next := Nat.le_add_right _ _
  have ag' (x : ℕ) (hx : x < base) : after m (eventLog rs) x = raw x := by
    rw [mem, write_below _ cap base base m x hx, ag x hx]
  obtain ⟨ss, runs, mem', calls', probes'⟩ := run_fibers c r ords old dirs
    (selectedParsers_ordered B f hf T hT X z) cap base next _ hn ag'
    (fun l hl => hcap l (List.mem_cons_of_mem L hl)) hf'
  refine ⟨rs ++ ss, .cons (head := .leaf cap base old.length) run runs, ?_, ?_, ?_⟩
  · rw [append_memory, mem', mem]
    rfl
  · rw [List.length_append, calls, calls', eq]
    rfl
  · apply le_trans _ (probes_le ls cap hcap)
    rw [append_probes, probes, probes', eq, List.map_cons, List.sum_cons]
    have h : 2 * old.length ≤ L.probeCount := by simp [L, Layer.probeCount, leafLayer]; omega
    exact Nat.add_le_add_right h _

end PairSimulation.TraversalRows.DirectoryRun

end VPVNP
end Computability
end OAI
