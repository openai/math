import OAI.Computability.VPVNP.PairTraversalLayerExecution

/-!
# Native construction of all depth-first traversal rows

The raw preimage records from Appendix E are translated layer by layer.
Every native pass reads identifiers below the descriptor arena, and writes
only the live words of its own row. Consequently the raw inputs and the
completed older layers survive. The final memory is precisely the image
used by the depth-first traversal.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.TraversalRows

open BurstRAM CompressorRecords
open scoped Fin.CommRing

variable {w : ℕ}

/-- Locations of the count and old-site identifier list for each site. -/
structure Source (w : ℕ) (L : Layer) where
  /-- External address of the cell holding the number of old-site identifiers for each site of
  this layer. -/
  counts : Fin L.count → Word w
  /-- External address of the first identifier in each site's list of preimages in the
  preceding layer. -/
  starts : Fin L.count → Word w

/-- The Appendix E records lie below the fresh traversal arena. -/
structure Source.Ready {L : Layer} (r : Source w L) (mem : Memory w) (limit : ℕ) : Prop where
  rows : ∀ i, rowRepresents mem (r.counts i) (r.starts i)
    ((L.ids i).map (fun j : ℕ => (j : Word w)))
  countBefore : ∀ i, (r.counts i).val < limit
  sourceBefore : ∀ i, (r.starts i).val + (L.ids i).length ≤ limit

/-- The shared zero word can supply the zero count for every cursor leaf. -/
def leafSource {I : Type} (ord : LocalHistory.Order I) (zero : Word w) :
    Source w (leafLayer ord) := ⟨fun _ => zero, fun _ => zero⟩

theorem leafSource_ready {I : Type} (ord : LocalHistory.Order I) (zero : Word w) (mem : Memory w)
    {limit : ℕ} (hzero : mem zero.val = 0) (hbelow : zero.val < limit) :
    (leafSource ord zero).Ready mem limit := by
  refine ⟨fun _ => ⟨?_, fun i => Fin.elim0 i⟩, fun _ => hbelow, fun _ => hbelow.le⟩
  change (mem zero.val).val = 0
  rw [hzero]
  rfl

/-- The raw record directories, in increasing compressor-stage order. -/
def Sources (w : ℕ) : List Layer → Type
  | [] => PUnit
  | L :: ls => Source w L × Sources w ls

/-- Each layer's source directory describes the correct old-site identifier lists in memory,
with all count cells and live identifier cells below `limit`. -/
def SourcesReady (mem : Memory w) (limit : ℕ) : (ls : List Layer) → Sources w ls → Prop
  | [], _ => True
  | _ :: ls, r => r.1.Ready mem limit ∧ SourcesReady mem limit ls r.2

private theorem transfer_ready (ls : List Layer) (sources : Sources w ls) {mem mem' : Memory w}
    {limit limit' : ℕ} (le : limit ≤ limit') (below : ∀ x < limit, mem' x = mem x)
    (h : SourcesReady mem limit ls sources) : SourcesReady mem' limit' ls sources := by
  induction ls with
  | nil => trivial
  | cons L ls ih =>
    have hc := h.1.countBefore
    have hs := h.1.sourceBefore
    refine ⟨⟨fun i => ?_, fun i => (hc i).trans_le le, fun i => (hs i).trans le⟩,
      ih sources.2 h.2⟩
    have r := h.1.rows i
    refine ⟨(congrArg Fin.val (below _ (hc i))).trans r.1, fun j => ?_⟩
    have hj : j.val < (L.ids i).length := by simpa only [List.length_map] using j.isLt
    exact (below _ ((Nat.add_lt_add_left hj _).trans_le (hs i))).trans (r.2 j)

/-- Each layer's actual scan begins with the memory left by its predecessor.
The trace lists concatenate the native instruction events in that order. -/
inductive BuildPasses (cap : ℕ) (state : Word w) (priv : Word w → Word w) :
    (previous base : ℕ) → (ls : List Layer) → Sources w ls → Memory w → List (Event w) → Prop
  | nil (previous base : ℕ) (sources : Sources w []) (m : Memory w) :
      BuildPasses cap state priv previous base [] sources m []
  | cons {previous base : ℕ} {L : Layer} {ls : List Layer} {sources : Sources w (L :: ls)}
      {m : Memory w} {es tail : List (Event w)}
      (stage : LayerPasses L cap previous base state priv sources.1.counts sources.1.starts
        (List.finRange L.count) m es)
      (rest : BuildPasses cap state priv base (endPos cap base L) ls sources.2 (after m es) tail) :
      BuildPasses cap state priv previous base (L :: ls) sources m (es ++ tail)

/-- Two probes for each identifier, plus three probes for each header. -/
def Layer.probeCount (L : Layer) : ℕ := (2 * ∑ i, (L.ids i).length) + 3 * L.count

theorem probes_le (ls : List Layer) (cap : ℕ) (hc : ∀ L ∈ ls, ∀ i, (L.ids i).length ≤ cap) :
    (ls.map Layer.probeCount).sum ≤ (2 * cap + 3) * (ls.map Layer.count).sum := by
  induction ls with
  | nil => simp
  | cons L ls ih =>
    have hi := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hc L List.mem_cons_self i)
    have hsum : (∑ i, (L.ids i).length) ≤ L.count * cap := by simpa using hi
    have hL : L.probeCount ≤ (2 * cap + 3) * L.count := by
      unfold Layer.probeCount
      exact (Nat.add_le_add_right (Nat.mul_le_mul_left 2 hsum) _).trans_eq (by ring)
    simpa [Nat.mul_add] using Nat.add_le_add hL (ih (fun l hl => hc l (List.mem_cons_of_mem _ hl)))

private theorem countProbes_append (x y : List (Event w)) :
    countProbes (x ++ y) = countProbes x + countProbes y := by
  induction x with
  | nil => simp [countProbes]
  | cons e x ih => cases e <;> simp [countProbes, ih, Nat.add_assoc]

/-- Construct all layers from their live raw count and identifier records.
The proof executes each native pass and obtains the exact descriptor image
as its post-memory. -/
theorem native_build (ls : List Layer) (cap previous base : ℕ) (state : Word w)
    (priv : Word w → Word w) (sources : Sources w ls) (mem : Memory w)
    (ready : SourcesReady mem base ls sources) (hc : ∀ L ∈ ls, ∀ i, (L.ids i).length ≤ cap)
    (fit : base + words cap ls < 2 ^ w) :
    ∃ es, BuildPasses cap state priv previous base ls sources mem es ∧
      after mem es = build cap previous base ls mem ∧
      countProbes es = (ls.map Layer.probeCount).sum := by
  induction ls generalizing previous base mem with
  | nil => exact ⟨[], .nil _ _ _ _, rfl, rfl⟩
  | cons L ls ih =>
    let next := endPos cap base L
    have hfit : next + words cap ls < 2 ^ w := by
      simpa [next, endPos, address, words, Nat.mul_add, Nat.add_assoc] using fit
    obtain ⟨ss, stage, hmem, probes⟩ := native_layer L cap previous base state priv
      sources.1.counts sources.1.starts mem ready.1.rows ready.1.countBefore ready.1.sourceBefore
      (hc L List.mem_cons_self) ((Nat.le_add_right _ _).trans_lt hfit)
    have hbefore (x : ℕ) (hx : x < base) : after mem ss x = mem x := by
      rw [hmem]
      apply writeLayer_unchanged
      rintro ⟨i, h, _⟩
      exact hx.not_ge ((Nat.le_add_right base _).trans h)
    have hr := transfer_ready ls sources.2 (limit' := next) (Nat.le_add_right _ _) hbefore ready.2
    obtain ⟨es, tail, hm, hp⟩ := ih base next sources.2 (after mem ss) hr
      (fun L hL => hc L (List.mem_cons_of_mem _ hL)) hfit
    refine ⟨ss ++ es, .cons stage tail, ?_, ?_⟩
    · rw [show after mem (ss ++ es) = after (after mem ss) es from List.foldl_append, hm, hmem]
      rfl
    · rw [countProbes_append, hp, probes]
      rfl

section Selected

open LocalHistory NetworkKernel Compression

variable {k A : Type*} [Field k] [CommRing A] {S : BlockSchedule k} (B : S.Templates)
variable (f : B.Entry → A) (hf : B.IsSolution f) {lanes : ℕ} (T : ℕ)
variable (hT : T * S.laneBits ≤ lanes) (X : State (S.degreeExponent 0) lanes)
variable (z : (B.execute f hf T hT X).Choices)

theorem selected_capacity :
    ∀ L ∈ selectedLayers B f hf T hT X z, ∀ i, (L.ids i).length ≤ B.recordLimit := by
  let E := B.execute f hf T hT X
  let data := B.records f hf T hT X
  have hb := Procedure.repeat_recordBounds (B.recordBounds f hf) _ T lanes
    (Nat.add_sub_of_le hT).symm X
  exact chainLayers_capacity (E.termChain data z) (selectedParsers B f hf T hT X z)
    (branchOrders E data z) (siteOrder X) (E.termChain_bounded data hb.1 z)

/-- On an actual selected compressor branch, the native builder passes their
post-memory directly to the ordered DFS. The two probe counts measure the
whole build and a single final vertex's traversal respectively. -/
theorem selected_native_traversal (base : ℕ) (state : Word w) (priv : Word w → Word w)
    (sources : Sources w (selectedLayers B f hf T hT X z)) (mem : Memory w)
    (ready : SourcesReady mem base _ sources)
    (fit : base + words B.recordLimit (selectedLayers B f hf T hT X z) < 2 ^ w) :
    let ls := selectedLayers B f hf T hT X z
    let E := B.execute f hf T hT X
    let data := B.records f hf T hT X
    let chain := E.termChain data z
    let ptr := chainPointers B.recordLimit chain (branchOrders E data z)
      (address B.recordLimit base (siteOrder X).length)
    let leaf := sitePointers B.recordLimit base (siteOrder X)
    let trees := chainTrees chain (selectedParsers B f hf T hT X z) ptr (fun v => leafTree (leaf v))
    ∃ es, BuildPasses B.recordLimit state priv base base ls sources mem es ∧
      after mem es = build B.recordLimit base base ls mem ∧
      countProbes es ≤ (2 * B.recordLimit + 3) * (ls.map Layer.count).sum ∧
      ∀ v, ∃ log, DFS.Visits (after mem es) (B.growthConstant ^ T) [((trees v).address : Word w)]
        ((trees v).preorder.map (fun n : ℕ => (n : Word w))) log ∧
        countProbes log < 3 * chain.occurrences (fun _ => 1) v ∧
        log.length ≤ 15 * chain.occurrences (fun _ => 1) v + 1 := by
  have hc := selected_capacity B f hf T hT X z
  obtain ⟨es, hpass, hm, hcost⟩ := native_build _ _ base base state priv sources mem ready hc fit
  refine ⟨es, hpass, hm, hcost.trans_le (probes_le _ _ hc), ?_⟩
  rw [hm]
  exact selected_memory_traversal B f hf T hT X z base mem fit

end Selected

end PairSimulation.TraversalRows

end VPVNP
end Computability
end OAI
