import OAI.Computability.VPVNP.CompressorRecordsShrinkGreedyLayout
import OAI.Computability.VPVNP.CompressorGreedyRelocated

/-! # External state transfer between the shrinking assignment passes -/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.GreedyArena

open BurstRAM Compression Greedy

variable {w N width d : ℕ} {V A : Type*}

/-- A pair of actual reset-on-entry burst scans with the public parameters used
by the planner. The reader begins in exactly the memory left by preparation. -/
structure Assignment (L : WalkLayout w N width) (T : PortTables w) (G : SlotGraph V d)
    (order : V ≃ Fin N) (rows : OperandRows d) (arity n : ℕ) (m : Memory w)
    (encode : A → Word w) (label : V → A) where
  /-- Reports of preparing one operand row per old base vertex for a greedy assignment. -/
  prep : List (Report w)
  /-- Reports of the visits that read the prepared rows and write each vertex's assigned label. -/
  reads : List (Report w)
  prepRun : runSegment ((Relocated.preparePass rows).table.instantiate w
    (Relocated.publicWords d L T)).program (1 + (Relocated.prepareCode rows).length) (some 0) m
    (List.replicate N []) = some prep
  prepEnd : endState (some 0) prep = some (Fin.ofNat _ N)
  prepMemory : after m (eventLog prep) =
    L.initialMemory (fun i => rowWords T G order (order.symm i) rows) m
  prepCost : RAMBuckets.cost Report.probes prep = N * (4 + rows.length + width)
  prepLength : prep.length = N
  prepWork : ∀ r ∈ prep, r.events.length ≤ 22 + 8 * rows.length + 6 * width ∧
    r.probes = 3 + rows.length + width
  readRun : runSegment (visitMachine w arity n).program (1 + (visitCode arity n).length)
    (some (L.base 0)) (after m (eventLog prep)) (List.replicate N []) = some reads
  readEnd : endState (some (L.base 0)) reads = some (L.base N)
  readMemory : L.Represents (after m (eventLog prep)) (after (after m (eventLog prep)) (eventLog reads))
    encode order label
  readLength : reads.length = N
  readWork : ∀ r ∈ reads, r.events.length = 12 + ((4 * arity + 4) * n + 4) * n ∧
    countProbes r.events = 3 + 2 * arity * n * n

namespace Assignment

variable {L : WalkLayout w N width} {T : PortTables w} {G : SlotGraph V d} {order : V ≃ Fin N}
    {rows : OperandRows d} {arity n : ℕ} {m : Memory w} {encode : A → Word w} {label : V → A}
    (P : Assignment L T G order rows arity n m encode label)

/-- The memory containing the completed greedy assignment after row preparation and visits. -/
def post : Memory w := after (after m (eventLog P.prep)) (eventLog P.reads)

theorem atLabel (v : V) : P.post (L.label (order v)).val = encode (label v) := P.readMemory.labels v

theorem frame (z : ℕ) (away : z < L.origin ∨ L.limit ≤ z) : P.post z = m z := by
  have h := P.readMemory.frame z (away.imp_right (fun h => by unfold WalkLayout.limit at h; omega))
  change P.post z = _ at h
  rw [h, P.prepMemory]
  rcases away with hz | hz
  · simp [WalkLayout.initialMemory, hz]
  · exact L.initialMemory_after _ _ hz

end Assignment

theorem assignment_exists (L : WalkLayout w N width) (T : PortTables w) (G : SlotGraph V d)
    (order : V ≃ Fin N) (rows : OperandRows d) (arity n : ℕ) (m : Memory w)
    (encode : A → Word w) (label : V → A) (labels : T.labels = Fin.ofNat _ L.origin)
    (rep : T.Represents G order m) (space : L.limit < 2 ^ w) (outside : GraphOutside (d := d) L T order)
    (size : ∀ i : Fin N, (rowWords T G order (order.symm i) rows).length = width)
    (reader : L.Pass (L.initialMemory (fun i => rowWords T G order (order.symm i) rows) m)
      arity n encode order label) : Nonempty (Assignment L T G order rows arity n m encode label) := by
  obtain ⟨prep, hp, hend, hm, hl, hc, hw⟩ :=
    Relocated.prepare_directory L T G order rows m labels rep space outside size
  rw [← hm] at reader
  obtain ⟨reads, hr, hrend, hmem, hlen, hwork⟩ := reader
  exact ⟨⟨prep, reads, hp, hend, hm, hc, hl, hw, hr, hrend, hmem, hlen, hwork⟩⟩

end CompressorRecords.GreedyArena

end VPVNP
end Computability
end OAI
