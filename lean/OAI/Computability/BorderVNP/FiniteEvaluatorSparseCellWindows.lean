import OAI.Computability.BorderVNP.FiniteEvaluatorSparsePatchedCells
import OAI.Computability.BorderVNP.FragmentRowsSparsePatch

/-! # Compressed field-cell operands in the actual signed task windows

The public owner and scratch starts are read from the seven-word task table.
The fixed-stride compressed region lies strictly below that table. The
frame, scalar tail words and global call owner survive all sparse updates.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.SignedTaskArena

open VPVNP.BurstRAM Evaluator DiagonalTallyAllocation FiniteEvaluator SparseExterior CellPacket.Supplement
open private output_windows from OAI.Computability.BorderVNP.DiagonalNativeSparseProtection

variable (a : Layout) (team frame offsets ctl count w : ℕ) (raw : ℕ → ℕ)
variable (os : ℕ → SparseExterior.Owned)
local notation "l" => a.tasks team frame offsets ctl
local notation "sl" => batchLayout a frame ctl count

/-- Every scalar and call field needed after exterior encoding is outside
all sparse writes. Both the allocation header and the per-cell scalar tails
are true retained input ranges of the private dispatcher. -/
theorem Layout.field_windows (place : a.SparsePlacement frame ctl)
    (global : ∀ i < count, (os i).global<a.fragments.cells) (width : ∀ i < count, (os i).field.bytes.length≤a.fragments.stride) :
    Reports.SparseMetaOutside l sl os ∧ (l).SourceRange ctl 8 ∧ (l).SourceRange (l).tails (l).cells ∧
      ∀ k < 8, ¬(l).outputAt (ctl+k) := by
  have ord := a.sparse_order place.cells
  have early := place.beforeControl
  have base := place.beforeBank
  have frag : a.fragments.start≤a.fragments.external := by
    dsimp only [FragmentArena.Layout.external,FragmentArena.Layout.cursors,FragmentArena.Layout.triples,
      FragmentArena.Layout.pairs,FragmentArena.Layout.quads]; omega
  have below : ctl+8≤a.fragments.external := by omega
  have extent : a.before.tailWidths+a.cube.cells≤a.before.limit := by
    rw [a.before.footprint]
    change a.before.start+a.cube.cells≤a.before.start+16*a.p.report.cells+_+_
    have h := place.cells
    omega
  have old : a.fragments.limit≤a.before.tailWidths := le_rfl
  have limit : a.fragments.external≤a.fragments.limit := by
    dsimp only [FragmentArena.Layout.limit,FragmentArena.Layout.counts]; omega
  have calls : a.before.limit≤(l).scratch := by
    change a.before.limit≤a.before.limit+3*a.cube.cells+7*a.cube.cells
    omega
  have tailLo : a.fragments.limit≤a.before.limit := old.trans ((Nat.le_add_right ..).trans extent)
  refine ⟨?_,⟨(below.trans limit).trans (tailLo.trans calls),.inl ((below.trans limit).trans tailLo)⟩,
    ⟨extent.trans calls,.inl extent⟩,?_⟩
  · intro i hi
    have safe {addr : ℕ} (h : inputRegion a count addr) := inputRegion_outside a frame ctl count os global width hi h
    refine ⟨fun k hk => safe (.inl (by change frame+k<a.fragments.external; omega)),
      fun k hk => safe (.inl (by change ctl+k<a.fragments.external; omega)),?_⟩
    intro c hc
    change c<a.cube.cells at hc
    refine ⟨safe (.inr (.inl ⟨?_,?_⟩)),safe (.inr (.inl ⟨?_,?_⟩))⟩
    · change a.fragments.limit≤a.before.tailWidths+c; omega
    · change a.before.tailWidths+c<a.before.limit+3*a.cube.cells; omega
    · change a.fragments.limit≤a.before.limit+3*c; omega
    · change a.before.limit+3*c<a.before.limit+3*a.cube.cells; omega
  · intro k hk
    change ¬((a.before.limit+3*a.cube.cells ≤ ctl+k ∧ _) ∨
      (∃ c < a.cube.cells, ctl+k=a.before.limit+3*c) ∨ ctl+k=frame+90)
    rintro (⟨_,_⟩|⟨c,_,_⟩|h) <;> omega

/-- The observed seven task words determine the allocator's scratch, burst
and dispatch row for the genuine compact rank. -/
private theorem task_starts (t : TypedTaskBuilder.Layout) (mem : ℕ → ℕ) (built : Memory w)
    (room : t.Room mem w) (published : readings built=t.published mem) (i : ℕ) (hi : i<t.before mem t.cells)
    (row : TypedBatch.Task) (stored : row.Stored built t.tasks i) :
    let c := TypedTaskBuilder.globalCell t mem i
    row.callRow=t.call c ∧ row.cell.scratchBase=t.scratch+t.scratchStride*c ∧
      row.cell.burstBase=t.bursts+t.burstStride*c := by
  intro c
  obtain ⟨hc,own,rank⟩ := TypedTaskBuilder.global_spec t mem hi
  change t.before mem c=i at rank
  have get (k : Fin 7) : readings built (t.tasks+7*i+k.val)=(t.row mem c)[k.val]'(by simpa only [TypedTaskBuilder.Layout.row,List.length_cons,List.length_nil] using k.isLt) := by
    have selected := t.image_word mem room hc le_rfl own k
    have fresh := room.outputs.2
    rw [rank] at selected
    rw [published,TypedTaskBuilder.Layout.published,Function.update_of_ne (by omega : t.tasks+7*i+k.val≠t.frame+90)]
    exact selected
  obtain ⟨_,_,_,_,scratch,burst,call⟩ := stored
  exact ⟨call.symm.trans (get 6),scratch.symm.trans (get 4),burst.symm.trans (get 5)⟩

/-- All allocation fields for the sparse finite private cell call follow from
the real seven-word headers, their source-window endpoints and compressed
payload sizes. The global cells are recovered by compact rank. -/
theorem Layout.compressed_arenas {Site : Type} (src : ℕ → Batch.Owned Site) (built : Memory w)
    (room : (l).Room raw w) (published : readings built=(l).published raw)
    (card : count=(l).before raw (l).cells) (stored : ∀ i < count, (src i).typed.Stored built (l).tasks i)
    (global : ∀ i < count, (os i).global<a.fragments.cells)
    (width : ∀ i < count, (os i).field.bytes.length≤a.fragments.stride)
    (descriptors : ∀ i < count, (src i).typed.cell.descriptorBase+3*(src i).typed.cell.chunks.length≤a.before.limit)
    (chunks : ∀ i < count, ∀ c ∈ (src i).typed.cell.chunks, c.endSource≤a.before.limit)
    (sizes : ∀ i < count, ((os i).typed sl (src i).typed).cell.payload.length≤a.p.scratchStride ∧
      (((os i).typed sl (src i).typed).cell.burst w).length≤a.p.burstStride) :
    (l).Arenas raw w (fun i => (os i).typed sl (src i).typed) ∧
      ∀ i < count, (src i).callRow=(l).call (TypedTaskBuilder.globalCell l raw i) := by
  have starts (i : ℕ) (hi : i<count) := task_starts w l raw built room published i (card ▸ hi) (src i).typed (stored i hi)
  have below : a.fragments.counts≤a.before.limit := by
    rw [a.before.footprint]
    have before : a.before.start=a.fragments.limit := rfl
    have after : a.fragments.counts≤a.fragments.limit := by dsimp only [FragmentArena.Layout.limit]; omega
    omega
  have source (base size : ℕ) (small : base+size≤a.before.limit) : (l).SourceRange base size :=
    ⟨small.trans (by change a.before.limit≤a.before.limit+3*a.cube.cells+7*a.cube.cells; omega),.inl small⟩
  constructor
  · constructor
    · change a.before.limit+3*a.cube.cells≤a.before.limit+3*a.cube.cells+7*a.cube.cells; omega
    · exact le_rfl
    · exact le_rfl
    · exact fun i hi => starts i (card ▸ hi)
    · exact fun i hi => source _ _ (descriptors i (card ▸ hi))
    · intro i hi
      exact source _ _ ((output_windows a frame ctl count os global width i (card ▸ hi)).2.1.trans below)
    · intro i hi c hc
      have e := chunks i (card ▸ hi) c hc
      exact ⟨e.trans (by change a.before.limit≤a.before.limit+3*a.cube.cells+7*a.cube.cells; omega),.inl e⟩
    · exact fun i hi => sizes i (card ▸ hi)
  · exact fun i hi => (starts i hi).1

end RoutingISA.SignedTaskArena

end BorderVNP
end Computability
end OAI
