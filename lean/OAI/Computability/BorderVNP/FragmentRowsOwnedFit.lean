import OAI.Computability.BorderVNP.FragmentRowsBucketStored
import OAI.Computability.BorderVNP.FragmentRowsArenaBounds
import OAI.Computability.BorderVNP.CellSparseExteriorNativeOwned
import OAI.Computability.BorderVNP.DiagonalTallyAllocatedTaskSource

/-! # Physical window bounds for an owned cell in the signed cube allocation -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.FragmentRows

open VPVNP.BurstRAM SparseExterior Diagonal.ExternalSew.Fragments

private theorem ordered_stop {width pos : ℕ} {rs : List Span} (h : Ordered width pos rs)
    {r : Span} (hr : r ∈ rs) : r.stop≤width := by
  induction rs generalizing pos with
  | nil => contradiction
  | cons x xs ih =>
    rcases List.mem_cons.mp hr with rfl|ht
    · exact Native.ordered_bound h.2
    · exact ih h.2 ht

variable {w : ℕ} (a : SignedTaskArena.Layout) (f : FragmentRows.Layout) (orig : ℕ → ℕ)
    (fit : f.Fits w orig) (cells : a.fragments.cells=f.cells)
local notation "B" => a.fragments.bucket (List.length (f.stream orig))
local notation "tagOf" => f.bucketTag fit B rfl cells
local notation "quadAt" => f.bucketRow orig B rfl

/-- Every stored fragment of this cell and the raw suffix lie inside its true
fixed-stride cube bank, below the fragment arena. -/
theorem owned_bank_bounds (c : Fin a.fragments.cells) (data : ℕ → ℕ → Bool) (tail : List Bool)
    (bank : orig (f.host.cells+2*c.val+1)=a.cube.cellBank+c.val*a.cube.cellStride)
    (full : orig (f.supplied+c.val)+tail.length≤a.cube.cellStride)
    (ordered : Ordered (orig (f.supplied+c.val)) 0 (spans (f.stream orig) data c.val)) :
    (∀ r ∈ spans (f.stream orig) data c.val, r.source+r.bits.length≤a.fragments.start) ∧
      orig (f.host.cells+2*c.val+1)+orig (f.supplied+c.val)+tail.length≤a.fragments.start := by
  have hmul := Nat.mul_le_mul_right a.cube.cellStride (show c.val+1≤a.cube.cells from c.isLt)
  rw [Nat.succ_mul] at hmul
  have cap := (arena_order a).2.2.1
  change a.cube.cellBank+a.cube.cells*a.cube.cellStride≤a.fragments.start at cap
  constructor
  · intro r hr
    have size := ordered_stop ordered hr
    obtain ⟨q,member,rfl⟩ := List.mem_map.mp hr
    obtain ⟨qmem,tag⟩ := List.mem_filter.mp member
    have qc : q.cell=c.val := of_decide_eq_true tag
    have pos := (stream_located f.host orig _ _ q qmem).2
    rw [qc,bank] at pos
    simp only [Span.stop,Quad.span,List.length_ofFn] at size ⊢
    omega
  · omega

private theorem scratch_below (a : SignedTaskArena.Layout) (w u v k : ℕ) :
    (a.tasks 0 0 0 0).scratch≤a.endAddress w u v k := by
  have last := (a.task_bounds 0 0 0 0).2.2.1
  have bursts : (a.tasks 0 0 0 0).scratch≤(a.tasks 0 0 0 0).bursts := Nat.le_add_right ..
  have before : a.after.start≤a.after.localBase := by
    rw [DiagonalTallyAllocation.AfterTasks.localBase,a.after.footprint]; omega
  dsimp only [SignedTaskArena.Layout.endAddress,SignedTaskArena.Layout.entry,DiagonalResidueRAM.gateBase,
    SignedTaskArena.Layout.valuation,SignedTaskArena.Layout.tallyBits]
  omega

/-- Real source addresses, row capacity and every task fit follow from the physical
cube bank, the occupied row counts, and the signed arena's single high-water bound. -/
theorem owned_initial_in_arena (c : Fin a.fragments.cells) (data : ℕ → ℕ → Bool) (tail : List Bool)
    (frame ctl count i u v k : ℕ) {before : NatState} (regs : Bank w) (bucketMem now : Memory w)
    (result : FragmentBucket.Result B tagOf (fun j => fieldValue (quadAt j)) before (.ofWords regs bucketMem))
    (kept : ∀ addr, (a.fragments.pairs≤addr ∧ addr<a.fragments.pairs+2*a.fragments.cells) ∨
      (a.fragments.triples≤addr ∧ addr<a.fragments.triples+3*(f.stream orig).length) →
        readings now addr=readings bucketMem addr)
    (bank : orig (f.host.cells+2*c.val+1)=a.cube.cellBank+c.val*a.cube.cellStride)
    (full : orig (f.supplied+c.val)+tail.length≤a.cube.cellStride)
    (cables : f.host.count=a.cube.cables) (raw : f.count≤a.cube.maxRows)
    (idx : i<a.cube.cells ∧ i<a.p.report.cells) (high : a.endAddress w u v k<2^w) :
    let dense := orig (f.host.cells+2*c.val+1)
    let width := orig (f.supplied+c.val)
    let ss := spans (f.stream orig) data c.val
    readings now (a.before.six+6*i)=c.val → readings now (a.before.six+6*i+2)=width →
    readings now ((a.tasks 0 0 0 0).tasks+7*i+2)=dense →
    readings now ((a.tasks 0 0 0 0).tasks+7*i+3)=width+tail.length →
    Ordered width 0 ss → (∀ r ∈ ss, r.Reads now) → CompactWrite.Source now (dense+width) tail →
    (encode width tail 0 ss).length≤a.fragments.stride →
    (emittedOwned a f orig fit cells c data dense width tail).Initial (batchLayout a frame ctl count) i now := by
  intro dense width ss num wid base len ordered reads reports extent
  obtain ⟨sources,tailFits⟩ := owned_bank_bounds a f orig c data tail bank full ordered
  have rows := stream_length f.host orig (fun c => orig (f.supplied+c)) ((List.range f.count).map (f.row orig))
  simp only [List.length_map,List.length_range,cables] at rows
  change (f.stream orig).length≤2*a.cube.cables+f.count at rows
  have capacity : (f.stream orig).length≤a.fragments.capacity := by
    change (f.stream orig).length≤2*a.cube.cables+a.cube.maxRows+1; omega
  exact initial_from_emission a f orig fit cells c data dense width tail frame ctl count i regs bucketMem now
    result kept ⟨num,wid⟩ ⟨base,len⟩ ordered reads reports sources tailFits extent capacity idx
    (by have := fit.head; omega) ((scratch_below a w u v k).trans_lt high)

end RoutingISA.FragmentRows

end BorderVNP
end Computability
end OAI
