import OAI.Computability.BorderVNP.CellSparseExteriorNativeBatchArena
import OAI.Computability.BorderVNP.FragmentRowsBucketProgram

/-! # Initial native exterior task of a genuinely owned signed cell -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.SparseExterior

open FragmentBucket Diagonal.ExternalSew.Fragments VPVNP.BurstRAM
open private batch_regions from OAI.Computability.BorderVNP.CellSparseExteriorNativeBatchArena

variable {w : ℕ} (a : SignedTaskArena.Layout) (f : FragmentRows.Layout) (orig : ℕ → ℕ)
    (fit : f.Fits w orig) (cells : a.fragments.cells=f.cells)

local notation "B" => a.fragments.bucket (List.length (f.stream orig))
local notation "tagOf" => f.bucketTag fit B rfl cells
local notation "quadAt" => f.bucketRow orig B rfl

/-- Its true global ordinal, sorted triple start, dense bank and compact input. -/
noncomputable def emittedOwned (c : Fin a.fragments.cells) (data : ℕ → ℕ → Bool) (dense width : ℕ) (tail : List Bool) : Owned :=
  ⟨c.val,dense,start tagOf c.val,⟨width,spans (f.stream orig) data c.val,tail⟩⟩

/-- The bucket output plus the physical task and report scan supply every
precondition of the per-owned-cell writer. Only the assigned cell's data
words enter this statement. The other teams' inputs may differ. -/
theorem initial_from_emission (c : Fin a.fragments.cells) (data : ℕ → ℕ → Bool)
    (dense width : ℕ) (tail : List Bool) (frame ctl count i : ℕ) {before : NatState}
    (bankRegs : Bank w) (bucketMem m : Memory w)
    (result : Result B tagOf (fun j => FragmentRows.fieldValue (quadAt j)) before (.ofWords bankRegs bucketMem))
    (kept : ∀ addr, (a.fragments.pairs ≤ addr ∧ addr<a.fragments.pairs+2*a.fragments.cells) ∨
      (a.fragments.triples≤addr ∧ addr<a.fragments.triples+3*(f.stream orig).length) →
      readings m addr=readings bucketMem addr)
    (header : readings m (a.before.six+6*i)=c.val ∧ readings m (a.before.six+6*i+2)=width)
    (task : readings m ((a.tasks 0 0 0 0).tasks+7*i+2)=dense ∧
      readings m ((a.tasks 0 0 0 0).tasks+7*i+3)=width+tail.length)
    (ordered : Ordered width 0 (spans (f.stream orig) data c.val))
    (reads : ∀ r ∈ spans (f.stream orig) data c.val, r.Reads m)
    (reports : CompactWrite.Source m (dense+width) tail)
    (low : ∀ r ∈ spans (f.stream orig) data c.val, r.source+r.bits.length≤a.fragments.start)
    (tailLow : dense+width+tail.length≤a.fragments.start)
    (extent : (encode width tail 0 (spans (f.stream orig) data c.val)).length≤a.fragments.stride)
    (capacity : (f.stream orig).length≤a.fragments.capacity)
    (idx : i<a.cube.cells ∧ i<a.p.report.cells)
    (wide : 7<2^w) (high : (a.tasks 0 0 0 0).scratch<2^w) :
    (emittedOwned a f orig fit cells c data dense width tail).Initial (batchLayout a frame ctl count) i m := by
  let o := emittedOwned a f orig fit cells c data dense width tail
  let sp := spans (f.stream orig) data c.val
  let first := start tagOf c.val
  have enum : List.ofFn quadAt=f.stream orig := List.ofFn_getElem
  have own (j : Fin (f.stream orig).length) : (tagOf j).val=(quadAt j).cell := rfl
  obtain ⟨p,h⟩ := Native.cell_header quadAt data c (f.stream orig) enum own result
  change readings bucketMem (a.fragments.pairs+2*c.val)=first at p
  change readings bucketMem (a.fragments.pairs+2*c.val+1)=sp.length at h
  have num : FragmentBucket.count tagOf c = sp.length := (result.counts c).symm.trans h
  have past : first+sp.length≤(f.stream orig).length := by
    rw [←num]
    change start tagOf c.val+FragmentBucket.count tagOf c≤(f.stream orig).length
    exact (start_step tagOf c).symm.le.trans (start_le_rows tagOf (Nat.succ_le_of_lt c.isLt))
  have bankRows := Native.rows_from_bucket quadAt data c (f.stream orig) enum own result
  have inputRows : Native.Stored m (a.fragments.triples+3*first) (dense+width) sp tail := by
    refine ⟨?_,reads,reports⟩
    intro j
    have row := bankRows j
    have words (k : ℕ) (hk : k<3) :
        readings m (a.fragments.triples+3*first+3*j.val+k)=readings bucketMem (a.fragments.triples+3*first+3*j.val+k) := by
      have hi := j.isLt
      apply kept _ (.inr ⟨by omega,by omega⟩)
    exact ⟨(words 0 (by decide)).trans row.logical,(words 1 (by decide)).trans row.physical,
      (words 2 (by decide)).trans row.length⟩
  have layout := batch_regions a
  have scratch : (a.tasks 0 0 0 0).scratch=(a.tasks 0 0 0 0).tasks+7*a.cube.cells := rfl
  have lim : a.fragments.limit≤2^w := by omega
  have room := Native.room_from_arena a.fragments c.val first (dense+width) _ sp tail c.isLt
    (past.trans capacity) low tailLow extent lim
  have countEnd : a.fragments.counts+c.val<a.fragments.limit := by
    have := c.isLt
    dsimp only [FragmentArena.Layout.limit]; omega
  have tableFits := room.tableFits
  have tailFits := room.reportFits
  have outFits := room.outputFits
  have pairLo : a.fragments.pairs+2*a.fragments.cells≤a.fragments.triples := le_rfl
  have tripleLow : a.fragments.triples≤a.fragments.limit := by
    dsimp only [FragmentArena.Layout.limit,FragmentArena.Layout.counts,FragmentArena.Layout.external,
      FragmentArena.Layout.cursors]; omega
  have ci := c.isLt
  have firstKept := kept (a.fragments.pairs+2*c.val) (.inl ⟨by omega,by omega⟩)
  have secondKept := kept (a.fragments.pairs+2*c.val+1) (.inl ⟨by omega,by omega⟩)
  change o.Initial _ _ _
  refine ⟨⟨header.1,header.2,task.1,task.2,firstKept.trans p,secondKept.trans h⟩,inputRows,?_,ordered,room⟩
  refine ⟨wide,?_,?_,?_,?_,tailFits,outFits,?_,?_⟩
  · change a.before.six+6*i+2<2^w; omega
  · change (a.tasks 0 0 0 0).tasks+7*i+3<2^w; omega
  · change a.fragments.pairs+2*c.val+1<2^w; omega
  · change a.fragments.triples+3*(first+sp.length)<2^w
    rw [Nat.mul_add]; omega
  · change a.fragments.counts+c.val<2^w; omega
  · omega

end RoutingISA.SparseExterior

end BorderVNP
end Computability
end OAI
