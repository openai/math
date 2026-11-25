import OAI.Computability.BorderVNP.CellSparseExteriorNativeBucket
import OAI.Computability.BorderVNP.RoutingISAFragmentArena

/-! # Numeric room and source preservation for real compressed cell windows -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.SparseExterior.Native

open VPVNP.BurstRAM FragmentBucket Diagonal.ExternalSew.Fragments

/-- The length-only fragment allocation makes every sorted descriptor, live
bit, report and output cursor fit. The compact cell extent can be bounded
using the binary gap encoding independently of the global number of cells. -/
theorem room_from_arena {w : ℕ} (a : FragmentArena.Layout) (c first tb outLen : ℕ)
    (ss : List Span) (tail : List Bool) (cell : c<a.cells) (rows : first+ss.length≤a.capacity)
    (sources : ∀ r ∈ ss, r.source+r.bits.length≤a.start) (reports : tb+tail.length≤a.start)
    (extent : outLen≤a.stride) (fits : a.limit≤2^w) :
    Room w (a.triples+3*first) tb (a.external+c*a.stride) outLen ss tail := by
  have prod := Nat.mul_le_mul_right a.stride (Nat.succ_le_of_lt cell)
  rw [Nat.succ_mul] at prod
  have scale := Nat.mul_le_mul_left 3 rows
  rw [Nat.mul_add] at scale
  have endTable : a.triples+3*first+3*ss.length≤a.external := by
    dsimp only [FragmentArena.Layout.external,FragmentArena.Layout.cursors]; omega
  have low : a.start≤a.external := by
    dsimp only [FragmentArena.Layout.external,FragmentArena.Layout.cursors,FragmentArena.Layout.triples,
      FragmentArena.Layout.pairs,FragmentArena.Layout.quads]; omega
  have endDst : a.external+c*a.stride+outLen<a.limit := by
    dsimp only [FragmentArena.Layout.limit,FragmentArena.Layout.counts]; omega
  have output := endDst.trans_le fits
  refine ⟨by omega,fun r hr => ?_,by omega,output,Or.inl (by omega),fun r hr => Or.inl ?_,Or.inl (by omega)⟩
  · have := sources r hr; omega
  · have := sources r hr; omega

/-- Every live and report bit preceding the bucket's three writable arrays
survives the full native count, prefix and scatter program. -/
theorem stored_from_initial {w : ℕ} {l : FragmentBucket.Layout} {tag : Fin l.rows → Fin l.cells}
    {before : NatState} {s : Bank w} {m : Memory w} (q : Fin l.rows → Quad) (data : ℕ → ℕ → Bool)
    (c : Fin l.cells) (qs : List Quad) (enumeration : List.ofFn q=qs) (owner : ∀ i, (tag i).val=(q i).cell)
    (result : Result l tag (fun i => FragmentRows.fieldValue (q i)) before (.ofWords s m))
    (reads : ∀ r ∈ spans qs data c.val, ∀ j : Fin r.bits.length, before.mem (r.source+j.val)=r.bits[j].toNat)
    (tb : ℕ) (tail : List Bool) (report : ∀ i : Fin tail.length, before.mem (tb+i.val)=tail[i].toNat)
    (bankEnd : ℕ) (banks : ∀ r ∈ spans qs data c.val, r.source+r.bits.length≤bankEnd) (reportEnd : tb+tail.length≤bankEnd)
    (separation : bankEnd≤l.pairs ∧ bankEnd≤l.triples ∧ bankEnd≤l.cursors) :
    Stored m (l.triples+3*start tag c.val) tb (spans qs data c.val) tail := by
  have keep (j : ℕ) (hj : j<bankEnd) : (m j).val=before.mem j :=
    result.other j (Or.inl (hj.trans_le separation.1)) (Or.inl (hj.trans_le separation.2.1))
      (Or.inl (hj.trans_le separation.2.2))
  apply stored_from_bucket q data c qs enumeration owner result _ tb tail
  · intro i hi
    rw [keep _ (by omega)]
    exact report ⟨i,hi⟩
  · intro r hr i hi
    have := banks r hr
    rw [keep _ (by omega)]
    exact reads r hr ⟨i,hi⟩

end RoutingISA.SparseExterior.Native

end BorderVNP
end Computability
end OAI
