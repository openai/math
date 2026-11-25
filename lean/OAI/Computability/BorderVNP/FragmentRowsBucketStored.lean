import OAI.Computability.BorderVNP.FragmentRowsBucketProgram
import OAI.Computability.BorderVNP.CellSparseExteriorNativeArena
import OAI.Computability.BorderVNP.CellSparseExteriorBatchRun

/-! # Reading each cell's actual sparse exterior from the published directory -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.FragmentRows

open VPVNP.BurstRAM Diagonal.ExternalSew.Fragments

variable {l : Layout} {m : ℕ → ℕ} {w : ℕ} (fit : l.Fits w m)
variable (b : FragmentBucket.Layout) (count : b.rows=(l.stream m).length) (cells : b.cells=l.cells)
local notation "tag" => l.bucketTag fit b count cells
local notation "row" => l.bucketRow m b count

/-- Enumerating the physically published ordinals gives the producer's true source list. -/
theorem Layout.bucket_enumeration (l : Layout) (m : ℕ → ℕ) (b : FragmentBucket.Layout)
    (count : b.rows=(l.stream m).length) : List.ofFn (l.bucketRow m b count)=l.stream m := by
  rw [List.ofFn_congr count]
  exact List.ofFn_get (l.stream m)

/-- The actual global cell's original dense supplied pointer, width, compact header and
report suffix determine the native sparse exterior writer's row. -/
def Layout.bucketOwned (data : ℕ → ℕ → Bool) (c : Fin b.cells) (tail : List Bool) : SparseExterior.Owned :=
  ⟨c.val,m (l.host.cells+2*c.val+1),FragmentBucket.start tag c.val,
    ⟨m (l.supplied+c.val),spans (l.stream m) data c.val,tail⟩⟩

/-- A bucket result publishes the ordinal and number of the true source spans of the cell. -/
theorem Layout.bucket_header {before z : NatState} (data : ℕ → ℕ → Bool) (c : Fin b.cells)
    (result : FragmentBucket.Result b tag (fun i => fieldValue (row i)) before z) :
    z.mem (b.pairs+2*c.val)=FragmentBucket.start tag c.val ∧
      z.mem (b.pairs+2*c.val+1)=(spans (l.stream m) data c.val).length :=
  SparseExterior.Native.cell_header row data c _ (l.bucket_enumeration m b count) (fun _ => rfl) result

/-- The sorted memory supplies every physical triple of the cell's genuine source stream.
The individual live and report bits are read from the same memory as the triples. -/
theorem Layout.bucket_stored {before : NatState} {t : Bank w} {mt : Memory w}
    (data : ℕ → ℕ → Bool) (c : Fin b.cells) (tb : ℕ) (tail : List Bool)
    (result : FragmentBucket.Result b tag (fun i => fieldValue (row i)) before (.ofWords t mt))
    (read : ∀ q ∈ l.stream m, q.cell=c.val → ∀ j : Fin q.width, readings mt (q.source+j.val)=(data q.cell (q.start+j.val)).toNat)
    (report : CompactWrite.Source mt tb tail) :
    SparseExterior.Native.Stored mt (b.triples+3*FragmentBucket.start tag c.val) tb
      (spans (l.stream m) data c.val) tail := by
  apply SparseExterior.Native.stored_from_bucket row data c _ (l.bucket_enumeration m b count)
    (fun _ => rfl) result _ tb tail report
  intro r hr
  obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hr
  obtain ⟨hm,owner⟩ := List.mem_filter.mp hq
  exact Quad.span_reads _ _ _ (read q hm (of_decide_eq_true owner))

/-- The joined emitter and bucketer preserve each preceding physical word other
than the emitter's count publication. This applies to the original data lanes and the
guessed report suffix, as well as earlier header and task arrays. -/
theorem Layout.preserved_before_quads {before z : NatState} (image : before.mem=l.image m)
    (result : FragmentBucket.Result b tag (fun i => fieldValue (row i)) before z)
    (a : ℕ) (clear : a≠l.control+29) (low : a<l.quads)
    (separate : l.quads≤b.pairs ∧ l.quads≤b.triples ∧ l.quads≤b.cursors) : z.mem a=m a := by
  rw [result.other a (Or.inl (low.trans_le separate.1)) (Or.inl (low.trans_le separate.2.1))
    (Or.inl (low.trans_le separate.2.2)),image]
  exact FragmentArena.image_below l m a low clear

/-- Populate the native per-owned-cell traversal input from the actual stable bucket
result and the original dense task and header words. -/
theorem Layout.bucket_initial {before : NatState} {t : Bank w} {mt : Memory w}
    (data : ℕ → ℕ → Bool) (c : Fin b.cells) (tail : List Bool) (batch : SparseExterior.Layout)
    (i : ℕ) (pair : batch.pairs=b.pairs) (triple : batch.triples=b.triples)
    (result : FragmentBucket.Result b tag (fun j => fieldValue (row j)) before (.ofWords t mt)) :
    let o := Layout.bucketOwned fit b count cells data c tail
    readings mt (batch.six+6*i)=c.val → readings mt (batch.six+6*i+2)=o.field.width →
    readings mt (batch.tasks+7*i+2)=o.dense → readings mt (batch.tasks+7*i+3)=o.field.width+tail.length →
    (∀ q ∈ l.stream m, q.cell=c.val → ∀ j : Fin q.width, readings mt (q.source+j.val)=(data q.cell (q.start+j.val)).toNat) →
    CompactWrite.Source mt (o.dense+o.field.width) tail → o.Fits batch i w →
    SparseExterior.Ordered o.field.width 0 o.field.spans →
    SparseExterior.Native.Room w (batch.triples+3*o.first) (o.dense+o.field.width) (o.dest batch)
      o.field.bytes.length o.field.spans o.field.tail →
    o.Initial batch i mt := by
  intro o num width base size read report bound order room
  obtain ⟨first,length⟩ := Layout.bucket_header fit b count cells data c result
  refine ⟨⟨num,width,base,size,?_,?_⟩,?_,bound,order,room⟩
  · exact pair ▸ first
  · exact pair ▸ length
  · exact triple ▸ Layout.bucket_stored fit b count cells data c (o.dense+o.field.width) tail result read report

end RoutingISA.FragmentRows

end BorderVNP
end Computability
end OAI
