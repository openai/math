import OAI.Computability.BorderVNP.CellSparseExteriorNativeRun
import OAI.Computability.BorderVNP.FragmentBucketProgram
import OAI.Computability.BorderVNP.FragmentRowsBucketInput

/-! # Feeding the actual stable-bucket output to the native sparse writer -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.SparseExterior.Native

open VPVNP.BurstRAM FragmentBucket Diagonal.ExternalSew.Fragments

/-- The chronological stable-bucket subsequence of the three producer passes
is the span list passed to the private restoration proof. -/
theorem span_list {l : FragmentBucket.Layout} (tag : Fin l.rows → Fin l.cells)
    (q : Fin l.rows → Quad) (data : ℕ → ℕ → Bool) (c : Fin l.cells) (qs : List Quad)
    (enumeration : List.ofFn q=qs) (owner : ∀ i, (tag i).val=(q i).cell) :
    ((List.finRange l.rows).filter (fun i => tag i=c)).map (fun i => (q i).span data) =
      spans qs data c.val := by
  rw [← enumeration,spans,List.ofFn_eq_map,List.filter_map,List.map_map]
  congr 2
  funext i
  change decide (tag i=c)=decide ((q i).cell=c.val)
  rw [← owner]
  by_cases e : tag i=c
  · simp [e]
  · simp [e]; exact fun h => e (Fin.ext h)

/-- The actual physical cell base and count, read from the two-word header
after the native stable scatter, are the start and length of its true spans. -/
theorem cell_header {l : FragmentBucket.Layout} {tag : Fin l.rows → Fin l.cells} {before z : NatState}
    (q : Fin l.rows → Quad) (data : ℕ → ℕ → Bool) (c : Fin l.cells) (qs : List Quad)
    (enumeration : List.ofFn q=qs) (owner : ∀ i, (tag i).val=(q i).cell)
    (result : Result l tag (fun i => FragmentRows.fieldValue (q i)) before z) :
    z.mem (l.pairs+2*c.val)=start tag c.val ∧
    z.mem (l.pairs+2*c.val+1)=(spans qs data c.val).length := by
  refine ⟨result.starts c,?_⟩
  rw [result.counts,←span_list tag q data c qs enumeration owner,←stable_cell]
  simp

/-- All three fields at every sorted word address are the actual logical
offset, physical source and length. Reading those true inputs gives precisely
the spans of the genuine emitted stream in their original order. -/
theorem rows_from_bucket {w : ℕ} {l : FragmentBucket.Layout} {tag : Fin l.rows → Fin l.cells}
    {before : NatState} {s : Bank w} {m : Memory w} (q : Fin l.rows → Quad) (data : ℕ → ℕ → Bool)
    (c : Fin l.cells) (qs : List Quad) (enumeration : List.ofFn q=qs) (owner : ∀ i, (tag i).val=(q i).cell)
    (result : Result l tag (fun i => FragmentRows.fieldValue (q i)) before (.ofWords s m))
    : ∀ i : Fin (spans qs data c.val).length,
      Row m (l.triples+3*start tag c.val+3*i.val) (spans qs data c.val)[i] := by
  let P (rs : List Span) := ∀ i : Fin rs.length, Row m (l.triples+3*start tag c.val+3*i.val) rs[i]
  change P (spans qs data c.val)
  rw [←span_list tag q data c qs enumeration owner,←stable_cell]
  let atSlot (k : Fin (count tag c)) := (dest tag).symm (cellPos tag c k)
  intro i
  let k : Fin (count tag c) := ⟨i.val,by simpa using i.isLt⟩
  have field (j : Fin 3) : readings m (l.triples+3*start tag c.val+3*i.val+j.val)=FragmentRows.fieldValue (q (atSlot k)) j := by
      have h := result.fields (atSlot k) j
      change readings m (l.triples+3*(dest tag (atSlot k)).val+j.val)=_ at h
      simpa [atSlot,cellPos_val,k,Nat.mul_add,Nat.add_assoc] using h
  have idx : ((List.finRange (count tag c)).map (fun k => (q (atSlot k)).span data))[i.val]
        =(q (atSlot k)).span data := by simp [k]
  change Row m _ (((List.finRange (count tag c)).map (fun k => (q (atSlot k)).span data))[i.val])
  rw [idx]
  exact ⟨field 0,field 1,(field 2).trans (by simp [FragmentRows.fieldValue,Quad.span,Quad.words])⟩

/-- All three fields at every sorted word address are the actual logical
offset, physical source and length. Reading those true inputs gives precisely
the spans of the genuine emitted stream in their original order. -/
theorem stored_from_bucket {w : ℕ} {l : FragmentBucket.Layout} {tag : Fin l.rows → Fin l.cells}
    {before : NatState} {s : Bank w} {m : Memory w} (q : Fin l.rows → Quad) (data : ℕ → ℕ → Bool)
    (c : Fin l.cells) (qs : List Quad) (enumeration : List.ofFn q=qs) (owner : ∀ i, (tag i).val=(q i).cell)
    (result : Result l tag (fun i => FragmentRows.fieldValue (q i)) before (.ofWords s m))
    (reads : ∀ r ∈ spans qs data c.val, r.Reads m)
    (tb : ℕ) (tail : List Bool) (report : CompactWrite.Source m tb tail) :
    Stored m (l.triples+3*start tag c.val) tb (spans qs data c.val) tail :=
  ⟨rows_from_bucket q data c qs enumeration owner result,reads,report⟩

end RoutingISA.SparseExterior.Native

end BorderVNP
end Computability
end OAI
