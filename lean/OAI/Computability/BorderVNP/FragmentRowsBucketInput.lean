import OAI.Computability.BorderVNP.FragmentRowsProgram
import OAI.Computability.BorderVNP.FragmentBucketLayout

/-! # The native fragment producer supplies the counting sort's tagged input

The bucket pass reads the cell tag and three payload scalars directly from
the published quadruple array. Each accepted tag names a genuine cell.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.FragmentRows

open Diagonal.ExternalSew.Fragments

private theorem cable_cell_lt {l : Layout} {w : ℕ} {m : ℕ → ℕ} (fit : l.Fits w m)
    {i : ℕ} (hi : i<l.host.count) (side : Bool) {q : Quad} (eq : cable l.host m side i=some q) :
    q.cell<l.cells := by
  unfold cable at eq
  split at eq
  · contradiction
  · rename_i h
    obtain ⟨cross,wide⟩ := not_or.mp h
    cases eq
    exact fit.cableCell i hi side wide cross

/-- Every accepted source row carries an in-range destination cell. -/
theorem Layout.stream_cell {l : Layout} {w : ℕ} {m : ℕ → ℕ} (fit : l.Fits w m)
    {q : Quad} (mem : q ∈ l.stream m) : q.cell<l.cells := by
  simp only [Layout.stream,Diagonal.ExternalSew.Fragments.stream,List.mem_append,List.mem_filterMap] at mem
  rcases mem with (⟨i,hi,eq⟩|⟨i,hi,eq⟩)|⟨r,hr,eq⟩
  · exact cable_cell_lt fit (List.mem_range.mp hi) false eq
  · exact cable_cell_lt fit (List.mem_range.mp hi) true eq
  · obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hr
    unfold live at eq
    split at eq
    · cases eq
      exact fit.dataCell i (List.mem_range.mp hi)
    · contradiction

/-- Address a whole quadruple by its row ordinal in the flat scalar array. -/
theorem quad_at (m : ℕ → ℕ) (base : ℕ) (qs : List Quad)
    (rows : CellPacket.WordsAt m base (qs.flatMap Quad.words)) (i : Fin qs.length) :
    CellPacket.WordsAt m (base+4*i.val) qs[i.val].words := by
  induction qs generalizing base with
  | nil => exact i.elim0
  | cons q qs ih =>
    change CellPacket.WordsAt m base (q.words++qs.flatMap Quad.words) at rows
    refine Fin.cases ?_ (fun k => ?_) i
    · simpa using rows.left
    · have tail := ih (base+q.words.length) rows.right k
      simpa [Quad.words,Nat.mul_succ,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] using tail

/-- Exact payload consumed by the native bucketer in its three field positions. -/
def fieldValue (q : Quad) (j : Fin 3) : ℕ := q.words[1+j.val]'(by simp [Quad.words]; omega)

/-- The source row of the stream at an ordinal of the published bucket array. -/
def Layout.bucketRow (l : Layout) (m : ℕ → ℕ) (b : FragmentBucket.Layout)
    (count : b.rows=(l.stream m).length) (i : Fin b.rows) : Quad := (l.stream m)[(i.cast count).val]

/-- In-range tagged cell of the actual stream row used in the bucket scan. -/
def Layout.bucketTag {l : Layout} {m : ℕ → ℕ} {w : ℕ} (fit : l.Fits w m)
    (b : FragmentBucket.Layout) (count : b.rows=(l.stream m).length) (cells : b.cells=l.cells)
    (i : Fin b.rows) : Fin b.cells :=
  ⟨(l.bucketRow m b count i).cell,cells ▸ Layout.stream_cell fit (List.getElem_mem _)⟩

/-- After the fragment producer, the actual quadruple bank satisfies the typed bucket
program's complete input contract, including when no row survived the scans. -/
theorem Layout.bucket_input {l : Layout} {m : ℕ → ℕ} {w : ℕ} (fit : l.Fits w m)
    (b : FragmentBucket.Layout) (base : b.quads=l.quads) (count : b.rows=(l.stream m).length)
    (cells : b.cells=l.cells) :
    b.Input (l.bucketTag fit b count cells) (fun i => fieldValue (l.bucketRow m b count i)) (l.image m) := by
  have row (i : Fin b.rows) : CellPacket.WordsAt (l.image m) (b.quads+4*i.val) (l.bucketRow m b count i).words :=
    base ▸ quad_at _ _ _ (l.image_quads m fit) (i.cast count)
  constructor
  · intro i
    simpa [Layout.bucketTag,Quad.words] using row i ⟨0,by simp [Quad.words]⟩
  · intro i j
    simpa only [fieldValue,Nat.add_assoc] using row i ⟨1+j.val,by simp [Quad.words]; omega⟩

end RoutingISA.FragmentRows

end BorderVNP
end Computability
end OAI
