import OAI.Computability.BorderVNP.DiagonalExternalTileRows

/-! # Nonoverlap of the frozen positive old-word fragments within a retained tile -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal.ExternalSew.TileRuns

open scoped Classical
variable {R r w link g V : ℕ}

private def slotKind : Option (Slot R r w link g) → Kind R r w link g
  | none => .zero
  | some (.inl _) => .free
  | some (.inr (s,⟨c,_⟩)) => .cable s c

private theorem kind_read {u : Fin (R+1)} {tile : ℕ} {q : Kind R r w link g} {i : ℕ} {k : Fin g}
    (h : Reads u tile q i k) : slotKind (lookup u tile k) = q := by
  cases q with
  | zero => exact congrArg slotKind h
  | free => obtain ⟨f,e⟩ := h; exact congrArg slotKind e
  | cable s c => obtain ⟨j,_,e⟩ := h; exact congrArg slotKind e

variable (u : Fin (R+1)) (tile : Fin V) (copies old : ℕ) (hg : 0 < g) (small : g ≤ link)
    (room : r*(2*w+R*link) ≤ V*g)
local notation "rs" => runs (r := r) (w := w) u tile.val hg small

private theorem disjoint_run {a b : Run R r w link g u tile.val} (ha : a ∈ rs) (hb : b ∈ rs)
    (ne : a ≠ b) (pa : 0 < a.width) (pb : 0 < b.width) :
    a.first+a.width ≤ b.first ∨ b.first+b.width ≤ a.first := by
  by_contra! overlap
  let j := max a.first b.first
  have ja : a.first ≤ j := le_max_left ..
  have jb : b.first ≤ j := le_max_right ..
  have ja' : j < a.first+a.width := max_lt (by omega) overlap.1
  have jb' : j < b.first+b.width := max_lt overlap.2 (by omega)
  let k : Fin g := ⟨j,ja'.trans_le a.fit⟩
  have eA := kind_read (a.read (j-a.first) (by omega) k (by change j = _; omega))
  have eB := kind_read (b.read (j-b.first) (by omega) k (by change j = _; omega))
  exact ne (List.inj_on_of_nodup_map (runs_nodup_kind u tile.val hg small) ha hb (eA.symm.trans eB))

/-- Only positive-length operands are sent to the public fragment sorter. -/
noncomputable def occupiedRows : List CopyRow :=
  ((rs).filter (fun q => 0 < q.width)).map (copyRow u tile copies old hg small room)

/-- Deleting empty clamp or free runs preserves the six-row capacity. -/
theorem occupiedRows_length : (occupiedRows u tile copies old hg small room).length ≤ 6 := by
  simp only [occupiedRows,List.length_map]
  exact (List.length_filter_le ..).trans (runs_length u tile.val hg small)

/-- All enabled range operands are positive. -/
theorem occupiedRows_positive {a : CopyRow} (h : a ∈ occupiedRows u tile copies old hg small room) :
    0 < a.width := by
  obtain ⟨q,mem,rfl⟩ := List.mem_map.mp h
  change 0 < q.width
  simpa only [decide_eq_true_eq] using (List.mem_filter.mp mem).2

/-- The authentic old-port ranges are disjoint in their frozen producer order, before sorting. -/
theorem occupiedRows_disjoint : (occupiedRows u tile copies old hg small room).Pairwise fun a b =>
    a.oldOffset+a.width ≤ b.oldOffset ∨ b.oldOffset+b.width ≤ a.oldOffset := by
  rw [occupiedRows,List.pairwise_map]
  have uniq := (runs_nodup_kind (r := r) (w := w) u tile.val hg small).of_map Run.kind
  have keep := uniq.filter (fun q => decide (0 < q.width))
  apply keep.imp_of_mem
  intro a b ha hb hn
  obtain ⟨am,ap⟩ := List.mem_filter.mp ha
  obtain ⟨bm,bp⟩ := List.mem_filter.mp hb
  have e := disjoint_run u tile hg small am bm hn (of_decide_eq_true ap) (of_decide_eq_true bp)
  change u.val%copies*g+a.first+a.width ≤ u.val%copies*g+b.first ∨
    u.val%copies*g+b.first+b.width ≤ u.val%copies*g+a.first
  omega

/-- Every original lane is retained after suppression of zero-width operands. -/
theorem occupiedRows_cover (k : Fin g) :
    ∃ q ∈ rs, ∃ row ∈ occupiedRows u tile copies old hg small room,
      row = copyRow u tile copies old hg small room q ∧ ∃ i < row.width,
        u.val%copies*g+k.val = row.oldOffset+i ∧ Reads u tile.val q.kind i k := by
  obtain ⟨q,hm,i,hi,hk⟩ := runs_cover (r := r) (w := w) u tile.val hg small k
  have positive : 0 < q.width := Nat.zero_lt_of_lt hi
  refine ⟨q,hm,_,List.mem_map.mpr ⟨q,List.mem_filter.mpr ⟨hm,decide_eq_true positive⟩,rfl⟩,rfl,i,hi,?_,q.read i hi k hk⟩
  change u.val%copies*g+k.val = u.val%copies*g+q.first+i
  omega

end Diagonal.ExternalSew.TileRuns

end BorderVNP
end Computability
end OAI
