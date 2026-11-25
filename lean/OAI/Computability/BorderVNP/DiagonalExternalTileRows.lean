import OAI.Computability.BorderVNP.DiagonalExternalTileRuns
import OAI.Computability.BorderVNP.DiagonalExternalSewOrdinal

/-! # Length-dependent frozen operands for reconstructing one grouped input tile

A previous group packs `copies` old teams into each of its ports. A retained free
interval uses the ordinary new team/tile port. A physical exterior interval uses
the actual appended cable ID and its genuine low or high endpoint.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal.ExternalSew.TileRuns

variable {R r w link g V : ℕ}

/-- The sparse directory coordinate needed by a site's interval record. -/
inductive Target
  /-- Pin the old range to zero. -/
  | zero
  /-- Copy an interval in an actual free port of the new network. -/
  | port (ordinal : ℕ)
  /-- Copy a range at the specified end of the appended cable. -/
  | wire (side : Bool) (ordinal : ℕ)
  deriving DecidableEq

/-- Numeric metadata for a single tile-copy range. All positions are relative to their respective port or edge. -/
structure CopyRow where
  /-- ID of the old grouped port in copy-group then tile order. -/
  oldPort : ℕ
  /-- Which original team within the grouped port. -/
  copy : ℕ
  /-- First original lane in the complete grouped port. -/
  oldOffset : ℕ
  /-- Number of consecutive original lanes reconstructed by this row. -/
  width : ℕ
  /-- Sparse port or wire coordinate in the sewn layout. -/
  target : Target
  /-- First lane within that new port or wire. -/
  newOffset : ℕ
  deriving DecidableEq

variable (u : Fin (R+1)) (tile : Fin V) (copies old : ℕ) (hg : 0 < g) (small : g ≤ link)
    (room : r*(2*w+R*link) ≤ V*g)

/-- Encode the physically named new cable or port in the frozen range descriptor. -/
def copyRow (q : Run R r w link g u tile.val) : CopyRow :=
  let tgt := match q.kind with
    | .zero => Target.zero
    | .free => Target.port (u.val*V+tile.val)
    | .cable s c => Target.wire s (FourSlot.pieceOrdinal old V hg small (by omega) room c).val
  let dst := match q.kind with
    | .free => q.first
    | _ => 0
  ⟨u.val/copies*V+tile.val,u.val%copies,u.val%copies*g+q.first,q.width,tgt,dst⟩

/-- The bounded frozen row list for one actual old group-port copy. -/
noncomputable def copyRows : List CopyRow :=
  (runs u tile.val hg small).map (copyRow u tile copies old hg small room)

/-- Six rows suffice even for a tile that straddles a processor boundary. -/
theorem copyRows_length : (copyRows u tile copies old hg small room).length ≤ 6 := by
  rw [copyRows,List.length_map]
  exact runs_length u tile.val hg small

/-- All encoded offsets fit the full port of the previous copy group. -/
theorem copyRow_oldFit (positive : 0 < copies) (q : Run R r w link g u tile.val) :
    let row := copyRow u tile copies old hg small room q
    row.oldOffset+row.width ≤ copies*g := by
  have fit := q.fit
  have bound := Nat.mul_le_mul_right g (Nat.succ_le_of_lt (Nat.mod_lt u.val positive))
  rw [Nat.succ_mul] at bound
  change u.val%copies*g+q.first+q.width ≤ copies*g
  omega

/-- The frozen free-port ordinal is the real port name and each offset is the authentic delivered lane. -/
theorem copyRow_free (q : Run R r w link g u tile.val) (h : q.kind = .free)
    (i : ℕ) (hi : i < q.width) (k : Fin g) (hk : k.val = q.first+i) :
    let row := copyRow u tile copies old hg small room q
    ∃ f : FreePort R r w, lookup (link := link) u tile.val k = some (.inl f) ∧
      freeLane hg room f = ⟨(u,tile),k⟩ ∧
      row.target = .port (finProdFinEquiv (u,tile)).val ∧ row.newOffset+i = k.val := by
  have read := q.read i hi k hk
  rw [h] at read
  obtain ⟨f,hf⟩ := read
  refine ⟨f,hf,lookup_free_lane hg room u tile k f hf,?_,?_⟩
  · simp only [copyRow,h,finProdFinEquiv_apply_val]
    congr 1
    ac_rfl
  · simpa only [copyRow,h] using hk.symm

/-- The appended sparse cable and its side identify the actual bit copied into the old grouped port. -/
theorem copyRow_cable (q : Run R r w link g u tile.val) (s : Bool) (c : Cables R r w link g)
    (h : q.kind = .cable s c) (i : ℕ) (hi : i < q.width) (k : Fin g) (hk : k.val = q.first+i) :
    let row := copyRow u tile copies old hg small room q
    ∃ j : Fin (cableWidth c), lookup u tile.val k = some (.inr (s,⟨c,j⟩)) ∧
      row.target = .wire s (FourSlot.pieceOrdinal old V hg small (by omega) room c).val ∧ row.newOffset+i=j.val := by
  have read := q.read i hi k hk
  rw [h] at read
  obtain ⟨j,hj,hj'⟩ := read
  exact ⟨j,hj',by simp [copyRow,h],by simp [copyRow,h,hj]⟩

/-- A zero-clamp descriptor only covers positions outside the genuine processor array. -/
theorem copyRow_zero (q : Run R r w link g u tile.val) (h : q.kind = .zero)
    (i : ℕ) (hi : i < q.width) (k : Fin g) (hk : k.val = q.first+i) :
    lookup (r := r) (w := w) (link := link) u tile.val k = none ∧ (copyRow u tile copies old hg small room q).target = .zero := by
  have read := q.read i hi k hk
  rw [h] at read
  exact ⟨read,by simp [copyRow,h]⟩

/-- The old copy-index and within-copy offset account for every original grouped input lane. -/
theorem copyRows_cover (k : Fin g) :
    ∃ q ∈ runs (r := r) (w := w) u tile.val hg small, ∃ row ∈ copyRows u tile copies old hg small room,
      row = copyRow u tile copies old hg small room q ∧ ∃ i < row.width,
        u.val%copies*g+k.val = row.oldOffset+i ∧ Reads u tile.val q.kind i k := by
  obtain ⟨q,mem,i,hi,eq⟩ := runs_cover (r := r) (w := w) u tile.val hg small k
  exact ⟨q,mem,_,List.mem_map.mpr ⟨q,mem,rfl⟩,rfl,i,hi,by change _ = _+q.first+i; omega,q.read i hi k eq⟩

end Diagonal.ExternalSew.TileRuns

end BorderVNP
end Computability
end OAI
