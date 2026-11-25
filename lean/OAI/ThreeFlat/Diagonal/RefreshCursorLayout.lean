import OAI.ThreeFlat.Diagonal.NavigationDirectory
import OAI.ThreeFlat.Diagonal.RefreshArchiveLayout
import OAI.ThreeFlat.Diagonal.RefreshPreparationImage
import OAI.ThreeFlat.RAM.HeaderScanLayout

namespace OAI
/-! # The chronological allocator instantiates both refresh span certificates -/

namespace ThreeFlat.Diagonal.RefreshStageNav

open Computability.VPVNP.BurstRAM PrivateRAM RAM RAM.HeaderScan NavigationDirectory RefreshDemandRows

variable {W : ℕ} (cur : Word W) (mem : Memory W)

def oldColumns (c : Cursor) (v d : ℕ) : SlotImage.Columns := ⟨c.graph,v*d,c.width⟩

def nextColumns (p : Entry) (v d h pad : ℕ) : SlotImage.Columns := ⟨p.next.graph,v*d*(1+h+pad),p.next.width⟩

/-- Cursor inequalities needed at every chronological stage. Existing arrays
and packed histograms are disjoint from the next fresh heap allocation;
the fixed control block follows the complete allocation. -/
structure CursorSpace (c : Cursor) (K v a t h pad : ℕ) : Prop where
  header : Scans.Header cur mem c.header 63 (allocate K c (.refresh v (mPort a) (2^t) h pad)).words
  graph : c.graph+6*(v*mPort a)≤c.heap
  widths : c.width+v*mPort a*(mPort a*2^t)≤c.heap
  counts : c.dense+v*2^t*K≤c.heap
  earlier : c.header+64≤c.heap
  controls : (allocate K c (.refresh v (mPort a) (2^t) h pad)).next.heap≤cur.val

namespace CursorSpace

variable {cur mem} {c : Cursor} {K v a t h pad : ℕ}
    (u : CursorSpace cur mem c K v a t h pad)
set_option quotPrecheck false
local notation "d" => mPort a
local notation "entry" => allocate K c (.refresh v d (2^t) h pad)
local notation "old" => oldColumns c v d
local notation "new" => nextColumns entry v d h pad

include u in
theorem read (i : ℕ) (hi : i≤63) : info (fun i => (mem i).val) cur i=(entry).words i := by
  change (mem ((mem cur.val).val+i)).val=_
  rw [u.header.pointer,u.header.values _ hi]

private abbrev X := RefreshStageLayout.counts v d (2^t) h pad

theorem ordered :
    c.heap+3*(v*2^t)=(entry).words 3 ∧
    (entry).words 3+v*2^t*d*h=(entry).words 12 ∧
    (entry).words 12+3*(old).rows=(new).graph ∧
    (new).graph+6*(new).rows=(new).widths ∧
    (new).widths+v*d*(1+h+pad)*2^t≤(entry).next.heap := by
  refine ⟨rfl,rfl,rfl,rfl,?_⟩
  change _≤RefreshStageLayout.extraEnd _ _ _
  rw [RefreshStageLayout.extra_extent]
  exact Nat.le_add_right _ _

include u in
theorem prepare : PreparationLayout cur mem v a t old ((entry).words 12) c.heap := by
  obtain ⟨h1,h2,h3,h4,h5⟩ := ordered (c:=c) (K:=K) (v:=v) (a:=a) (t:=t) (h:=h) (pad:=pad)
  have ptr := u.header.pointer
  have cap := cur.isLt
  have last := u.controls
  have hOld := u.graph
  have hWidth := u.widths
  have hHead := u.earlier
  refine ⟨by have := u.header.fit; omega,u.read 8 (by decide),u.read 9 (by decide),u.read 10 (by decide),
    u.read 11 (by decide),u.read 12 (by decide),u.read 13 (by decide),u.read 2 (by decide),
    u.read 18 (by decide),?_,?_,?_,?_,?_,?_⟩
  · change c.graph+6*(v*d)≤_
    omega
  · change c.width+v*d*(d*2^t)≤_
    omega
  · omega
  · omega
  · intro i hi
    change i<(entry).words 12 ∨ (entry).words 12+3*(old).rows≤ i
    change i=cur.val ∨ _≤ i ∧ i≤_+19 ∨ c.graph≤ i ∧ i<c.graph+6*(v*d) ∨ c.width≤ i ∧ i<c.width+v*d*(d*2^t) at hi
    omega
  · intro i hi
    change i<c.heap ∨ c.heap+3*(v*2^t)≤ i
    change i=cur.val ∨ _≤ i ∧ i≤_+19 ∨ c.graph≤ i ∧ i<c.graph+6*(v*d) ∨ c.width≤ i ∧ i<c.width+v*d*(d*2^t) ∨
      (entry).words 12≤ i ∧ i<(entry).words 12+3*(old).rows at hi
    omega

include u in
theorem archive : Archive cur mem v a t h pad old new ((entry).words 12) K ((entry).words 3) := by
  obtain ⟨h1,h2,h3,h4,h5⟩ := ordered (c:=c) (K:=K) (v:=v) (a:=a) (t:=t) (h:=h) (pad:=pad)
  have ptr := u.header.pointer
  have cap := cur.isLt
  have last := u.controls
  have hOld := u.graph
  have hWidth := u.widths
  have hHead := u.earlier
  have hDense := u.counts
  have dEq : info (fun i => (mem i).val) cur 1=c.dense := u.read 1 (by decide)
  refine ⟨by have := u.header.fit; omega,u.read 14 (by decide),u.read 15 (by decide),
    u.read 16 (by decide),rfl,u.read 19 (by decide),u.read 17 (by decide),u.read 3 (by decide),
    u.read 20 (by decide),?_,?_,?_,?_,?_,?_,Or.inl h4.le,?_,?_⟩
  · omega
  · omega
  · omega
  · change c.graph+6*(v*d)<_
    omega
  · omega
  · rw [dEq]
    omega
  · intro i hi
    change (i<(new).graph ∨ (new).graph+6*(new).rows≤ i) ∧ (i<(new).widths ∨ (new).widths+v*d*(1+h+pad)*2^t≤ i)
    change (i=cur.val ∨ _≤ i ∧ i≤_+19 ∨ c.graph≤ i ∧ i<c.graph+6*(v*d) ∨ c.width≤ i ∧ i<c.width+v*d*(d*2^t) ∨
      (entry).words 12≤ i ∧ i<(entry).words 12+3*(old).rows) ∨ i=_+20 ∨ info (fun i => (mem i).val) cur 1≤ i ∧ i< info (fun i => (mem i).val) cur 1+v*2^t*K at hi
    rw [dEq] at hi
    omega
  · intro i hi
    change i<(entry).words 3 ∨ (entry).words 3+v*2^t*d*h≤ i
    omega


end CursorSpace
end ThreeFlat.Diagonal.RefreshStageNav

end OAI
