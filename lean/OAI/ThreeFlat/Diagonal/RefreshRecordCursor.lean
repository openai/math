import OAI.ThreeFlat.Diagonal.RefreshCursorLayout
import OAI.ThreeFlat.Diagonal.RefreshRecordImage
import OAI.ThreeFlat.Diagonal.RefreshScanPlan

namespace OAI
/-! # The canonical cursor supplies every retained refresh-node array -/

namespace ThreeFlat.Diagonal.RefreshStageNav

open Computability.VPVNP.BurstRAM PrivateRAM Computability.VPVNP.Compression RAM RAM.HeaderScan NavigationDirectory
open RefreshDemandRows CompressorPacking.Native
open scoped Fin.CommRing

namespace CursorSpace

variable {W v a t h pad K : ℕ} {cur : Word W} {mem : Memory W} {c : Cursor}
    (u : CursorSpace cur mem c K v a t h pad)
set_option quotPrecheck false
local notation "m" => mPort a
local notation "d" => 1+h+pad
local notation "N" => v*m*2^t
local notation "entry" => allocate K c (.refresh v m (2^t) h pad)
local notation "new" => nextColumns entry v m h pad
local notation "memN" => fun i=>(mem i).val

def recordPointers (e : Entry) : Records.Pointers :=
  ⟨e.words 34,e.words 36,e.words 38,e.words 40,e.words 2,e.words 1⟩

local notation "P" => recordPointers entry

include u in
theorem record_table (q : Records.Table) : info memN cur q.start=(P).dst q := by
  exact (u.read q.start (by cases q <;> decide)).trans (by cases q <;> rfl)

include u in
theorem record_length (q : Records.Table) :
    info memN cur (q.start+1)=Records.length v m t d q := by
  rw [u.read _ (by cases q <;> decide)]
  cases q <;> dsimp only [Records.length,Records.Table.cols] <;> change _*N=N*_ <;> ac_rfl

theorem record_layout :
    (P).kernel=(new).widths+v*m*d*2^t ∧
    (P).kernel+N*5=(P).motif ∧ (P).motif+N*6=(P).headers ∧ (P).headers+N*2=(P).halves ∧
    (P).halves+N*(8*d)≤(entry).next.heap := by
  refine ⟨rfl,?_,?_,?_,?_⟩
  · change _+N*5=_+5*N
    rw [Nat.mul_comm N]; rfl
  · change _+N*6=_+6*N
    rw [Nat.mul_comm N]; rfl
  · change _+N*2=_+2*N
    rw [Nat.mul_comm N]; rfl
  · change _≤RefreshStageLayout.extraEnd _ _ _
    rw [RefreshStageLayout.extra_extent]
    change _+5*N+6*N+2*N+N*(8*d)≤_+(15+8*d)*N
    rw [Nat.add_mul,Nat.mul_comm N (8*d)]
    omega

include u in
theorem record_alloc : Records.Allocation W cur.val c.header P new v m t d := by
  obtain ⟨h1,h2,h3,h4,h5⟩ := record_layout (c:=c) (K:=K) (v:=v) (a:=a) (t:=t) (h:=h) (pad:=pad)
  obtain ⟨h6,h7,h8,h9,_⟩ := ordered (c:=c) (K:=K) (v:=v) (a:=a) (t:=t) (h:=h) (pad:=pad)
  have controls := u.controls
  have b := cur.isLt
  have cHead := u.earlier
  have cChoice : (P).choices=c.heap := rfl
  constructor
  · intro q
    cases q <;> dsimp only [Records.Pointers.dst,Records.length,Records.Table.cols] <;> omega
  · intro q i hi
    change i=cur.val ∨ c.header≤ i ∧ i≤c.header+41 ∨ (P).choices≤ i ∧ i<(P).choices+3*(v*2^t) ∨
      (new).graph≤ i ∧ i<(new).graph+6*(new).rows ∨ (new).widths≤ i ∧ i<(new).widths+v*m*d*2^t at hi
    cases q <;> dsimp only [apart,Records.Pointers.dst,Records.length,Records.Table.cols] <;> omega
  · intro q r ne i lo hi
    cases q <;> cases r <;> first | exact (ne rfl).elim |
      (dsimp only [Records.Pointers.dst,Records.length,Records.Table.cols] at lo hi;
        dsimp only [apart,Records.Pointers.dst,Records.length,Records.Table.cols]; omega)

include u in
theorem record_data {G : LiftedSlots (Fin v × Fin m) d (BitWord t)}
    {w : SlotImage.Edge (Fin v × Fin m) (BitWord t) d→ℕ} (read : ℕ→ℕ)
    (image : SlotImage.Stored G finProdFinEquiv (tagOrdinal t) new memN w)
    (choice : ∀ i,c.heap≤ i → i<c.heap+3*(v*2^t) → (mem i).val=read i) :
    Records.Data cur mem c.header P new G w read := by
  refine ⟨u.header.pointer,by have := u.header.fit; omega,u.record_table,u.record_length,
    u.read 1 (by decide),u.read 2 (by decide),u.read 8 (by decide),u.read 14 (by decide),
    u.read 15 (by decide),u.read 19 (by decide),image,choice⟩

include u in
theorem record_limits (sm : 6<2^W) (ports : m<2^W) (degree : 2*d<2^W) (lanes : 2^t<2^W) :
    Records.Limits W v m t d P new := by
  have bound := u.prepare
  have ar := u.archive
  exact ⟨sm,ports,degree,lanes,bound.choiceCap.le,ar.graphFit.le,ar.widthFit.le⟩


end CursorSpace
end ThreeFlat.Diagonal.RefreshStageNav

end OAI
