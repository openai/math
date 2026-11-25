import OAI.ThreeFlat.Diagonal.TickHistoryChronology
import OAI.ThreeFlat.Diagonal.ClippedPairBuckets

namespace OAI
/-! # The chronological transfer for the clipped original cursor buckets -/

noncomputable section
namespace ThreeFlat.Diagonal.TickPhaseModel

open HistoryContraction TickChronology TickAuxiliary PackedChunkTransfer
open scoped Classical BigOperators
variable {F : Type*} [CommSemiring F] {S : Shape} {P : Plan F S} {E : P.Codes} {bits : P.History → ℕ}
  {a : ℕ} {c : Clock} {R : GroupRegister P E bits a} {lanes span : ℕ}

structure Buckets (P : Plan F S) (bits : P.History → ℕ) (c : Clock) (a lanes span : ℕ) where
  site : Fin lanes → S.Site
  group : ∀ h, (P.finish h).Site → Fin c.groups
  positive : 0<span
  fit : c.chunks*a ≤ lanes*span

namespace Buckets

variable (T : Buckets P bits c a lanes span)

def rows := ClippedPairBuckets.rows T.site (c.chunks*a) span

def home (h : P.History) (i : S.Site) : ℕ := (T.group h (P.destination h i)).val

def length (v : Plan.Terminal P bits) (g : ℕ) := BucketRows.count (T.home v.1) T.rows g

theorem length_outside (v : Plan.Terminal P bits) (g : ℕ) (out : c.groups ≤ g) : T.length v g=0 := by
  unfold length
  generalize T.rows = bs
  induction bs with
  | nil => rfl
  | cons b bs ih =>
    have bound := (T.group v.1 (P.destination v.1 b.site)).isLt
    have ne : T.home v.1 b.site≠g := by change (T.group v.1 _).val≠g; omega
    change (if T.home v.1 b.site=g then b.size else 0)+BucketRows.count _ bs g=0
    simp [ne,ih]

def code (v : Plan.Terminal P bits) (g : ℕ) :=
  RotatedBucketScan.code P v.1 (fun i => (T.group v.1 i).val) T.rows c g a

def packed (v : Plan.Terminal P bits) (g : Fin c.groups) : Live (T.code v g.val) ≃ Fin (T.length v g.val) :=
  PackedBucketBijection.chunkEquiv (T.home v.1) g.val T.rows
    (ClippedPairBuckets.disjoint T.site (c.chunks*a) span (T.home v.1)) c.chunks a
    (ClippedPairBuckets.bounded T.site (c.chunks*a) span)

theorem addr (v : Plan.Terminal P bits) (g : Fin c.groups) (z : Live (T.code v g.val)) :
    (T.packed v g z).val = T.code v g.val z.val.1 z.val.2-1 :=
  PackedBucketBijection.chunkEquiv_val _ _ _ _ _ _ _ _

def owner (v : Plan.Terminal P bits) (z : Fin c.chunks × Fin a) :=
  T.group v.1 (P.destination v.1 (T.site (ClippedPairBuckets.lane span T.positive T.fit z)))

theorem hit (v : Plan.Terminal P bits) (g : Fin c.groups) (z : Fin c.chunks × Fin a) :
    T.code v g.val z.1 z.2 ≠ 0 ↔ T.owner v z=g :=
  PackedGroupPartition.bucket_hit P v.1 (T.group v.1) T.rows c (T.owner v)
    (ClippedPairBuckets.covered T.site span T.positive T.fit)
    (fun z b hb lo hi => congrArg (fun i => T.group v.1 (P.destination v.1 i))
      (ClippedPairBuckets.owner T.site span T.positive T.fit z b hb lo hi)) g z

def data (room : ∀ v g,1+R.capacity+2*T.length v g≤a)
    (w : ∀ v g, Aux (T.length v g) → Aux (T.length v g) → ℕ → F) : Data R c :=
  ⟨T.length,room,T.code,w⟩

def read (v : Plan.Terminal P bits) (g : Fin c.groups) (x : Ext c a) : Aux (T.length v g.val) :=
  PackedChunkTransfer.project (T.code v g.val) (T.packed v g) x

/-- Extend a packed group to all physical chunks by assigning zero to the
bits whose terminal site belongs to another group. -/
def extend (v : Plan.Terminal P bits) (g : Fin c.groups) (xs : Aux (T.length v g.val)) : Ext c a :=
  fun k j=>if h : T.code v g.val k j≠0 then xs (T.packed v g ⟨(k,j),h⟩) else false

theorem read_extend (v : Plan.Terminal P bits) (g : Fin c.groups) (xs : Aux (T.length v g.val)) :
    T.read v g (T.extend v g xs)=xs := by
  funext i
  let z:=(T.packed v g).symm i
  change (if h : T.code v g.val z.val.1 z.val.2≠0 then xs (T.packed v g ⟨(z.val.1,z.val.2),h⟩) else false)=xs i
  rw [dite_eq_left z.property]
  exact congrArg xs ((T.packed v g).apply_symm_apply i)

theorem extend_read (v : Plan.Terminal P bits) (g : Fin c.groups) (x : Ext c a)
    (k : Fin c.chunks) (j : Fin a) (live : T.owner v (k,j)=g) :
    T.extend v g (T.read v g x) k j=x k j := by
  have active := (T.hit v g (k,j)).mpr live
  unfold extend
  rw [dite_eq_left active]
  simp only [read,PackedChunkTransfer.project,Equiv.symm_apply_apply]

/-- Reading any live packed ordinal retrieves the originating physical bit. -/
theorem read_code (v : Plan.Terminal P bits) (g : Fin c.groups) (x : Ext c a)
    (k : Fin c.chunks) (j : Fin a) (i : Fin (T.length v g.val))
    (found : T.code v g.val k j = 1+i.val) : T.read v g x i=x k j := by
  let z : Live (T.code v g.val) := ⟨(k,j),by rw [found]; omega⟩
  have index : T.packed v g z=i := Fin.ext (by rw [T.addr]; change T.code v g.val k j-1=i.val; omega)
  rw [← index]
  simp only [read,PackedChunkTransfer.project,Equiv.symm_apply_apply,z]

/-- At a chosen original leaf the packed group ordinal is the sum of the
earlier group bucket widths plus the offset within this leaf. -/
theorem read_bucket (v : Plan.Terminal P bits) (pre post : List (Bucket S.Site)) (b : Bucket S.Site)
    (rows_eq : T.rows=pre++b::post) (k : Fin c.chunks) (j : Fin a)
    (lo : b.lo≤k.val*a+j.val) (hi : k.val*a+j.val<b.hi) (x : Ext c a) :
    let g := T.group v.1 (P.destination v.1 b.site)
    ∃ i : Fin (T.length v g.val), i.val=BucketRows.count (T.home v.1) pre g.val+(k.val*a+j.val-b.lo) ∧
      T.read v g x i=x k j := by
  let g := T.group v.1 (P.destination v.1 b.site)
  have disj : PackedBucketBijection.Disjoint (T.home v.1) (pre++b::post) := by
    rw [← rows_eq]
    exact ClippedPairBuckets.disjoint ..
  have code : T.code v g.val k j =
      1+BucketRows.count (T.home v.1) pre g.val+(k.val*a+j.val-b.lo) := by
    change Diagonal.TickGroupIntervals.pairCode (T.home v.1 b.site) (k.val*a+j.val)
      (BucketIntervalCodes.intervals (T.home v.1) (fun _=>0) T.rows) = _
    rw [rows_eq]
    exact BucketIntervalCodes.code_middle _ _ _ _ _ (BucketIntervalCodes.compatible _ _ _ disj) lo hi
  have bound : T.code v g.val k j≤T.length v g.val := PackedBucketBijection.pairCode_le_count ..
  let offset := BucketRows.count (T.home v.1) pre g.val+(k.val*a+j.val-b.lo)
  have key : T.code v g.val k j=1+offset := by
    simpa only [offset,Nat.add_assoc] using code
  let i : Fin (T.length v g.val) := ⟨offset,by omega⟩
  exact ⟨i,rfl,T.read_code v g x k j i key⟩

theorem sum (room : ∀ v g,1+R.capacity+2*T.length v g≤a)
    (w : ∀ v g, Aux (T.length v g) → Aux (T.length v g) → ℕ → F)
    (labels : ∀ h, (Fin (bits h) → Bool) ≃ (P.finish h).Boundary) (factors : Ext c a → Ext c a → S.Factors F)
    (values : ∀ v (g : Fin c.groups) x y, ((TickRangeChronology.evalTicks c g.val).map
      (w v g.val (T.read v g x) (T.read v g y))).prod =
        ∏ i : {i // T.group v.1 i=g}, P.cells v.1 (factors x y) i.val
          ((P.finish v.1).graph.atVertex (labels v.1 v.2) i.val)) (x y : Ext c a) :
    (((List.range (c.last+1)).map (step (T.data room w))).prod) (x,fun _=>false) (y,fun _=>false) =
      (1 : Matrix (Ext c a) (Ext c a) F) x y + S.contract (factors x y) :=
  contract (T.data room w) labels T.owner T.hit T.packed T.addr factors T.group values x y


end Buckets
end ThreeFlat.Diagonal.TickPhaseModel

end
end OAI
