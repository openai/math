import OAI.Hierarchy.DescentPackedMatchProfileRAM

namespace OAI
/-! # Prefixing packed survivor counts and issuing the globally dense profile tape -/

namespace Hierarchy.DescentPacking.PackedMatch.ProfileTable
open DescentSIMDLookup DescentPackedProfileWindow ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure DescriptorExpr
open scoped Classical BigOperators Fin.CommRing
noncomputable section
variable {w n M R : ℕ}

structure Layout where
  countROM : Bank
  topology : Bank
  raw : Bank
  counts : ℕ
  cursor : Bank
  out : ℕ
  tables : Tables

def issue (w R n : ℕ) (l : Layout) :=
  ((scan w l.counts n (sumLookup l.countROM l.topology)).seq
    (PackedProfileCursor.program w R l.counts l.cursor.base n)).seq
    (scan w l.out n (programExpr l.tables l.topology l.raw (pointer l.cursor) (rem_ l.cursor)))

def clock (n : ℕ) := (4+28*n)+PackedProfileCursor.ticks n+(4+152*n)

def boot (l : Layout) (n : ℕ) (m : Memory w) := image l.counts n (sumLookup l.countROM l.topology) m

def middle (l : Layout) (R n : ℕ) (m : Memory w) := PackedProfileCursor.after R l.counts l.cursor.base n (boot l n m)

def issued (l : Layout) (R n : ℕ) (m : Memory w) :=
  image l.out n (programExpr l.tables l.topology l.raw (pointer l.cursor) (rem_ l.cursor)) (middle l R n m)

structure Room (s : Shape) (M R n w : ℕ) (l : Layout) : Prop where
  scan : Fits s M R n w l.out l.tables l.topology l.raw (pointer l.cursor) (rem_ l.cursor)
  counter : l.countROM.Fits w l.counts
  countBits : l.countROM.bits=s.outputBits*M
  topology : l.topology.Fits w l.counts
  raw : l.raw.Fits w l.counts
  fixedT : l.tables.topology.Fits w l.counts
  fixedO : l.tables.offset.Fits w l.counts
  fixedL : l.tables.low.Fits w l.counts
  fixedR : l.tables.result.Fits w l.counts
  low : l.counts+n≤l.cursor.base
  size : 2*(n+1)≤l.cursor.size
  cursor : l.cursor.Fits w l.out

def quota (s : Shape) (keys : Fin n→Cell (s.outputBits*M)) (i : ℕ) :=
  if h : i<n then chunkCount s M (keys ⟨i,h⟩) else 0

private theorem fits_before {b : Bank} {w cut n : ℕ} (h : b.Fits w cut) (x : Fin (2^n)) (width : b.bits=n) :
    b.base+x.val<cut := by
  have small : x.val<b.size := by simpa only [Bank.size,width] using x.isLt
  exact (Nat.add_lt_add_left small b.base).trans_le h.2.2

theorem run (s : Shape) (l : Layout) (r : Room s M R n w l) (m : Memory w)
    (keys : Fin n→Cell (s.outputBits*M)) (stream : ℕ→Cell s.digit)
    (pos : 0<R) (size : M*s.pairs≤R) (room : 2*R≤2^w) (digits : R≤2^(s.digit*R))
    (source : ∀i,m (l.topology.base+i.val)=((keys i).val:Word w))
    (counts : ∀k : Cell (s.outputBits*M),m (l.countROM.base+k.val)=(chunkCount s M k:Word w))
    (menu : static s M R l.tables m) (raw : ∀i<l.raw.size,m (l.raw.base+i)=((word s.digit R stream i).val:Word w))
    (windowRoom : ∀ i : Fin n,PackedProfileCursor.total (quota s keys) i.val/R+1<l.raw.size) :
    (issue w R n l).Exec m (issued l R n m) (clock n) ∧
      (∀i : Fin n,∀g : Fin M,∀j : Fin s.pairs,
        digit s.digit (finProdFinEquiv (g,j)).val (issued l R n m (l.out+i.val)).val=
        if j.val<(laneCounts s M (keys i) g).val then
          (stream (PackedProfileCursor.total (quota s keys) i.val+localPrefix (laneCounts s M (keys i)) g+j.val)).val
        else 0) ∧
      ∀a<l.counts,issued l R n m a=m a := by
  let a:=quota s keys
  let pre:=boot l n m
  let mid:=middle l R n m
  have old:=r.low
  have capacity:=r.size
  have front:=r.cursor.2.2
  have end_:=r.scan.space
  have wide : PackedProfileCursor.addr l.cursor.base n+2<2^w := by unfold PackedProfileCursor.addr;omega
  obtain ⟨first,live,low⟩ := sum_scan s l.countROM l.topology l.counts keys m r.counter r.topology
    r.scan.groups r.countBits (by omega) counts source
  have tally : ∀i<n,pre (l.counts+i)=(a i:Word w) := by
    intro i hi
    simpa only [pre,boot,a,quota,dite_eq_left hi] using live ⟨i,hi⟩
  have small : ∀i<n,a i≤R := by
    intro i hi
    simpa only [a,quota,dite_eq_left hi] using (chunkCount_bound s M (keys ⟨i,hi⟩)).trans size
  have carry : (PackedProfileCursor.program w R l.counts l.cursor.base n).Exec pre mid (PackedProfileCursor.ticks n) :=
    PackedProfileCursor.run R l.counts l.cursor.base n pre r.low wide
  have cursor := PackedProfileCursor.read R l.counts l.cursor.base n pre a pos room r.low tally small
  have frame {x : ℕ} (h : x<l.counts) : mid x=m x :=
    (PackedProfileCursor.below R l.counts l.cursor.base n pre x (by omega)).trans (low x h)
  have staticMid : static s M R l.tables mid :=
    ⟨fun k=>(frame (fits_before r.fixedT k r.scan.keyT)).trans (menu.1 k),
     fun k=>(frame (fits_before r.fixedO k r.scan.keyO)).trans (menu.2.1 k),
     fun k=>(frame (fits_before r.fixedL k r.scan.keyL)).trans (menu.2.2.1 k),
     fun k=>(frame (fits_before r.fixedR k r.scan.keyR)).trans (menu.2.2.2 k)⟩
  let e:=programExpr l.tables l.topology l.raw (pointer l.cursor) (rem_ l.cursor)
  have emit : (scan w l.out n e).Exec mid (issued l R n m) (4+n*(2*e.work+4)) :=
    (exec s l.tables l.topology l.raw (pointer l.cursor) (rem_ l.cursor) r.scan mid).1
  have eps : (issue w R n l).Exec m (issued l R n m) ((4+28*n)+PackedProfileCursor.ticks n+(4+n*(2*e.work+4))) :=
    Procedure.Exec.then (Procedure.Exec.then first carry) emit
  have step (i : Fin n) : l.cursor.read mid (((i.val:Word w)+(i.val:Word w)))=mid (PackedProfileCursor.addr l.cursor.base i.val) ∧
      l.cursor.read mid (((i.val:Word w)+(i.val:Word w))+1)=mid (PackedProfileCursor.addr l.cursor.base i.val+1) := by
    have hi:=i.isLt
    have second : i.val+i.val+1<l.cursor.size := by omega
    constructor
    · simpa only [PackedProfileCursor.addr, Nat.two_mul, Nat.cast_add] using
        DescentPackedZip.bank_read l.cursor mid (Nat.lt_of_succ_lt second) r.cursor
    · simpa only [PackedProfileCursor.addr, Nat.two_mul, Nat.cast_add, Nat.cast_one, add_assoc] using
        DescentPackedZip.bank_read l.cursor mid second r.cursor
  have billed : (4+28*n)+PackedProfileCursor.ticks n+(4+n*(2*e.work+4))=clock n := by
    simp only [e, clock, work, show 2*74+4=(152:ℕ) by decide, Nat.mul_comm n 152]
  rw [billed] at eps
  refine ⟨@eps,?_,
    fun x hx=>(ProtocolRAMGeneratedWrite.frame_image l.out n e mid x (.inl (by omega))).trans (frame hx)⟩
  intro i g j
  let start:=PackedProfileCursor.total a i.val
  let q:=start/R
  let off : Fin R:=⟨start%R,Nat.mod_lt _ pos⟩
  have prior := cursor i.val i.isLt.le
  have get := step i
  have rowNum := (get.1.trans prior.1 : (pointer l.cursor).eval mid (i.val:Word w)=(q:Word w))
  have offset := (get.2.trans prior.2 : (rem_ l.cursor).eval mid (i.val:Word w)=(off.val:Word w))
  have rd {t : ℕ} (h : t<l.raw.size) : mid (l.raw.base+t)=((word s.digit R stream t).val:Word w) :=
    (frame ((Nat.add_lt_add_left h _).trans_le r.raw.2.2)).trans (raw _ h)
  have kth := (frame ((Nat.add_lt_add_left (i.isLt.trans_le r.scan.groups) _).trans_le r.topology.2.2)).trans (source i)
  have last := read s l.tables l.topology l.raw (pointer l.cursor) (rem_ l.cursor) r.scan mid staticMid i (keys i)
    off q (word s.digit R stream q) (word s.digit R stream (q+1)) digits kth rowNum offset (windowRoom i)
    (rd (Nat.lt_of_succ_lt (windowRoom i))) (rd (windowRoom i))
  have wordAt := (ProtocolRAMGeneratedWrite.read_image l.out n (programExpr l.tables l.topology l.raw (pointer l.cursor) (rem_ l.cursor)) mid i).trans last
  let vals:=localProfile s.digit s.pairs M R (laneCounts s M (keys i)) off (word s.digit R stream q) (word s.digit R stream (q+1))
  change issued l R n m (l.out+i.val)=(vals.val:Word w) at wordAt
  have cellBits : s.digit*(M*s.pairs)≤bits (s.outputBits*M) (s.digit*R) := by
    have k:=Nat.mul_le_mul_left s.digit size
    dsimp [bits];omega
  have keyRoom : 2^(bits (s.outputBits*M) (s.digit*R))<2^w := by simpa only [Bank.size,r.scan.keyR] using r.scan.result.2.1
  rw [wordAt,Fin.val_cast_of_lt (vals.isLt.trans ((Nat.pow_le_pow_right (by decide : 0<2) cellBits).trans_lt keyRoom))]
  exact window s.digit s.pairs M R (laneCounts s M (keys i)) stream start pos size g j

end
end Hierarchy.DescentPacking.PackedMatch.ProfileTable

end OAI
