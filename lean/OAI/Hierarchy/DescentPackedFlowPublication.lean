import OAI.Hierarchy.DescentPackedFlowBatch
import OAI.Hierarchy.ProtocolRAMUniformWork

namespace OAI
/-! # Execute the complete native directed-count and reciprocal-pair publication -/
namespace Hierarchy.DescentPackedFlowPublication
open DescentSIMDLookup DescentPackedColony DescentPackedFlowBatch ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
variable {D H J r c M d b w : ℕ}

structure Layout (D r c : ℕ) where
  tokens : DescentPackedFlowRAM.Slot r c→Bank
  inserts : Fin D→Fin r→DescentPackedZip.Tables
  peers : Ports D
  header : DescentPackedFlowReturn.Index
  add : DescentPackedZip.Tables
  first : ℕ
  bits : ℕ

def Layout.pitch (A : Layout D r c) := 2^A.bits
def Layout.middle (A : Layout D r c) := A.first+D*A.pitch
def Layout.issued (A : Layout D r c) (i : Fin D) : Bank := ⟨A.first+i.val*A.pitch,A.bits⟩
def Layout.front (A : Layout D r c) (j : ℕ) : Expr :=
  if yes:j<D then DescentPackedFlowRAM.sumRow A.tokens (A.inserts ⟨j,yes⟩) else .lit 0
def Layout.both (A : Layout D r c) (H j : ℕ) : Expr :=
  if yes:j<D then DescentPackedFlowPair.expr A.header A.peers A.issued A.add H ⟨j,yes⟩ else .lit 0

def procedure (A : Layout D r c) (H J M w : ℕ) :=
  (program w (passes A.first (H*chunks J M) A.pitch A.front 0 D)).seq
    (program w (passes A.middle (H*chunks J M) A.pitch (A.both H) 0 D))

def duration (A : Layout D r c) (H J M : ℕ) :=
  clock (passes A.first (H*chunks J M) A.pitch A.front 0 D)+
    clock (passes A.middle (H*chunks J M) A.pitch (A.both H) 0 D)

structure Room (A : Layout D r c) (H J M d b w : ℕ) : Prop where
  pitch : H*chunks J M≤A.pitch
  small : A.middle+D*A.pitch<2^w
  tokens : ∀q,(A.tokens q).Fits w A.first ∧ H*chunks J M≤(A.tokens q).size
  addOne : ∀j x,WordRoom (A.inserts j x) (b*r) d M w A.first
  front : ∀j<D,(A.front j).inputEnd≤A.first
  back : ∀j<D,(A.both H j).inputEnd≤A.middle
  access : ∀j,Accessible A.peers (A.issued j) H J M w A.middle
  zip : WordRoom A.add (b*r) (b*r) M w A.middle
  idsBelow : ∀i,(A.peers.ids i).base+H*chunks J M≤A.first
  nearBelow : A.peers.roster.base+H*D≤A.first
  offsetsBelow : A.peers.offsets.base+H≤A.first
  chunksBelow : A.peers.chunks.base+H*chunks J M≤A.first
  startBelow : A.header.starts.base+H≤A.first
  hostsBelow : A.header.hosts.base+H*chunks J M≤A.first
  shiftBelow : A.add.shift.base+2^((b*r)*M)≤A.first
  tableBelow : A.add.apply.base+2^((b*r+b*r)*M)≤A.first

theorem run_framed (A : Layout D r c) (S : Room A H J M d b w) (unit : ℕ)
    (next : Fin H→Fin D→Option (Fin H)) (tags : Fin H→Fin J→DescentPackedFlowRAM.Slot r c→Cell d)
    (m : Memory w) (loaded : ∀q,Reads (A.tokens q) (fun v g=>tags v g q) M m)
    (rom : ∀(j : Fin D) (x : Fin r),DescentPackedZip.Static (A.inserts j x)
      (DescentPackedFlowRAM.insert (b:=b) (d:=d) unit j.val x) M m)
    (roster : Mounted A.peers next m J M) (idx : DescentPackedFlowReturn.Header A.header A.middle m D H J M)
    (table : DescentPackedZip.Static A.add (DescentPackedFlowPair.add (b:=b) (r:=r)) M m) :
    let value (v : Fin H) (g : Fin J) (j : Fin D) (x : Fin r):=unit*DescentPackedFlowRAM.counts (tags v g) j.val x
    ∃dst : Memory w,(procedure A H J M w).Exec m dst (duration A H J M) ∧
      (∀(j : Fin D) (p : Row H J M),dst (A.middle+j.val*A.pitch+(row H J M p).val)=
        ((data (fun v g=>encode b r (fun x=>(DescentPackedFlowPair.paid next value v g j x:Cell b))) p).val:Word w)) ∧
      (∀a<A.first,dst a=m a) ∧ ∀a,A.middle+D*A.pitch≤a→dst a=m a := by
  intro value
  let n:=H*chunks J M
  let qs:=passes A.first n A.pitch A.front 0 D
  let mid:=result qs m
  have stop : A.middle<2^w:=(Nat.le_add_right _ _).trans_lt S.small
  have start : A.first≤A.middle:=Nat.le_add_right _ _
  have frontSpace : ∀j<D,(A.front j).Fits w A.first:=fun j h=>(A.front j).fits_of_inputEnd (S.front j h) (start.trans_lt stop)
  obtain ⟨pass,word,low⟩:=execute A.first n A.pitch D A.front m frontSpace stop S.pitch
  have cols (j : Fin D) : Reads (A.issued j) (fun v g=>encode b r (fun x=>(value v g j x:Cell b))) M mid := by
    intro p
    have got:=word j (row H J M p)
    have single:=DescentPackedFlowRAM.native A.tokens (A.inserts j) A.first unit j.val m tags
      (by by_cases empty:D=0;exact Fin.elim0 (Fin.cast empty j)
          have present : A.pitch≤D*A.pitch:=by simpa using Nat.mul_le_mul_right A.pitch (show 1≤D by omega)
          exact (Nat.add_le_add_left (S.pitch.trans present) _).trans_lt stop)
      S.tokens (S.addOne j) (rom j) loaded
    have own:=single.2.1 p
    rw [ProtocolRAMGeneratedWrite.read_image] at own
    change result (passes A.first n A.pitch A.front 0 D) m
      (A.first+j.val*A.pitch+(row H J M p).val)=_
    exact got.trans (by simpa only [Layout.front,dite_eq_left j.isLt] using own)
  have newR : Mounted A.peers next mid J M := by
    refine ⟨fun p i=>(low _ ((Nat.add_lt_add_left (row H J M p).isLt _).trans_le (S.idsBelow i))).trans (roster.ids p i),
      fun v i=>(low _ ((Nat.add_lt_add_left (by
        have h:=Nat.mul_le_mul_right D v.isLt;rw [Nat.succ_mul] at h;have s:=i.isLt;omega : v.val*D+i.val<H*D) _).trans_le S.nearBelow)).trans (roster.roster v i),
      fun v=>(low _ ((Nat.add_lt_add_left v.isLt _).trans_le S.offsetsBelow)).trans (roster.offsets v),
      fun p=>(low _ ((Nat.add_lt_add_left (row H J M p).isLt _).trans_le S.chunksBelow)).trans (roster.chunks p)⟩
  have newI : DescentPackedFlowReturn.Header A.header A.middle mid D H J M :=
    {idx with read:=fun v=>(low _ ((Nat.add_lt_add_left v.isLt _).trans_le S.startBelow)).trans (idx.read v)
              self:=fun p=>(low _ ((Nat.add_lt_add_left (row H J M p).isLt _).trans_le S.hostsBelow)).trans (idx.self p)}
  have newT : DescentPackedZip.Static A.add (DescentPackedFlowPair.add (b:=b) (r:=r)) M mid :=
    ⟨fun z=>(low _ ((Nat.add_lt_add_left z.isLt _).trans_le S.shiftBelow)).trans (table.1 z),
     fun z=>(low _ ((Nat.add_lt_add_left z.isLt _).trans_le S.tableBelow)).trans (table.2 z)⟩
  let tail:=passes A.middle n A.pitch (A.both H) 0 D
  have backSpace : ∀j<D,(A.both H j).Fits w A.middle:=fun j h=>(A.both H j).fits_of_inputEnd (S.back j h) stop
  obtain ⟨last,all,frame⟩:=execute A.middle n A.pitch D (A.both H) mid backSpace S.small S.pitch
  have upper (a : ℕ) (ha : A.middle+D*A.pitch≤a) : result tail mid a=m a := by
    have first : A.first+D*A.pitch≤a := (show A.middle≤a by omega)
    exact (above A.middle n A.pitch (A.both H) mid 0 D a S.pitch (by simpa only [Nat.zero_add] using ha)).trans
      (above A.first n A.pitch A.front m 0 D a S.pitch (by simpa only [Nat.zero_add] using first))
  refine ⟨result tail mid,Procedure.Exec.then pass last,?_,fun a h=>(frame a (h.trans_le start)).trans (low a h),upper⟩
  intro j p
  have min : A.pitch≤D*A.pitch:=by simpa using Nat.mul_le_mul_right A.pitch (show 1≤D from Nat.zero_lt_of_lt j.isLt)
  have one:=DescentPackedFlowPair.native A.header A.peers A.issued A.add next value A.middle j mid newI
    S.access newR cols S.zip newT ((Nat.add_le_add_left (S.pitch.trans min) _).trans_lt S.small)
  have trueWord:=one.2.1 p
  rw [ProtocolRAMGeneratedWrite.read_image] at trueWord
  exact (all j (row H J M p)).trans (by simpa only [Layout.both,dite_eq_left j.isLt] using trueWord)

theorem run (A : Layout D r c) (S : Room A H J M d b w) (unit : ℕ)
    (next : Fin H→Fin D→Option (Fin H)) (tags : Fin H→Fin J→DescentPackedFlowRAM.Slot r c→Cell d)
    (m : Memory w) (loaded : ∀q,Reads (A.tokens q) (fun v g=>tags v g q) M m)
    (rom : ∀(j : Fin D) (x : Fin r),DescentPackedZip.Static (A.inserts j x)
      (DescentPackedFlowRAM.insert (b:=b) (d:=d) unit j.val x) M m)
    (roster : Mounted A.peers next m J M) (idx : DescentPackedFlowReturn.Header A.header A.middle m D H J M)
    (table : DescentPackedZip.Static A.add (DescentPackedFlowPair.add (b:=b) (r:=r)) M m) :
    let value (v : Fin H) (g : Fin J) (j : Fin D) (x : Fin r):=unit*DescentPackedFlowRAM.counts (tags v g) j.val x
    ∃dst : Memory w,(procedure A H J M w).Exec m dst (duration A H J M) ∧
      (∀(j : Fin D) (p : Row H J M),dst (A.middle+j.val*A.pitch+(row H J M p).val)=
        ((data (fun v g=>encode b r (fun x=>(DescentPackedFlowPair.paid next value v g j x:Cell b))) p).val:Word w)) ∧
      ∀a<A.first,dst a=m a := by
  obtain ⟨dst,run,reads,low,_⟩:=run_framed A S unit next tags m loaded rom roster idx table
  exact ⟨dst,run,reads,low⟩

theorem tariff (A : Layout D r c) (H J M : ℕ) :
    duration A H J M≤8+D*(4+H*chunks J M*(2*(1+18*(r*c))+4))+D*(4+H*chunks J M*(2*(7+121*D)+4)) := by
  have one:=DescentPackedFlowBatch.tariff A.first (H*chunks J M) A.pitch D A.front (1+18*(r*c)) (by
    intro j hj;simp [Layout.front,hj,DescentPackedFlowRAM.work])
  have two:=DescentPackedFlowBatch.tariff A.middle (H*chunks J M) A.pitch D (A.both H) (7+121*D) (by
    intro j hj;simpa [Layout.both,hj] using DescentPackedFlowPair.cost A.header A.peers A.issued A.add H ⟨j,hj⟩)
  unfold duration;omega

end
end Hierarchy.DescentPackedFlowPublication

end OAI
