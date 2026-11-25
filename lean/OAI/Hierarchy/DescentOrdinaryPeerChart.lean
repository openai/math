import OAI.Hierarchy.DescentOrdinaryPeerLifts
import OAI.Hierarchy.DescentDyadicSpan

namespace OAI
/-! The coordinate-only successor tables and the true old reachability roster
are consumed in one chronological RAM. The integer table contains no old edges. -/
namespace Hierarchy.DescentOrdinaryPeerChart
open DescentSixParty.Chronology DescentDyadicSpan DescentOrdinaryPeerLifts
open Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
variable {H P S n w : ℕ}

def tables (base H n : ℕ) : Tables :=
  ⟨⟨base,Nat.clog 2 n⟩,⟨base+span n,Nat.clog 2 n⟩,⟨base+2*span n,Nat.clog 2 n⟩,
    ⟨base+3*span n,Nat.clog 2 H⟩⟩
def length (H n : ℕ) := 3*span n+span H
def out (base H n : ℕ) := base+length H n
def top (base H n : ℕ) := out base H n+span n

private def project {α : Type} (f : Fin n→α) (x : ℕ) (get : α→ℕ) : ℕ :=
  if hx : x<n then get (f ⟨x,hx⟩) else 0

def data (req : Request H P S n) (a : ℕ) : ℕ :=
  if a<span n then project req a (fun p=>p.elim H (fun x=>x.host.val))
  else if a<2*span n then project req (a-span n) (fun p=>p.elim 0 (fun x=>x.index.val))
  else if a<3*span n then project req (a-2*span n) (fun p=>p.elim 0 (fun x=>x.shape.val))
  else (a-3*span n)*S

def install (w base : ℕ) (req : Request H P S n) : NativePhase w :=
  let d:=data req
  let size:=length H n
  ⟨DescentStaticWordColumn.program w base d size,4+10*size,
    fun m=>DescentStaticWordColumn.image base d m size,DescentStaticWordColumn.cheap w base d size⟩

def program (w base Hnew : ℕ) (count old : Bank) (req : Request H P S n) : NativePhase w :=
  (install w base req).seq (phase w (out base H n) n H Hnew (tables base H n) count old)

private theorem room (base : ℕ) (count old : Bank) (cf : count.Fits w base) (ofit : old.Fits w base)
    (cap : H*P≤old.size) (host : H<2^w) (end_ : top base H n<2^w) :
    Room (tables base H n) count old H P n w (out base H n) := by
  let end₁:=out base H n
  have after : base≤end₁:=Nat.le_add_right ..
  have ready : end₁<2^w:=(Nat.le_add_right ..).trans_lt end_
  have mk (b bits : ℕ) (ok : b+2^bits≤end₁) : (Bank.mk b bits).Fits w end₁:=
    ⟨Nat.two_pow_pos _,(Nat.le_add_left ..).trans_lt (ok.trans_lt ready),ok⟩
  have A:=span_ge n
  have B:=span_ge H
  have intervals (s t : ℕ) : base+s≤base+(3*s+t) ∧ base+s+s≤base+(3*s+t) ∧
      base+2*s+s≤base+(3*s+t) ∧ base+3*s+t≤base+(3*s+t) :=
    ⟨by omega,by omega,by omega,by omega⟩
  obtain ⟨left,middle,right,last⟩:=intervals (span n) (span H)
  refine ⟨mk base (Nat.clog 2 n) left,
    mk (base+span n) (Nat.clog 2 n) middle,mk (base+2*span n) (Nat.clog 2 n) right,
    mk (base+3*span n) (Nat.clog 2 H) last,⟨cf.1,cf.2.1,cf.2.2.trans after⟩,
    ⟨ofit.1,ofit.2.1,ofit.2.2.trans after⟩,A,A,A,B,cap,host⟩

theorem any (base Hnew : ℕ) (count old : Bank) (req : Request H P S n) (m : Memory w)
    (cf : count.Fits w base) (ofit : old.Fits w base) (cap : H*P≤old.size)
    (host : H<2^w) (end_ : top base H n<2^w) :
    let p:=program w base Hnew count old req
    p.Runs m ∧ ∀a,a<base ∨ top base H n≤a→p.image m a=m a := by
  intro p
  let static_:=install w base req
  let write:=phase w (out base H n) n H Hnew (tables base H n) count old
  have safe : out base H n<2^w:=(Nat.le_add_right ..).trans_lt end_
  have ns : n≤ span n:=span_ge _
  have end₁:out base H n+n≤top base H n:=Nat.add_le_add_left ns _
  have wr:=DescentOrdinaryPeerLifts.any (tables base H n) count old Hnew (static_.image m)
    (room base count old cf ofit cap host end_) (end₁.trans_lt end_)
  have st : static_.Runs m:=DescentStaticWordColumn.mount base (length H n) (data req) m safe
  refine ⟨NativePhase.seq_runs static_ write m st wr.1,?_⟩
  intro a ha
  exact (wr.2 a (ha.imp (·.trans_le (Nat.le_add_right ..)) (end₁.trans ·))).trans
    (DescentStaticWordColumn.frame base (length H n) (data req) m a
      (ha.imp_right (fun h=>(Nat.le_add_right (out base H n) (span n)).trans h)))

private theorem installed (base N : ℕ) (count old : Bank) (req : Request H P S n)
    (peer : Fin H→Fin P→Option (Fin H)) (m : Memory w)
    (cf : count.Fits w base) (ofit : old.Fits w base) (cap : H*P≤old.size)
    (total : m count.base=(N:Word w))
    (actual : ∀(v:Fin H)(j:Fin P),m (old.base+(finProdFinEquiv (v,j)).val)=(((peer v j).elim H Fin.val : ℕ):Word w)) :
    Reads (tables base H n) count old N req peer ((install w base req).image m) := by
  let A:=span n
  have ns : n≤A:=span_ge _
  have read (x : ℕ) (small : x<length H n) :
      (install w base req).image m (base+x)=(data req x:Word w) :=
    DescentStaticWordColumn.read base (length H n) (data req) m small
  have below (a : ℕ) (inside : a<base) : (install w base req).image m a=m a :=
    DescentStaticWordColumn.frame _ _ _ _ a (.inl inside)
  refine ⟨(below _ ((Nat.lt_add_of_pos_right cf.1).trans_le cf.2.2)).trans total,?_,?_,?_,?_,?_⟩
  · intro i
    have hi:=i.isLt.trans_le ns
    exact (read i.val (by dsimp [length]; dsimp [A] at hi; omega)).trans (by simp [data,project,show i.val<span n from hi,i.isLt])
  · intro i
    have hi:=i.isLt.trans_le ns
    change (install w base req).image m (base+A+i.val)=_
    rw [Nat.add_assoc,read _ (by change A+i.val<3*A+span H;omega)]
    simp [data,project,show ¬(A+i.val<span n) by change ¬(A+i.val<A);omega,
      show A+i.val<2*span n by change A+i.val<2*A;omega,show A+i.val-span n=i.val by change A+i.val-A=_;omega,i.isLt]
  · intro i
    have hi:=i.isLt.trans_le ns
    change (install w base req).image m (base+2*A+i.val)=_
    rw [Nat.add_assoc,read _ (by change 2*A+i.val<3*A+span H;omega)]
    simp [data,project,show ¬(2*A+i.val<span n) by change ¬(2*A+i.val<A);omega,
      show ¬(2*A+i.val<2*span n) by change ¬(2*A+i.val<2*A);omega,
      show 2*A+i.val<3*span n by change 2*A+i.val<3*A;omega,
      show 2*A+i.val-2*span n=i.val by change 2*A+i.val-2*A=_;omega,i.isLt]
  · intro v
    have hv:=v.isLt.trans_le (span_ge H)
    change (install w base req).image m (base+3*A+v.val)=_
    rw [Nat.add_assoc,read _ (by change 3*A+v.val<3*A+span H;omega)]
    simp [data,show ¬(3*A+v.val<span n) by change ¬(3*A+v.val<A);omega,
      show ¬(3*A+v.val<2*span n) by change ¬(3*A+v.val<2*A);omega,
      show ¬(3*A+v.val<3*span n) by change ¬(3*A+v.val<3*A);omega,
      show 3*A+v.val-3*span n=v.val by change 3*A+v.val-3*A=_;omega]
  · intro v j
    have available:=(finProdFinEquiv (v,j)).isLt.trans_le cap
    exact (below _ ((Nat.add_lt_add_left available _).trans_le ofit.2.2)).trans (actual v j)

set_option maxHeartbeats 1000000 in
theorem read (base N Hnew : ℕ) (count old : Bank) (req : Request H P S n)
    (peer : Fin H→Fin P→Option (Fin H)) (m : Memory w) (bounded : N≤H)
    (cf : count.Fits w base) (ofit : old.Fits w base) (cap : H*P≤old.size)
    (host : H<2^w) (end_ : top base H n<2^w)
    (total : m count.base=(N:Word w))
    (actual : ∀(v:Fin H)(j:Fin P),m (old.base+(finProdFinEquiv (v,j)).val)=(((peer v j).elim H Fin.val : ℕ):Word w)) (i : Fin n) :
    (program w base Hnew count old req).image m (out base H n+i.val)=(result N Hnew S peer (req i):Word w) := by
  let mid := (install w base req).image m
  change (phase w (out base H n) n H Hnew (tables base H n) count old).image mid (out base H n+i.val)=_
  exact emit (out:=out base H n) (tables base H n) count old N Hnew req peer mid bounded
    (room (n:=n) base count old cf ofit cap host end_) (installed base N count old req peer m cf ofit cap total actual) i

theorem price (base Hnew : ℕ) (count old : Bank) (req : Request H P S n) :
    let p:=program w base Hnew count old req
    p.ticks ≤ 200*(n+1)+20*H+10 ∧
      DescentStaticWordColumn.names p.program ≤ 400+100*n+30*H := by
  intro p
  have hn:=span_le n
  have hh:=span_le H
  have work : (issue (tables base H n) count old H Hnew).work≤64 := by
    change 55 ≤ 64
    decide
  have dynamic := Nat.mul_le_mul_left n (show 2*(issue (tables base H n) count old H Hnew).work+4≤132 by omega)
  constructor
  · change (4+10*length H n)+(4+n*(2*_+4))≤_
    dsimp [length]
    omega
  · change DescentStaticWordColumn.names ((install w base req).program.seq (phase w (out base H n) n H Hnew _ count old).program)≤_
    rw [DescentStaticWordColumn.names_seq,show (install w base req).program=DescentStaticWordColumn.program w base (data req) (length H n) from rfl,
      DescentStaticWordColumn.names_mount,show (phase w (out base H n) n H Hnew (tables base H n) count old).program=
        scan w (out base H n) n (issue (tables base H n) count old H Hnew) from rfl,DescentStaticWordColumn.names_scan]
    dsimp [length]
    omega

theorem origin_word (base Hnew : ℕ) (count old : Bank) (req : Request H P S n) (m : Memory w) (i : Fin H) :
    (program w base Hnew count old req).image m ((tables base H n).origin.base+i.val)=((i.val*S:ℕ):Word w) := by
  let a:=3*span n+i.val
  have enough : a<length H n := Nat.add_lt_add_left (i.isLt.trans_le (span_ge H)) _
  have addr : (tables base H n).origin.base+i.val=base+a:=by dsimp [tables,a];omega
  rw [addr]
  change ProtocolRAM.image (out base H n) n _ ((install w base req).image m) (base+a)=_
  have before : base+a < out base H n := Nat.add_lt_add_left enough base
  rw [ProtocolRAMGeneratedWrite.frame_image (out base H n) n (issue (tables base H n) count old H Hnew)
    ((install w base req).image m) (base+a) (.inl before)]
  change DescentStaticWordColumn.image base (data req) m (length H n) (base+a)=_
  rw [DescentStaticWordColumn.read base (length H n) (data req) m enough]
  simp [data,show ¬a<span n by dsimp [a];omega,show ¬a<2*span n by dsimp [a];omega,
    show ¬a<3*span n by dsimp [a];omega,show a-3*span n=i.val by dsimp [a];omega]

theorem extent (base H n : ℕ) : top base H n ≤ base+8*n+2*H+5 := by
  have hn:=span_le n
  have hh:=span_le H
  dsimp [top,out,length]
  omega

end
end Hierarchy.DescentOrdinaryPeerChart

end OAI
