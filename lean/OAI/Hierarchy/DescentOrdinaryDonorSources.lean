import OAI.Hierarchy.DescentOrdinaryDonorRankDirectory
import OAI.Hierarchy.DescentOrdinarySignedParents
import OAI.Hierarchy.DescentStaticTablePages

namespace OAI
/-! Reassemble the original eleven donor digits from issued endpoint
paths and local keys. The two shared-peer digits use the receiver's actual
two-walk chart. The final three digits are the original donor data pages. -/
namespace Hierarchy.DescentOrdinaryDonorSources
open DescentParallelBase DescentParallelBase.ParentFilter DescentHaloWalkRAM
open DescentPackedZip DescentSIMDLookup DescentOrdinaryDonorRankDirectory
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure ProtocolRAM
open scoped Classical Fin.CommRing
noncomputable section
variable {H D Q K L b M hosts groups w a : ℕ} (R:Fin H→Fin D→Option (Fin H))
local notation "P" => breadth D

/-- The preceding donor tape has endpoint low digits, upper bit, ticket, and mass. -/
def material (r:Option (Fused.Raw R Q K L b)) (i:Fin 6):Cell b:=
  r.elim 0 (fun d=>(![d.parent.src.low.val,d.parent.dst.low.val,d.receiver.2.val,d.parent.upper.toNat,
    d.parent.ticket.val,d.parent.weight.val] i:ℕ))

/-- These are scalar directory lookups, hence they carry no fields from the
post-normalization edge list. Existence is decided by the old donor source. -/
def key (r:Option (Fused.Raw R Q K L b)) (which:Fin 5):ℕ:=
  r.elim 0 (fun z=>
    let q:=if which.val=2 ∨ which.val=4 then z.parent.dst.path else z.parent.src.path
    (PairRanks.pair z.path q).val+1)

def tag (i:Fin 5):Field:=if i.val=0 then .reverse else if i.val<3 then .localEndpoint else .sharedEndpoint
def geometry (fits:P*P<2^b) (r:Option (Fused.Raw R Q K L b)) (i:Fin 5):Cell b:=
  r.elim 0 (fun z=>let q:=if i.val=2 ∨ i.val=4 then z.parent.dst.path else z.parent.src.path
    ⟨numberAt R (tag i) z.receiver.1 z.path q,(number_le R (tag i) ..).trans_lt fits⟩)

/-- The collector may read arbitrary bytes on malformed input. On genuine
rows the address is the actual receiver and the canonical path selects
exactly that issuing donor. -/
def Correct (v:Fin H) (r:Option (Fused.Raw R Q K L b)):Prop:=
  ∀z,r=some z→z.receiver.1=v ∧ Gather.select (Gather.reaching R) v z.path=some z.host

theorem looked_up (fits:P*P<2^b) (r:Option (Fused.Raw R Q K L b)) (v:Fin H) (i:Fin 5)
    (bound:Correct R v r) (x:Cell a) (read:x.val=key R r i):
    DescentPackedChildNeighbor.SIMD.lookup (directory R fits (tag i) v) x (List.finRange (P*P))=geometry R fits r i:=by
  cases r with
  | none=>
    apply DescentPackedChildNeighbor.SIMD.lookup_missing
    intro j
    change x.val=0 at read
    rw [read]
    omega
  | some z=>
    obtain ⟨rfl,_⟩:=bound z rfl
    let q:=if i.val=2 ∨ i.val=4 then z.parent.dst.path else z.parent.src.path
    rw [DescentPackedChildNeighbor.SIMD.lookup_at _ x (PairRanks.pair z.path q) read]
    simp [geometry,directory,PairRanks.pair,q]

def peerDigit (Q:ℕ) (r x:Cell b):Cell b:=(r.val*Q+x.val:ℕ)

@[simp] theorem peerDigit_zero (Q : ℕ) : peerDigit Q (0 : Cell b) 0 = 0 := by
  simp [peerDigit]

def assemble (table:Tables) (mat:Fin 6→Expr) (geom:Fin 5→Expr):Fin 11→Expr:=
  ![geom 0,mat 0,geom 1,mat 1,geom 2,mat 2,table.read (geom 3) (mat 0),table.read (geom 4) (mat 1),mat 3,mat 4,mat 5]

def digits (fits:P*P<2^b) (r:Option (Fused.Raw R Q K L b)):Fin 11→Cell b:=
  let t:=geometry R fits r;let m:=material R r
  ![t 0,m 0,t 1,m 1,t 2,m 2,peerDigit Q (t 3) (m 0),peerDigit Q (t 4) (m 1),m 3,m 4,m 5]

set_option maxHeartbeats 1800000 in
theorem decode (fits:P*P<2^b) (r:Option (Fused.Raw R Q K L b)) (v:Fin H) (ground:Correct R v r) (i:Fin 11):
    digits R fits r i=Fused.columns r i:=by
  cases r with
  | none=>fin_cases i <;> first | rfl | exact peerDigit_zero Q
  | some z=>
    obtain ⟨rfl,chosen⟩:=ground z rfl
    have ms (j:Fin 11):Machine.fields R z.receiver z.path z.host z.parent j<2^b:=z.small j
    have ls:z.parent.src.low.val<2^b:=ms 1
    have lt:z.parent.dst.low.val<2^b:=ms 3
    have lq:z.receiver.2.val<2^b:=ms 5
    have lu:z.parent.upper.toNat<2^b:=ms 8
    have lk:z.parent.ticket.val<2^b:=ms 9
    have lw:z.parent.weight.val<2^b:=ms 10
    have peers (e:Endpoint P Q):(peer R z.receiver.1 z.path e).val=(PairRanks.ticket (Gather.reaching R) z.receiver.1 z.path e.path).val*Q+e.low.val:=by simp [peer,finProdFinEquiv_apply_val,Nat.mul_comm,Nat.add_comm]
    have ps:=ms 6;have pt:=ms 7
    change (peer R z.receiver.1 z.path z.parent.src).val<2^b at ps
    change (peer R z.receiver.1 z.path z.parent.dst).val<2^b at pt
    rw [peers] at ps pt
    apply Fin.ext
    fin_cases i <;> simp [digits,material,geometry,tag,numberAt,chosen,Fused.columns,peerDigit,Machine.fields,
      peers,Fin.val_cast_of_lt ls,Fin.val_cast_of_lt lt,Fin.val_cast_of_lt lq,Fin.val_cast_of_lt lu,Fin.val_cast_of_lt lk,
      Fin.val_cast_of_lt lw]
    all_goals rw [←Nat.cast_mul,←Nat.cast_add]
    · exact Fin.val_cast_of_lt ps
    · exact Fin.val_cast_of_lt pt

theorem source (T:Tables) (es:Fin 6→Expr) (gs:Fin 5→Expr) (fits:P*P<2^b) (m:Memory w) (upper:ℕ)
    (raw:Fin hosts→Fin groups→Option (Fused.Raw R Q K L b))
    (correct:∀h g z,raw h g=some z→Gather.select (Gather.reaching R) z.receiver.1 z.path=some z.host)
    (physical:∀i,DescentPackedZip.Source (es i) (fun h g=>material R (raw h g) i) M m)
    (rank:∀i,DescentPackedZip.Source (gs i) (fun h g=>geometry R fits (raw h g) i) M m)
    (room:∀(i:Fin 5)(j:Fin 6),DescentPackedZip.Fits T (gs i) (es j) b b M upper w)
    (installed:Static T (peerDigit Q (b:=b)) M m) (i:Fin 11):
    DescentPackedZip.Source (assemble T es gs i) (fun h g=>Fused.columns (raw h g) i) M m:=by
  have val (h:Fin hosts) (g:Fin groups):Fused.columns (raw h g) i=digits R fits (raw h g) i:=by
    cases live:raw h g with
    | none=>fin_cases i <;> first | rfl | exact peerDigit_zero Q | exact (peerDigit_zero Q).symm
    | some d=>
      apply (decode R fits (some d) d.receiver.1 ?_ i).symm
      intro e he
      obtain rfl:=Option.some.inj he
      exact ⟨rfl,correct h g d live⟩
  simp_rw [val]
  have join (u:Fin 5) (v:Fin 6):=read_data T (gs u) (es v) upper (room u v) (peerDigit Q (b:=b)) (peerDigit_zero Q) m installed _ _ (rank u) (physical v)
  fin_cases i <;> first | exact rank _ | exact physical _ | exact join _ _

theorem work (T:Tables) (es:Fin 6→Expr) (gs:Fin 5→Expr) (lim:ℕ)
    (a:∀i,(es i).work≤lim) (b:∀i,(gs i).work≤lim) (i:Fin 11):(assemble T es gs i).work≤2*lim+11:=by
  have sum (u:Fin 5) (v:Fin 6):(T.read (gs u) (es v)).work≤2*lim+11:=by
    rw [DescentPackedZip.work];have x:=a v;have y:=b u;omega
  fin_cases i <;> first | exact sum _ _ | exact (a _).trans (by omega) | exact (b _).trans (by omega)

section Received
open DescentSharedCableNames DescentParallelBase
variable {U E X T V:Type} [Fintype E] [DecidableEq U] [Fintype X] [Fintype T]
    {n O:ℕ} {B:Ends U n} (C:Blocks B E)
    (Z:Measured C R X T V Q O K L) (shelf:Measured.Shelf C R Z)
    (small:∀h path x (d:ParentFilter.Source (breadth D) Q K L) i,Machine.fields R (Z.venue h) path (Z.loc x).1 d i<2^b)

omit [Fintype E] in
theorem corrected (h:U) (j:Fin (P*O)):
    Correct (b:=b) R (Z.venue h).1 (Fused.fetched C R Z shelf small h j):=by
  intro z physical
  let xy:Fin P×Fin O:=finProdFinEquiv.symm j
  change (Gather.select (Gather.reaching R) (Z.venue h).1 xy.1).bind
    (fun u=>Resident.oldAt Z.loc (Fused.previous C R Z shelf small h xy.1) u xy.2)=some z at physical
  cases found:Gather.select (Gather.reaching R) (Z.venue h).1 xy.1 with
  | none=>simp [found] at physical
  | some donor=>
    simp only [found,Option.bind_some,Resident.oldAt] at physical
    split at physical
    next hit=>
      cases r:shelf.issued h hit.choose with
      | none=>simp [Fused.previous,r] at physical
      | some d=>
        simp only [Fused.previous,r,Option.map_some,Option.some.injEq] at physical
        subst z
        exact ⟨rfl,by simpa only [congrArg Prod.fst hit.choose_spec] using found⟩
    next miss=>simp at physical

omit [Fintype E] in
theorem corrected_bind {α:Type*} (chosen:Option α) (get:α→U) (slot:α→Fin (P*O))
    (d:Fused.Raw R Q K L b) (hit:chosen.bind (fun z=>Fused.fetched C R Z shelf small (get z) (slot z))=some d):
    Gather.select (Gather.reaching R) d.receiver.1 d.path=some d.host:=by
  cases chosen with
  | none=>simp at hit
  | some z=>
    obtain ⟨place,proper⟩:=corrected R C Z shelf small (get z) (slot z) d hit
    rw [place];exact proper

end Received

namespace ROM
open DescentOrdinaryAtomFieldRAM.ROM
def pages (Q b M:ℕ):=binary (peerDigit Q (b:=b)) M
def width (b M:ℕ):=(b+b)*M
def table (base Q b M:ℕ):=joined (pages Q b M) (width b M) base id
def endAddress (base b M:ℕ):=base+2*2^(width b M)

theorem setup (base Q b M:ℕ) (m:Memory w) (room:endAddress base b M<2^w):
    let f:=pages Q b M;let bits:=width b M;let mid:=after f bits base m
    (mount f bits w base).Exec m mid (4+10*(2*2^bits)) ∧
    Static (table base Q b M) (peerDigit Q (b:=b)) M mid ∧
    (∀a,a<base ∨ endAddress base b M≤a→mid a=m a) ∧ CheapCode (mount f bits w base):=by
  intro f bits mid
  refine ⟨(run f bits base m room).1,binary_mounted _ M f bits base m ?_ id (fun _=>rfl),frame f bits base m,@cheap _ f bits w base⟩
  intro j
  fin_cases j <;> change _*M≤_*M <;> apply Nat.mul_le_mul_right <;> simp []
end ROM

end
end Hierarchy.DescentOrdinaryDonorSources

end OAI
