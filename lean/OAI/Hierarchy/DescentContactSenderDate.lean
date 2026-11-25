import OAI.Hierarchy.DescentOldSenderReturn
import OAI.Hierarchy.DescentPreparedRotorInputs
import OAI.Hierarchy.ProtocolRAMGeneratedWrite

namespace OAI
/-! # One old sender gather, a shared field projection, and both directed payload returns -/
namespace Hierarchy.DescentContactSenderDate
open DescentSIMDLookup DescentPackedZip DescentPackedColony DescentPackedFallbackTree.Image
open DescentPacking.PackedMatch.Local.Gather DescentResetReciprocalPeer DescentResetOppositePayload
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open DescentOrdinaryAtomFieldRAM
open scoped Classical Fin.CommRing
noncomputable section
variable {D L cap n r Ht b w : ℕ}
local notation "N" => DescentOldContactSender.count D L cap n r
local notation "F" => DescentOldContactSender.lanes L cap
local notation "P" => b*F
local notation "K" => 2*cap
local notation "jobs" => (L*K)*2
local notation "span" => DescentResetOppositePayload.span D cap
abbrev Calendar := DescentResetCandidateDate.Shape

structure Layout (D L cap n r Ht b : ℕ) where
  first : ℕ
  hosts : ℕ
  groups : ℕ
  batch : ℕ

structure Prior (D L cap n r : ℕ) where
  board : Fin (DescentOldContactSender.count D L cap n r)→Expr
  routes : Ports D
  signed : Fin L→Fin (2*cap)→Bank
  host : Expr
  ones : Expr

namespace Layout
variable (A : Layout D L cap n r Ht b) (U : Prior D L cap n r)

def localShape : Calendar := ⟨A.first,1,A.batch,A.hosts,A.groups⟩
def localLaw : (Fin N→Cell b)→Cell P := DescentOldContactSender.bundle n r Ht
def localEnd := A.localShape.endAddress N b
def indexSize := F*A.localShape.stride
def splitShape : Calendar := ⟨A.localEnd+A.indexSize,F,A.batch,A.hosts,A.groups⟩
def packedBank := A.localShape.output N b 0
def indexPage (j : Fin F) : ROM.Page := ⟨A.localShape.rowBits,fun x=>
  if yes : x.val<A.localShape.rows then
    (data (fun (_ : Fin A.hosts) (_ : Fin A.groups)=>(j.val:Cell P))
      ((row A.hosts A.groups A.batch).symm ⟨_,yes⟩)).val else 0⟩
def indexBank (j : Fin F) := ROM.bank A.indexPage A.localShape.rowBits A.localEnd j
def splitReads (j : ℕ) : Fin 2→Expr := ![.lookup A.packedBank .row,if hit : j<F then .lookup (A.indexBank ⟨j,hit⟩) .row else .lit 0]
def splitLaw (x : Fin 2→Cell P) : Cell b :=
  if ok : (x 1).val<F then (encode b F).symm (x 0) ⟨_,ok⟩ else 0
def senderBank (s : Bool) (t : Fin L×Fin K) (f : Fin 3) :=
  A.splitShape.output 2 P (DescentOldContactSender.lane s (finProdFinEquiv t) f).val

def leftShape : Calendar := ⟨A.splitShape.endAddress 2 P,jobs,A.batch,A.hosts,A.groups⟩
def rightShape : Calendar := ⟨A.leftShape.endAddress span b,jobs,A.batch,A.hosts,A.groups⟩
def returnShape (s : Bool) : Calendar := if s then A.rightShape else A.leftShape
def endAddress := A.rightShape.endAddress span b
def ticket (t : Fin L×Fin K) (f : Fin 2) : Fin jobs := finProdFinEquiv (finProdFinEquiv t,f)
def returnBank (s : Bool) (t : Fin L×Fin K) (f : Fin 2) := (A.returnShape s).output span b (ticket t f).val

def returnReads (s : Bool) (j : ℕ) : Fin span→Expr :=
  if live : j<jobs then
    let slot:=finProdFinEquiv.symm (⟨j,live⟩:Fin jobs)
    let t : Fin L×Fin K:=finProdFinEquiv.symm slot.1
    DescentResetOppositePayload.«fields» U.routes (U.signed t.1) (fun z=>A.senderBank (!s) (t.1,z) (Fin.castLE (by decide) slot.2))
      A.hosts (.lookup (U.signed t.1 t.2) .row) U.host U.ones
  else fun _=>.lit 0

def localCode := A.localShape.code (localLaw (D:=D) (L:=L) (cap:=cap) (b:=b) (n:=n) (r:=r) (Ht:=Ht)) (fun _=>U.board) w
def localImage (m : Memory w) := A.localShape.image (localLaw (D:=D) (L:=L) (cap:=cap) (b:=b) (n:=n) (r:=r) (Ht:=Ht)) (fun _=>U.board) m
def localTicks := A.localShape.ticks (localLaw (D:=D) (L:=L) (cap:=cap) (b:=b) (n:=n) (r:=r) (Ht:=Ht)) (fun _=>U.board)
def indexImage (m : Memory w) := ROM.after A.indexPage A.localShape.rowBits A.localEnd (A.localImage U m)
def splitImage (m : Memory w) := A.splitShape.image (splitLaw (L:=L) (cap:=cap) (b:=b)) A.splitReads (A.indexImage U m)
def leftImage (m : Memory w) := A.leftShape.image (both D cap b true) (A.returnReads U false) (A.splitImage U m)
def image (m : Memory w) := A.rightShape.image (both D cap b false) (A.returnReads U true) (A.leftImage U m)

def program (w : ℕ) :=
  ((((A.localCode U (w:=w)).seq (ROM.mount A.indexPage A.localShape.rowBits w A.localEnd)).seq
    (A.splitShape.code (splitLaw (L:=L) (cap:=cap) (b:=b)) A.splitReads w)).seq
    (A.leftShape.code (both D cap b true) (A.returnReads U false) w)).seq
    (A.rightShape.code (both D cap b false) (A.returnReads U true) w)
def ticks :=
  (((A.localTicks U+(4+10*A.indexSize))+
    A.splitShape.ticks (splitLaw (L:=L) (cap:=cap) (b:=b)) A.splitReads)+
    A.leftShape.ticks (both D cap b true) (A.returnReads U false))+
    A.rightShape.ticks (both D cap b false) (A.returnReads U true)

theorem bounds : A.first≤A.localEnd ∧ A.localEnd≤A.splitShape.first ∧
    A.splitShape.first≤A.leftShape.first ∧ A.leftShape.first≤A.rightShape.first ∧
    A.rightShape.first≤A.endAddress := by
  have bound (t : Calendar) (arity d : ℕ) : t.first≤t.endAddress arity d:=by
    obtain ⟨l,m,h⟩:=t.ordered arity d;exact l.trans ((Nat.le_add_right ..).trans (m.trans h))
  exact ⟨bound A.localShape N b,Nat.le_add_right ..,bound A.splitShape 2 P,
    bound A.leftShape span b,bound A.rightShape span b⟩

theorem index_fits (j : Fin F) (room : A.endAddress<2^w) :
    (A.indexBank j).Fits w A.splitShape.first := by
  have ⟨lo,s,g,h,last⟩:=A.bounds
  have roof:=g.trans (h.trans last)
  have final : (A.indexBank j).base+(A.indexBank j).size≤A.splitShape.first:=by
    change A.localEnd+j.val*A.localShape.stride+A.localShape.stride≤A.localEnd+F*A.localShape.stride
    rw [Nat.add_assoc,←Nat.succ_mul];exact Nat.add_le_add_left (Nat.mul_le_mul_right _ j.isLt) _
  refine ⟨Nat.two_pow_pos _,?_,final⟩
  exact (Nat.le_add_left ..).trans_lt (final.trans_lt (roof.trans_lt room))

private theorem up {X : Bank} {lo hi : ℕ} (r : X.Fits w lo) (h : lo≤hi) : X.Fits w hi := ⟨r.1,r.2.1,r.2.2.trans h⟩

theorem split_fits (j : ℕ) (room : A.endAddress<2^w) (k : Fin 2) :
    (A.splitReads j k).Fits w A.splitShape.first := by
  obtain ⟨lo,s,g,h,last⟩:=A.bounds
  fin_cases k
  · exact ⟨up (A.localShape.output_fits («N»:=N) (field:=b) 0 Nat.zero_lt_one (s.trans_lt (g.trans_lt (h.trans_lt (last.trans_lt room))))) s,trivial⟩
  · simp only [splitReads]
    split
    · exact ⟨A.index_fits _ room,trivial⟩
    · trivial

structure PriorFits (w : ℕ) : Prop where
  board : ∀j,(U.board j).Fits w A.first
  route : ∀lo z,Accessible U.routes (U.signed lo z) A.hosts A.groups A.batch w A.first
  host : U.host.Fits w A.first
  ones : U.ones.Fits w A.first

theorem return_fits (prior : A.PriorFits U w) (room : A.endAddress<2^w) (s : Bool) (j i) :
    (A.returnReads U s j i).Fits w (A.returnShape s).first := by
  obtain ⟨lo,mid,sp,l,r⟩:=A.bounds
  have next : A.leftShape.first≤(A.returnShape s).first:=by cases s <;>simp [returnShape,l]
  have start : A.first≤(A.returnShape s).first:=lo.trans (mid.trans (sp.trans next))
  unfold returnReads
  split
  next h=>
    let a:=finProdFinEquiv.symm (⟨j,h⟩:Fin jobs)
    let t : Fin L×Fin K:=finProdFinEquiv.symm a.1
    let dest:=fun z=>A.senderBank (!s) (t.1,z) (Fin.castLE (by decide) a.2)
    have leap {priorBank : Bank} (ok : Accessible U.routes priorBank A.hosts A.groups A.batch w A.first) :
        Accessible U.routes priorBank A.hosts A.groups A.batch w (A.returnShape s).first :=
      ⟨fun x=>up (ok.ids x) start,ok.idsRoom,up ok.roster start,ok.rosterRoom,up ok.offsets start,
        ok.offRoom,up ok.chunks start,ok.chunkRoom,up ok.source start,ok.srcRoom⟩
    have prev:=leap (prior.route t.1 t.2)
    have outlet (z : Fin K) : Accessible U.routes (dest z) A.hosts A.groups A.batch w (A.returnShape s).first:=by
      have cell:=A.splitShape.output_fits («N»:=2) (field:=P) (DescentOldContactSender.lane (!s)
        (finProdFinEquiv (t.1,z)) (Fin.castLE (by decide) a.2)).val (by exact Fin.isLt _) (l.trans_lt (r.trans_lt room))
      exact {prev with source:=up cell next,srcRoom:=A.splitShape.rows_fit}
    exact fits_fields U.routes (U.signed t.1 t.2) (U.signed t.1) dest _ prev
      (fun z=>⟨leap (prior.route _ z),outlet z⟩) (.lookup (U.signed t.1 t.2) .row) U.host U.ones ⟨prev.source,trivial⟩
      (ProtocolRAMGeneratedWrite.fits_mono U.host start prior.host) (ProtocolRAMGeneratedWrite.fits_mono U.ones start prior.ones) i
  · trivial

theorem any (m : Memory w) (prior : A.PriorFits U w) (room : A.endAddress<2^w) :
    (A.program U w).Exec m (A.image U m) (A.ticks U) ∧ CheapCode (A.program U w) ∧
      ∀a,a<A.first ∨ A.endAddress≤a→A.image U m a=m a := by
  obtain ⟨a,c,d,e,f⟩:=A.bounds
  have H1:=e.trans_lt (f.trans_lt room)
  have H2:=d.trans_lt H1
  have H3:=c.trans_lt H2
  obtain ⟨r0,k0,z0⟩:=A.localShape.any (localLaw (D:=D) (L:=L) (cap:=cap) (b:=b) (n:=n) (r:=r) (Ht:=Ht)) (fun _=>U.board) m (fun _ _=>prior.board) H3
  have r1:=ROM.run A.indexPage A.localShape.rowBits A.localEnd (A.localImage U m) H2
  obtain ⟨r2,k2,z2⟩:=A.splitShape.any (splitLaw (L:=L) (cap:=cap) (b:=b)) A.splitReads (A.indexImage U m)
    (fun j _=>A.split_fits j room) H1
  obtain ⟨r3,k3,z3⟩:=A.leftShape.any (both D cap b true) (A.returnReads U false) (A.splitImage U m)
    (fun j _ i=>A.return_fits U prior room false j i) (f.trans_lt room)
  obtain ⟨r4,k4,z4⟩:=A.rightShape.any (both D cap b false) (A.returnReads U true) (A.leftImage U m)
    (fun j _ i=>A.return_fits U prior room true j i) room
  refine ⟨Procedure.Exec.then (Procedure.Exec.then (Procedure.Exec.then (Procedure.Exec.then r0 r1.1) r2) r3) r4,
    cheap_seq (cheap_seq (cheap_seq (cheap_seq k0 (ROM.cheap _ _ _ _)) k2) k3) k4,?_⟩
  intro x side
  rcases side with low|high
  · exact (z4 x (.inl (low.trans_le (a.trans (c.trans (d.trans e)))))).trans
      ((z3 x (.inl (low.trans_le (a.trans (c.trans d))))).trans ((z2 x (.inl (low.trans_le (a.trans c)))).trans
      ((ROM.frame _ _ _ _ x (.inl (low.trans_le a))).trans (z0 x (.inl low)))))
  · exact (z4 x (.inr high)).trans ((z3 x (.inr (f.trans high))).trans ((z2 x (.inr (e.trans (f.trans high)))).trans
      ((ROM.frame _ _ _ _ x (.inr (d.trans (e.trans (f.trans high))))).trans (z0 x (.inr (c.trans (d.trans (e.trans (f.trans high)))))))))

end Layout
end
end Hierarchy.DescentContactSenderDate

end OAI
