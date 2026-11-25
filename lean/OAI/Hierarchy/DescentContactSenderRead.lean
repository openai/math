import OAI.Hierarchy.DescentContactSenderDate

namespace OAI
/-! # The sender date reads every original and returned field on its final shared memory -/
namespace Hierarchy.DescentContactSenderDate.Layout
open DescentSIMDLookup DescentPackedZip DescentPackedColony DescentPackedFallbackTree.Image
open DescentPacking.PackedMatch.Local.Gather DescentResetReciprocalPeer DescentResetOppositePayload
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open DescentOrdinaryAtomFieldRAM
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false
variable {D L cap n r Ht b w : ℕ} (A : Layout D L cap n r Ht b) (U : Prior D L cap n r)
local notation "N" => DescentOldContactSender.count D L cap n r
local notation "F" => DescentOldContactSender.lanes L cap
local notation "P" => b*F
local notation "K" => 2*cap
local notation "jobs" => (L*K)*2
local notation "span" => DescentResetOppositePayload.span D cap
local notation "emit" => localLaw (D:=D) (L:=L) (cap:=cap) (b:=b) (n:=n) (r:=r) (Ht:=Ht)
local notation "peel" => splitLaw (L:=L) (cap:=cap) (b:=b)
local notation "H" => A.hosts
local notation "J" => A.groups
local notation "M" => A.batch
local notation "grid" => Fin H→Fin J
variable (xs : Fin A.hosts→Fin A.groups→Fin (DescentOldContactSender.count D L cap n r)→Cell b)

def sentValue (s : Bool) (j : Fin L×Fin K) (f : Fin 3) (h : Fin H) (g : Fin J) : Cell b :=
  DescentOldContactSender.point Ht s (DescentOldContactSender.decode (xs h g)) j f

def arrivedValue (next : Adj H D) (raw : Fin L→Fin K→Fin H→Fin J→Cell b)
    (s : Bool) (t : Fin L×Fin K) (f : Fin 2) (h : Fin H) (g : Fin J) : Cell b :=
  both D cap b (!s) (digits next (raw t.1 t.2) (raw t.1)
    (fun z=>A.sentValue xs (!s) (t.1,z) (Fin.castLE (by decide) f)) h g)

structure Packed (w : ℕ) : Prop where
  positive : 0<M
  board : M*max (b*N) P≤w/2
  split : M*max (P*2) b≤w/2
  remote : M*max (b*span) b≤w/2
  index : F≤2^P

private theorem carry {a : ℕ} {m dst : Memory w} {e : Expr} {ceiling : ℕ}
    {values : Fin H→Fin J→Cell a} (low : e.Fits w ceiling)
    (frame : ∀p,p<ceiling→dst p=m p) (prior : Source e values M m) : Source e values M dst :=
  fun t=>(eval_below e _ m dst low frame).trans (prior t)

private theorem readSource {a : ℕ} {m : Memory w} {x : Fin H→Fin J→Cell a} {bk : Bank} {past : ℕ}
    (r : Source (.lookup bk .row) x M m) (capacity : A.localShape.rows≤bk.size) (fits : bk.Fits w past) :
    Reads bk x M m := fun t=>(bank_read bk m ((row H J M t).isLt.trans_le capacity) fits).symm.trans (r t)

theorem split_frame (m : Memory w) (prior : A.PriorFits U w) (room : A.endAddress<2^w) :
    (∀x,x<A.splitShape.first→A.splitImage U m x=A.indexImage U m x) ∧
    ∀x,x<A.first→A.splitImage U m x=m x := by
  obtain ⟨a,c,d,e,f⟩:=A.bounds
  have sb:=A.splitShape.any peel A.splitReads (A.indexImage U m) (fun j _=>A.split_fits j room) (e.trans_lt (f.trans_lt room))
  have loc:=A.localShape.any emit (fun _=>U.board) m (fun _ _=>prior.board) (c.trans_lt (d.trans_lt (e.trans_lt (f.trans_lt room))))
  exact ⟨fun x p=>sb.2.2 x (.inl p),fun x p=>(sb.2.2 x (.inl (p.trans_le (a.trans c)))).trans
    ((ROM.frame _ _ _ _ x (.inl (p.trans_le a))).trans (loc.2.2 x (.inl p)))⟩

private def splitData (j : ℕ) (h : Fin H) (g : Fin J) : Fin 2→Cell P :=
  ![emit (xs h g),(j:Cell P)]

theorem split_sources (m : Memory w) (prior : A.PriorFits U w) (space : A.Packed w) (room : A.endAddress<2^w)
    (input : ∀i,Source (U.board i) (fun h g=>xs h g i) M m)
    (s : Bool) (t : Fin L×Fin K) (f : Fin 3) :
    Reads (A.senderBank s t f) (A.sentValue xs s t f) M (A.splitImage U m) := by
  obtain ⟨a,c,d,e,last⟩:=A.bounds
  have packed:=A.localShape.words emit (fun _=>U.board) m (fun _ _=>prior.board)
    (c.trans_lt (d.trans_lt (e.trans_lt (last.trans_lt room)))) space.positive space.board (fun _=>xs)
    (fun _ _=>input) 0 Nat.zero_lt_one
  have oldFit : A.packedBank.Fits w A.localEnd:=A.localShape.output_fits 0 Nat.zero_lt_one
    (c.trans_lt (d.trans_lt (e.trans_lt (last.trans_lt room))))
  have saved:=carry (A:=A) (dst:=A.indexImage U m) (e:=.lookup A.packedBank .row) ⟨oldFit,trivial⟩
    (fun x h=>ROM.frame A.indexPage A.localShape.rowBits A.localEnd (A.localImage U m) x (.inl h)) packed
  have inputs (j : ℕ) (live : j<F) (k : Fin 2) :
      Source (A.splitReads j k) (fun h g=>A.splitData xs j h g k) M (A.indexImage U m) := by
    fin_cases k
    · exact saved
    · change Source (if _ : j<F then _ else _) _ _ _
      rw [dite_eq_left live]
      let key : Fin F:=⟨_,live⟩
      let table:=A.indexPage key
      have fits:=A.index_fits key room
      apply source_column _ _ fits _ _ A.localShape.rows_fit
      intro p
      change Row H J M at p
      have within:=(row H J M p).isLt
      let pos : Cell A.localShape.rowBits:=⟨_,within.trans_le A.localShape.rows_fit⟩
      have read:=ROM.read A.indexPage A.localShape.rowBits A.localEnd (A.localImage U m) key (le_refl _) pos
      apply read.trans
      congr 1
      dsimp only [indexPage]
      rw [dite_eq_left (show pos.val<A.localShape.rows from within)]
      change (data (fun (_ : Fin H) (_ : Fin J)=>(j:Cell P)) ((row H J M).symm ((row H J M) p))).val=_
      rw [Equiv.symm_apply_apply]
      rfl
  let key:=DescentOldContactSender.lane s (finProdFinEquiv t) f
  have result:=A.splitShape.words peel A.splitReads (A.indexImage U m) (fun j _=>A.split_fits j room)
    (e.trans_lt (last.trans_lt room)) space.positive space.split (A.splitData xs) inputs key.val key.isLt
  have selected (h : Fin H) (g : Fin J) : peel (A.splitData xs key.val h g)=A.sentValue xs s t f h g := by
    have ok : key.val<2^P:=key.isLt.trans_le space.index
    unfold splitLaw
    change (if hit : ((key.val:Cell P)).val<F then
      (encode b F).symm (emit (xs h g)) ⟨_, hit⟩ else 0) = _
    have keyval : ((key.val:Cell P)).val=key.val := Fin.val_cast_of_lt ok
    have valid : ((key.val:Cell P)).val<F := keyval.trans_lt key.isLt
    rw [dite_eq_left valid]
    have same : (⟨((key.val:Cell P)).val,valid⟩:Fin F)=key:=Fin.ext keyval
    rw [same]
    simp only [localLaw, DescentOldContactSender.bundle, key, DescentOldContactSender.lane,
      Equiv.symm_apply_apply, Equiv.apply_symm_apply, sentValue]
  have decoded : (fun h g=>peel (A.splitData xs key.val h g))=A.sentValue xs s t f := funext fun h=>funext (selected h)
  refine readSource (A:=A) (bk:=A.senderBank s t f) ?_ A.splitShape.rows_fit
    (A.splitShape.output_fits key.val key.isLt (e.trans_lt (last.trans_lt room)))
  rw [←decoded]
  exact result

structure Before (next : Adj H D) (raw : Fin L→Fin K→Fin H→Fin J→Cell b) (m : Memory w) : Prop where
  input : ∀j,Source (U.board j) (fun h g=>xs h g j) M m
  ports : Mounted U.routes next m J M
  signed : ∀lo z,Reads (U.signed lo z) (raw lo z) M m
  host : ∀p : Row H J M,U.host.eval m ((row H J M p).val:Word w)=(p.1.val:Word w)
  ones : Source U.ones (fun (_ : Fin H) (_ : Fin J)=>(1:Cell b)) M m

/-- The last two scans use the original mounted roster and signed store, whose addresses
are strictly below the sender date. Only sender payload reads point into the new projection. -/
theorem old_routes {next : Adj H D} {m dest : Memory w} {bk : Bank}
    (ok : Accessible U.routes bk H J M w A.first) (mounted : Mounted U.routes next m J M)
    (frame : ∀a,a<A.first→dest a=m a) : Mounted U.routes next dest J M := by
  have eqn {B : Bank} (safe : B.Fits w A.first) {j : ℕ} (small : j<B.size) :
      dest (B.base+j)=m (B.base+j):=frame _ ((Nat.add_lt_add_left small _).trans_le safe.2.2)
  refine ⟨fun p j=>(eqn (ok.ids j) ((row H J M p).isLt.trans_le (ok.idsRoom j))).trans (mounted.ids p j),
    fun v j=>(eqn ok.roster ?_).trans (mounted.roster v j),
    fun v=>(eqn ok.offsets (v.isLt.trans_le ok.offRoom)).trans (mounted.offsets v),
    fun p=>(eqn ok.chunks ((row H J M p).isLt.trans_le ok.chunkRoom)).trans (mounted.chunks p)⟩
  exact (Nat.add_lt_add_left j.isLt _).trans_le ((by rw [←Nat.succ_mul];exact Nat.mul_le_mul_right _ v.isLt : v.val*D+D≤H*D).trans ok.rosterRoom)

variable (next : Adj A.hosts D) (raw : Fin L→Fin (2*cap)→Fin A.hosts→Fin A.groups→Cell b)

private theorem return_source (s : Bool) (work : Memory w) (prior : A.PriorFits U w) (space : A.Packed w)
    (room : A.endAddress<2^w) (m : Memory w) (prev : A.Before U xs next raw m)
    (earlier : ∀a,a<A.first→work a=m a)
    (localReads : ∀t f,Reads (A.senderBank (!s) t f) (A.sentValue xs (!s) t f) M work)
    (t : Fin L×Fin K) (f : Fin 2) :
    Reads (A.returnBank s t f) (A.arrivedValue xs next raw s t f) M
      ((A.returnShape s).image (both D cap b (!s)) (A.returnReads U s) work) := by
  have ⟨a,c,d,e,last⟩:=A.bounds
  have after : A.leftShape.first≤(A.returnShape s).first:=by cases s <;>simp [returnShape,e]
  have endOK : (A.returnShape s).endAddress span b<2^w:=by
    cases s
    · exact last.trans_lt room
    · exact room
  let entry (j : ℕ) (h : Fin H) (g : Fin J) := if live : j<jobs then
    let task:=finProdFinEquiv.symm (⟨j,live⟩:Fin jobs)
    let t : Fin L×Fin K:=finProdFinEquiv.symm task.1
    digits next (raw t.1 t.2) (raw t.1) (fun z=>A.sentValue xs (!s) (t.1,z) (Fin.castLE (by decide) task.2)) h g
    else fun _=>0
  have inputs (j : ℕ) (ok : j<jobs) (i : Fin span) :
      Source (A.returnReads U s j i) (fun h g=>entry j h g i) M work := by
    let idx:=finProdFinEquiv.symm (⟨j,ok⟩:Fin jobs)
    let v : Fin L×Fin K:=finProdFinEquiv.symm idx.1
    let values:=fun z=>A.sentValue xs (!s) (v.1,z) (Fin.castLE (by decide) idx.2)
    let dest:=fun z=>A.senderBank (!s) (v.1,z) (Fin.castLE (by decide) idx.2)
    have lin:=prior.route v.1 v.2
    have old (z : Fin K) : Reads (U.signed v.1 z) (raw v.1 z) M work:=fun p=>
      (earlier _ ((Nat.add_lt_add_left ((row H J M p).isLt.trans_le (prior.route v.1 z).srcRoom) _).trans_le
        (prior.route v.1 z).source.2.2)).trans (prev.signed _ z p)
    have load (z : Fin K) : Accessible U.routes (dest z) H J M w A.leftShape.first:=by
      have fit:=A.splitShape.output_fits («N»:=2) (field:=P) (DescentOldContactSender.lane (!s) (finProdFinEquiv (v.1,z))
        (Fin.castLE (by decide) idx.2)).val (by exact Fin.isLt _) (e.trans_lt (last.trans_lt room))
      let incr:=a.trans (c.trans d)
      exact ⟨fun i=>⟨(lin.ids i).1,(lin.ids i).2.1,(lin.ids i).2.2.trans incr⟩,lin.idsRoom,
        ⟨lin.roster.1,lin.roster.2.1,lin.roster.2.2.trans incr⟩,lin.rosterRoom,
        ⟨lin.offsets.1,lin.offsets.2.1,lin.offsets.2.2.trans incr⟩,lin.offRoom,
        ⟨lin.chunks.1,lin.chunks.2.1,lin.chunks.2.2.trans incr⟩,lin.chunkRoom,fit,A.splitShape.rows_fit⟩
    have oldFit (z : Fin K) : Accessible U.routes (U.signed v.1 z) H J M w A.leftShape.first:=by
      let fit:=(prior.route v.1 z).source
      exact {load z with source:=⟨fit.1,fit.2.1,fit.2.2.trans (a.trans (c.trans d))⟩,srcRoom:=(prior.route v.1 z).srcRoom}
    have query:=source_column _ _ lin.source work _ lin.srcRoom (old v.2)
    have pos (p : Row H J M) : U.host.eval work ((row H J M p).val:Word w)=(p.1.val:Word w):=
      (eval_below _ _ m work prior.host earlier).trans (prev.host p)
    have got:=operands U.routes (U.signed v.1 v.2) (U.signed v.1) dest A.leftShape.first work next
      (A.old_routes U lin prev.ports earlier) (oldFit v.2) (fun z=>⟨oldFit z,load z⟩)
      (.lookup (U.signed v.1 v.2) .row) U.host U.ones (raw v.1 v.2) (raw v.1) values
      (fun z=>⟨old z,localReads (v.1,z) _⟩) query pos (carry (A:=A) prior.ones earlier prev.ones) i
    simpa only [returnReads,entry,dite_eq_left ok] using got
  let job:=ticket t f
  have endvals : Source (.lookup (A.returnBank s t f) .row)
      (fun h g=>both D cap b (!s) (entry job.val h g)) M
      ((A.returnShape s).image (both D cap b (!s)) (A.returnReads U s) work) := by
    cases s <;> exact DescentResetCandidateDate.Shape.words _ _ _ work
      (fun j _ i=>A.return_fits U prior room _ j i) endOK space.positive space.remote entry inputs job.val job.isLt
  have cast (h : Fin H) (g : Fin J) : both D cap b (!s) (entry job.val h g)=A.arrivedValue xs next raw s t f h g := by
    dsimp only [entry]
    rw [dite_eq_left job.isLt]
    simp only [Fin.eta, job, ticket, Equiv.symm_apply_apply, arrivedValue]
  apply readSource (A:=A) (by simpa only [cast] using endvals)
  · cases s <;> exact A.localShape.rows_fit
  · exact (A.returnShape s).output_fits job.val (by cases s <;>exact job.isLt) endOK

theorem sources (m : Memory w) (prior : A.PriorFits U w) (space : A.Packed w) (room : A.endAddress<2^w)
    (stored : A.Before U xs next raw m) :
    (∀s t f,Reads (A.senderBank s t f) (A.sentValue xs s t f) M (A.image U m)) ∧
    ∀s t f,Reads (A.returnBank s t f) (A.arrivedValue xs next raw s t f) M (A.image U m) := by
  obtain ⟨a,c,d,e,last⟩:=A.bounds
  have left:=A.leftShape.any (both D cap b true) (A.returnReads U false) (A.splitImage U m)
    (fun j _ i=>A.return_fits U prior room false j i) (last.trans_lt room)
  have right:=A.rightShape.any (both D cap b false) (A.returnReads U true) (A.leftImage U m)
    (fun j _ i=>A.return_fits U prior room true j i) room
  have src:=A.split_sources U xs m prior space room stored.input
  have preserved (s : Bool) (t : Fin L×Fin K) (f : Fin 3) (p : Row H J M) :
      (A.senderBank s t f).base+(row H J M p).val<A.leftShape.first := by
    have fit:=A.splitShape.output_fits («N»:=2) (field:=P) (DescentOldContactSender.lane s (finProdFinEquiv t) f).val
      (by exact Fin.isLt _) (e.trans_lt (last.trans_lt room))
    exact (Nat.add_lt_add_left ((row H J M p).isLt.trans_le A.splitShape.rows_fit) _).trans_le fit.2.2
  have prev:=A.split_frame U m prior room
  have nextRead (s t f) : Reads (A.senderBank s t f) (A.sentValue xs s t f) M (A.leftImage U m):=fun p=>
    (left.2.2 _ (.inl (preserved s t f p))).trans (src s t f p)
  refine ⟨fun s t f p=>(right.2.2 _ (.inl ((preserved s t f p).trans_le e))).trans (nextRead s t f p),?_⟩
  intro s t f
  cases s
  · have got:=A.return_source U xs next raw false (A.splitImage U m) prior space room m stored prev.2 (src true) t f
    have fit:=A.leftShape.output_fits («N»:=span) (field:=b) (ticket t f).val (ticket t f).isLt (last.trans_lt room)
    intro p
    exact (right.2.2 _ (.inl ((Nat.add_lt_add_left ((row H J M p).isLt.trans_le A.leftShape.rows_fit) _).trans_le fit.2.2))).trans (got p)
  · exact A.return_source U xs next raw true (A.leftImage U m) prior space room m stored
      (fun x h=>(left.2.2 x (.inl (h.trans_le (a.trans (c.trans d))))).trans (prev.2 x h)) (nextRead false) t f

end
end Hierarchy.DescentContactSenderDate.Layout

end OAI
