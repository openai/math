import OAI.Hierarchy.DescentResetOriginalDonorRead
import OAI.Hierarchy.DescentResetOriginalDonorSensors
import OAI.Hierarchy.DescentContactSparseSensors

namespace OAI
namespace Hierarchy.DescentContactOutputShape.Shape
open DescentContactDonorFront DescentContactMaskShape DescentContactProbePitch DescentSIMDLookup DescentPackedZip DescentPackedColony
open DescentResetSignedHaloMatrix DescentPackedChildNeighbor.SIMD
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
variable (A : Shape) (donorStart first : ℕ) {w k : ℕ}
set_option quotPrecheck false
local notation "D" => A.donor
local notation "H" => (D).hosts
local notation "J" => (D).groups
local notation "M" => (D).batch
local notation "N" => (D).lows*(2*(D).cap)
local notation "F" => DescentOldContactSender.count (D).degree (D).lows (D).cap (D).n (D).residual
local notation "b" => (D).fieldBits
local notation "C" => (D).markers donorStart A.shapes A.markerBits
local notation "S₀" => (D).sender donorStart
variable (u : DescentContactSenderDate.Prior A.donor.degree A.donor.lows A.donor.cap A.donor.n A.donor.residual)
variable (board : NonlinearExpanders.Graph A.donor.n k) (front : A.donor.Space donorStart u w)
variable (markerEnd : (A.donor.markers donorStart A.shapes A.markerBits).endAddress<2^w) (pack : A.donor.batch*max (A.donor.fieldBits*8) A.markerBits≤w/2)
local notation "markerSpace" => (D).markerSpace donorStart A.shapes A.markerBits u front markerEnd pack
variable (xs : Fin A.donor.hosts→Fin A.donor.groups→Fin (DescentOldContactSender.count A.donor.degree A.donor.lows A.donor.cap A.donor.n A.donor.residual)→Cell A.donor.fieldBits) (next : Fin A.donor.hosts→Fin A.donor.degree→Option (Fin A.donor.hosts))
    (raw : Fin A.donor.lows→Fin (2*A.donor.cap)→Fin A.donor.hosts→Fin A.donor.groups→Cell A.donor.fieldBits)
local notation "marks" => (D).sensorValue donorStart xs next raw
local notation "ys" => (D).boardValues xs
local notation "shelf" => (D).halo donorStart u.routes.roster
local notation "endM" => A.marker first
local notation "W₀" => DescentContactMaskShape.massEnd D first
local notation "size" => H*chunks J M

variable (initial postTrunk : Memory w) (acquired : (A.donor.sender donorStart).Before u xs next raw initial)
    (jobs : (A.donor.sender donorStart).Packed w) (viewWidth : A.donor.batch*max (A.donor.fieldBits*(A.donor.markers donorStart A.shapes A.markerBits).oldFields) (A.donor.markers donorStart A.shapes A.markerBits).viewBits≤w/2)
    (afterMarkers : (A.donor.markers donorStart A.shapes A.markerBits).endAddress≤first) (space : A.marker first+A.donor.hosts*chunks A.donor.groups A.donor.batch<2^w)
    (keys : DescentResetLocalRoster.rootSlots A.donor.residual (2^A.donor.n)*(2^A.donor.n+2^A.donor.height)<2^A.donor.fieldBits)
    (countWidth : A.donor.batch*max (A.donor.fieldBits*(A.donor.lows*(2*A.donor.cap)+1)) A.donor.fieldBits≤w/2) (haloWidth : A.donor.degree+2<2^A.donor.cargoBits)
local notation "before" => (D).memory donorStart u initial
local notation "original" => (D).result donorStart A.shapes A.markerBits u board front markerEnd pack initial
local notation "out" => DescentContactMaskShape.result D donorStart first u postTrunk
variable (kept : ∀addr,addr<(A.donor.markers donorStart A.shapes A.markerBits).endAddress→postTrunk addr=(A.donor.result donorStart A.shapes A.markerBits u board front markerEnd pack initial) addr)

include acquired jobs afterMarkers space kept in
/-- Original labels stay available independently of the socket selected in a later contact row. -/
theorem original_views (s : Bool) (j : Fin N) (f : Fin 5) :
    A.PresentAt endM out ((C).priorView ((D).priorSensor donorStart s j f))
      (lift (S:=A.shapes) (marks s j f)) :=by
  obtain ⟨old₁,old₂,old₃⟩:=(D).ordered donorStart
  obtain ⟨pre₁,pre₂,pre₃,pre₄,pre₅⟩:=(C).ordered
  have seed : donorStart≤(C).first:=old₁.trans (old₂.trans old₃)
  have ftop : (C).first≤(C).markerBase:=pre₁.trans (pre₂.trans pre₃)
  have qtop : (C).markerBase≤(C).endAddress:=pre₄.trans pre₅
  have earlier : (D).endAddress donorStart≤first:=ftop.trans (qtop.trans afterMarkers)
  have total : endM<2^w:=(Nat.le_add_right ..).trans_lt space
  have nextStart : W₀≤endM:=Nat.le_add_right ..
  have high : first≤endM:=(mass_bottom D first).trans nextStart
  have frame:=(period_any D donorStart first u earlier front total postTrunk).2.2
  have firstEq (a) (h : a<(C).endAddress) : out a=original a:=(frame a (.inl (h.trans_le afterMarkers))).trans (kept a h)
  have old (a) (h : a<(C).first) : original a=before a:=
    ((C).any board ((D).oldBoard u) ((D).priorSensor donorStart) markerSpace before).2.2 a (.inl h)
  have «until» : (C).first≤(C).endAddress:=ftop.trans qtop
  have retained (a) (h : a<(C).first) : postTrunk a=before a:=(kept a (h.trans_le «until»)).trans (old a h)
  have lastOld (a) (h : a<(C).first) : out a=before a:=(firstEq a (h.trans_le «until»)).trans (old a h)
  have ext : (C).markerBase≤endM:=qtop.trans (afterMarkers.trans high)
  have view {d} (term : Expr) (values : Fin H→Fin J→Cell d) (ok : term.Fits w endM) (src : Source term values M out) :
      A.PresentAt endM out ((C).priorView term) (lift (S:=A.shapes) values):=
    ⟨(C).late_view_fits endM ext (qtop.trans_lt markerEnd) term ok,
      (C).post_view board ((D).oldBoard u) ((D).priorSensor donorStart) markerSpace before out
        (fun a h=>firstEq a (h.trans_le qtop)) term values src⟩
  have sensed:=(D).sources donorStart u front xs next raw initial jobs acquired
  have safe:=(D).priorSensor_fits donorStart u front s j f
  exact view _ _ (ProtocolRAMGeneratedWrite.fits_mono _ (earlier.trans high) safe)
    (fun p=>(eval_below _ _ before out safe lastOld).trans (sensed s j f p))

include acquired jobs viewWidth afterMarkers space keys countWidth haloWidth kept in
theorem original_donor_reads (space' : A.projected first<2^w) :
    let q : Fin A.sockets:=⟨0,by unfold sockets DescentContactMaskShape.sockets;dsimp;positivity⟩
    let measured:=A.rawIndicators donorStart board xs next raw q
    let sensors:=A.originalSensors donorStart first u
    let dest:=A.held donorStart first u postTrunk
    (∀s j,A.PresentAt (A.choicePage first) dest (sensors.label s j) (lift (S:=A.shapes) (marks s j 0))) ∧
    (∀s j,A.PresentAt (A.choicePage first) dest (sensors.ticket s j)
      (lift (S:=A.shapes) (marks s j (if s then 1 else 0)))) ∧
    ∀j,A.PresentAt (A.choicePage first) dest (sensors.halo j) (measured.indicators.halo false j) :=by
  intro q measured sensors dest
  have top : A.choicePage first<A.projected first+1:=Nat.lt_succ_of_le (Nat.le_add_right ..)
  have room : A.choicePage first<2^w:=(Nat.le_add_right ..).trans_lt space'
  have casts:=A.casts first out room
  have raw_:=A.sparse_sensors donorStart first u board front markerEnd pack xs next raw initial postTrunk acquired
    jobs viewWidth afterMarkers space keys countWidth haloWidth kept q
  let mid:=A.halos first out
  obtain ⟨_,_,_,frame,_,_⟩:=DescentResetDonorBook.installed A.request b A.metaBits M (A.choicePage first) mid space'
  have move {a : ℕ} {e : Expr} {v : Fin A.sparseHosts→Fin J→Cell a} (h : A.PresentAt (A.choicePage first) mid e v) :
      A.PresentAt (A.choicePage first) dest e v :=
    ⟨h.1,fun t=>(eval_below _ _ mid dest h.1 (fun p lt=>frame p (.inl lt))).trans (h.2 t)⟩
  have get (s : Bool) (j : Fin N) (f : Fin 5) :=
    A.original_views donorStart first u board front markerEnd pack xs next raw initial postTrunk acquired jobs
      afterMarkers space kept s j f
  exact ⟨fun s j=>move (casts.raw _ _ (get s j 0)),fun s j=>move (casts.raw _ _ (get s j _)),
    fun j=>move (casts.halo _ _ (raw_.halo false j))⟩

def numberingLayout (sel short : ℕ) : DescentResetOriginalDonors.Layout :=
  ⟨A.sparseHosts,A.groups,A.blocks,(D).batch,N,b,A.metaBits,sel,short⟩

def numberingValues (sel short : ℕ) (shape : J=A.groups*A.blocks) : (A.numberingLayout sel short).Values where
  label side j h g:=lift (S:=A.shapes) (marks side j 0) h (g.cast shape.symm)
  ticket side j h g:=lift (S:=A.shapes) (marks side j (if side then 1 else 0)) h (g.cast shape.symm)
  halo j h g:=let q : Fin A.sockets:=⟨0,by unfold sockets DescentContactMaskShape.sockets;dsimp;positivity⟩
              (A.rawIndicators donorStart board xs next raw q).indicators.halo false j h (g.cast shape.symm)

private theorem reindex {n p h m bits w : ℕ} {term : Expr} {val : Fin h→Fin n→Cell bits} {mem : Memory w}
    (same : n=p) (ready : Source term val m mem) :
    Source term (fun v (i : Fin p)=>val v (i.cast same.symm)) m mem:=by
  subst p
  exact ready

set_option maxHeartbeats 440000 in
include acquired jobs viewWidth afterMarkers space keys countWidth haloWidth kept in
theorem numbered_reads (space' : A.projected first<2^w) (sel short : ℕ) (shape : J=A.groups*A.blocks)
    (at_ : Memory w) (preserved : ∀p,p<A.choicePage first→at_ p=A.held donorStart first u postTrunk p) :
    let L:=A.numberingLayout sel short
    L.Seen (A.originalSensors donorStart first u) (A.numberingValues donorStart board xs next raw sel short shape) at_ :=by
  let dest:=A.held donorStart first u postTrunk
  obtain ⟨l,t,h⟩:=A.original_donor_reads donorStart first u board front markerEnd pack xs next raw initial postTrunk
    acquired jobs viewWidth afterMarkers space keys countWidth haloWidth kept space'
  have lift_ {bits' : ℕ} (op : Expr) (y : Fin A.sparseHosts→Fin J→Cell bits')
      (pair : A.PresentAt (A.choicePage first) dest op y) :
      Source op (fun v (p : Fin (A.groups*A.blocks))=>y v (p.cast shape.symm)) M at_ :=
    reindex (term := op) (val := y) (m := M) (mem := at_) shape (fun p=>(eval_below op _ dest at_ pair.1 preserved).trans (pair.2 p))
  let q : Fin A.sockets := ⟨0, by unfold sockets DescentContactMaskShape.sockets; dsimp; positivity⟩
  constructor
  · intro s j
    exact lift_ ((A.originalSensors donorStart first u).label s j)
      (lift (S := A.shapes) (marks s j 0)) (l s j)
  · intro s j
    exact lift_ ((A.originalSensors donorStart first u).ticket s j)
      (lift (S := A.shapes) (marks s j (if s then 1 else 0))) (t s j)
  · intro j
    exact lift_ ((A.originalSensors donorStart first u).halo j)
      ((A.rawIndicators donorStart board xs next raw q).indicators.halo false j) (h j)

end
end Hierarchy.DescentContactOutputShape.Shape

end OAI
