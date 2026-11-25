import OAI.Hierarchy.DescentContactCastInputs
import OAI.Hierarchy.DescentContactMaskPeriod

namespace OAI
/-! # All five inputs of the sparse contact formatter on the attained post-trunk memory -/
namespace Hierarchy.DescentContactOutputShape.Shape
open DescentContactDonorFront DescentContactMaskShape DescentContactProbePitch DescentSIMDLookup DescentPackedZip DescentPackedColony
open DescentResetSignedHaloMatrix DescentPackedChildNeighbor.SIMD
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
set_option maxHeartbeats 420000
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

def rawIndicators (q : Fin A.sockets) : RawIndicators A q where
  own t:=lift (S:=A.shapes) (marks (A.socketWing q).1 t 0)
  marker t:=let j:=(C).index q (finProdFinEquiv (finTwoEquiv.symm (A.socketWing q).1,t))
            fun h g=>(C).marker board (finProdFinEquiv.symm j).1 ((C).values ys marks j h g)
  shape:=shapeField («H» := H) (S:=A.shapes) (G:=J) b
  halo s t:=let c:=finProdFinEquiv.symm t
            lift (S:=A.shapes) (fun h g=>DescentPackedChildNeighbor.SIMD.lookup (short («b» := (D).cargoBits) next id h)
              (if s then Right.askedField (D).degree (D).cap b (D).queryBits (raw c.1 c.2 h g) 0
               else askedField (D).degree (D).cap b (D).queryBits (raw c.1 c.2 h g) 0) (List.finRange ((D).degree+1)))
  mass:=lift (S:=A.shapes) (realAmount D donorStart xs q)

variable (initial postTrunk : Memory w) (acquired : (A.donor.sender donorStart).Before u xs next raw initial)
    (jobs : (A.donor.sender donorStart).Packed w) (viewWidth : A.donor.batch*max (A.donor.fieldBits*(A.donor.markers donorStart A.shapes A.markerBits).oldFields) (A.donor.markers donorStart A.shapes A.markerBits).viewBits≤w/2)
    (afterMarkers : (A.donor.markers donorStart A.shapes A.markerBits).endAddress≤first) (space : A.marker first+A.donor.hosts*chunks A.donor.groups A.donor.batch<2^w)
    (keys : DescentResetLocalRoster.rootSlots A.donor.residual (2^A.donor.n)*(2^A.donor.n+2^A.donor.height)<2^A.donor.fieldBits)
    (countWidth : A.donor.batch*max (A.donor.fieldBits*(A.donor.lows*(2*A.donor.cap)+1)) A.donor.fieldBits≤w/2) (haloWidth : A.donor.degree+2<2^A.donor.cargoBits)
local notation "before" => (D).memory donorStart u initial
local notation "original" => (D).result donorStart A.shapes A.markerBits u board front markerEnd pack initial
local notation "out" => DescentContactMaskShape.result D donorStart first u postTrunk
variable (kept : ∀addr,addr<(A.donor.markers donorStart A.shapes A.markerBits).endAddress→postTrunk addr=(A.donor.result donorStart A.shapes A.markerBits u board front markerEnd pack initial) addr)

/- One completed producer is used at each step. The preservation premise only concerns
the interval that precedes the intervening trunk code. The later count and two directed
halo reads are taken from their genuine final publication. -/
include acquired jobs viewWidth afterMarkers space keys countWidth haloWidth kept in
theorem sparse_sensors (q : Fin A.sockets) :
    RawRead A donorStart first u q (A.rawIndicators donorStart board xs next raw q) out := by
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
  have marker:=(D).period_sources donorStart A.shapes A.markerBits u board front xs next raw markerEnd pack initial acquired jobs viewWidth
  have oldBoard (i : Fin (C).oldFields) : Source ((D).oldBoard u i) (fun h g=>ys h g i) M before:=fun p=>
    (eval_below _ _ initial before (front.sender.board _) (fun a h=>((D).any donorStart u front initial).2.2 a (.inl h))).trans (acquired.input _ p)
  have markerRoom : (C).markerBase<2^w:=qtop.trans_lt markerEnd
  have shapeFit:=(C).shapeView_fits markerRoom
  have geometry:=(C).front ((D).oldBoard u) before ys (markerSpace).oldRow oldBoard markerRoom jobs.positive viewWidth
  have markerRun:=(C).marker_any board ((C).fields ((D).priorSensor donorStart))
    ((C).fields_fit ((D).oldBoard u) ((D).priorSensor donorStart) markerSpace) markerEnd pack ((C).frontImage ((D).oldBoard u) before)
  refine RawRead.mk ?_ ?_ ?_ ?_ ?_
  · intro j
    let term:=(D).priorSensor donorStart (A.socketWing q).1 j 0
    have safe:=(D).priorSensor_fits donorStart u front (A.socketWing q).1 j 0
    let ownValues := marks (A.socketWing q).1 j 0
    have src : Source term ownValues M out := by
      intro p
      exact (eval_below term _ before out safe lastOld).trans (sensed (A.socketWing q).1 j 0 p)
    exact view term ownValues (ProtocolRAMGeneratedWrite.fits_mono term (earlier.trans high) safe) src
  · intro j
    let k:=(C).index q (finProdFinEquiv (finTwoEquiv.symm (A.socketWing q).1,j))
    have safe : (Expr.lookup ((C).output k.val) .row).Fits w (C).endAddress:=⟨(C).output_fits k markerEnd,trivial⟩
    exact ⟨ProtocolRAMGeneratedWrite.fits_mono _ (afterMarkers.trans high) safe,fun p=>
      (eval_below _ _ original out safe firstEq).trans (marker k p)⟩
  · exact ⟨ProtocolRAMGeneratedWrite.fits_mono _ ext shapeFit,fun p=>
      (eval_below _ _ ((C).frontImage ((D).oldBoard u) before) out shapeFit
        (fun a h=>(firstEq a (h.trans_le qtop)).trans (markerRun.2.2 a (.inl h)))).trans (geometry.2.2.2.2.2 p)⟩
  · intro s t
    let pos:=finProdFinEquiv.symm t
    let chip:=Expr.lookup (u.signed pos.1 pos.2) .row
    have fit:=front.sender.route pos.1 pos.2
    have cf : chip.Fits w donorStart:=⟨fit.source,trivial⟩
    have val : Source chip (raw pos.1 pos.2) M initial:=source_column _ _ fit.source _ _ fit.srcRoom (acquired.signed pos.1 pos.2)
    cases s
    · have available:=(D).oldHalo donorStart u front initial next acquired.ports haloWidth chip (raw pos.1 pos.2) cf val
      let term := (shelf).port chip
      let values := fun (h : Fin H) (g : Fin J) => DescentPackedChildNeighbor.SIMD.lookup
        (short («b» := (D).cargoBits) next id h)
        (askedField (D).degree (D).cap b (D).queryBits (raw pos.1 pos.2 h g) 0) (List.finRange ((D).degree+1))
      have seen : Source term values M out := fun p =>
        (eval_below term _ before out available.1 lastOld).trans (available.2 p)
      exact view term values (ProtocolRAMGeneratedWrite.fits_mono term (earlier.trans high) available.1) seen
    · have issued : Source chip (raw pos.1 pos.2) M postTrunk:=fun p=>
        (eval_below _ _ initial postTrunk cf (fun a h=>(retained a (h.trans_le seed)).trans
          (((D).any donorStart u front initial).2.2 a (.inl h)))).trans (val p)
      have available:=right_source D donorStart first u earlier front postTrunk initial next acquired.ports haloWidth space retained
        chip (raw pos.1 pos.2) (ProtocolRAMGeneratedWrite.fits_mono chip (seed.trans earlier) cf) issued
      let values := fun (h : Fin H) (g : Fin J) => DescentPackedChildNeighbor.SIMD.lookup
        (short («b» := (D).cargoBits) next id h)
        (Right.askedField (D).degree (D).cap b (D).queryBits (raw pos.1 pos.2 h g) 0) (List.finRange ((D).degree+1))
      exact view (rightPort D donorStart first u chip) values available.1 available.2
  · let bank:=DescentContactMaskShape.bank D donorStart first q
    let cal:=DescentContactSenderMass.Date.calendar (A.donor.sender donorStart) first
    have legal := cal.output_fits («N» := N+1) (field:=b) q.val q.isLt (nextStart.trans_lt total)
    have recv:=published D donorStart first u ((old₂.trans old₃).trans earlier) front (nextStart.trans_lt total)
      xs next raw initial postTrunk jobs acquired (fun a h=>retained a (h.trans_le (old₂.trans old₃))) countWidth keys q
    have last:=(Right.any shelf W₀ total (memory D donorStart first postTrunk)).2.2
    have stored : Reads bank (realAmount D donorStart xs q) M out:=fun p=>
      (last _ (.inl ((Nat.add_lt_add_left ((row H J M p).isLt.trans_le cal.rows_fit) _).trans_le legal.2.2))).trans (recv p)
    have final : bank.Fits w endM:=⟨legal.1,legal.2.1,legal.2.2.trans nextStart⟩
    exact view (.lookup bank .row) (realAmount D donorStart xs q) ⟨final,trivial⟩
      (source_column bank endM final out (realAmount D donorStart xs q) cal.rows_fit stored)

end
end Hierarchy.DescentContactOutputShape.Shape

end OAI
