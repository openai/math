import OAI.Hierarchy.DescentFundedCompactPlanes
import OAI.Hierarchy.DescentOrdinaryDatedEntry
import OAI.Hierarchy.DescentOrdinaryResultSteps
import OAI.Hierarchy.DescentDatePortPaidRoom
import OAI.Hierarchy.DescentDatedOrdinaryMaterial

namespace OAI
/-! # Physical room of the two issued successor rasters in an ordinary date -/
namespace Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary
open DescentSIMDLookup DescentPackedColony DescentPaidResidentCount DescentVenueQuantityPlanes
open DescentOrdinaryRasterReturn DescentDatedAddressBook ProtocolRAM
noncomputable section
set_option quotPrecheck false

private theorem ports_later {D H G M w a b : ℕ} {P : Ports D} {source : Bank}
    (old : Accessible P source H G M w a) (hi : a≤b) : Accessible P source H G M w b :=
  ⟨fun i=>allocated_bank_later (old.ids i) hi,old.idsRoom,allocated_bank_later old.roster hi,old.rosterRoom,
    allocated_bank_later old.offsets hi,old.offRoom,allocated_bank_later old.chunks hi,old.chunkRoom,allocated_bank_later old.source hi,old.srcRoom⟩

variable {F P : Type} [Field F] (v : PhysicalOrdinary F P) (floor : ℕ)
local notation "a" => v.area
local notation "d" => v.venue
local notation "begin_" => StageVenueTail.OrdinaryRaster.prepared a d v.rasterLanes (v.endAddress floor)
local notation "top" => StageVenueTail.OrdinaryRaster.sweep a d v.rasterLanes (v.endAddress floor)
local notation "dims" => StageVenueTail.OrdinaryRaster.dims a d v.rasterLanes
local notation "p" => StageVenueTail.OrdinaryRaster.shapes a
local notation "D₀" => StageVenueTail.OrdinaryRaster.donors a
local notation "n" => StageVenueTail.OrdinaryRaster.nameBits a
local notation "paid_" => Sweep.paidBank begin_ p D₀ (a).cap (d).paidBits n (a).H (a).G v.rasterLanes
local notation "alive_" => Sweep.aliveBank begin_ p D₀ (a).cap (d).paidBits n (a).H (a).G v.rasterLanes

theorem funded_compact_room {w : ℕ} (split : (d).groups*2^(a).k=(a).G)
    (lanes : 0<(d).paidLanes) (room : v.rasterEnd floor<2^w)
    (count : (v.paidRasterBanks floor).count.Fits w top) :
    DescentOrdinaryRasterReturn.Room dims (v.paidRasterBanks floor) top 0 w := by
  have topFit : top<2^w:=(DescentOrdinaryRasterReturn.after dims top).trans_lt room
  have paidLe: (paid_).base+(paid_).size≤top:=by
    change (paid_).base+Sweep.span p (a).H (a).G v.rasterLanes≤
      ((paid_).base+Sweep.span p (a).H (a).G v.rasterLanes+(p*2)*2^(Sweep.maskBits D₀ (a).cap n v.rasterLanes))+
        Sweep.span p (a).H (a).G v.rasterLanes
    omega
  have aliveLe: (alive_).base+(alive_).size≤top:=le_refl _
  have enough : p*(a).H*chunks ((d).groups*2^(a).k) v.rasterLanes≤Sweep.span p (a).H (a).G v.rasterLanes:=by
    rw [split,Nat.mul_assoc]
    exact Sweep.covered ..
  exact room_from_allocated_columns dims (v.paidRasterBanks floor) top w (allocated_bank_fits _ paidLe topFit)
    (allocated_bank_fits _ aliveLe topFit) count enough enough lanes (Nat.two_pow_pos _) room

private theorem accessible_cast {u z H G M w out : ℕ} (eqn : u=z) (ports : Ports u) (src : Bank)
    (available : Accessible ports src H G M w out) : Accessible (eqn ▸ ports) src H G M w out := by
  subst z
  exact available

theorem funded_room_from_entry (prior : DatePorts) (A : ArgumentEntry v)
    (match_ : A.Match v floor) (paths : A.clip.venue.paths=StageVenueTail.OrdinaryRaster.paths v.area)
    {w : ℕ} (inlet : A.Room v floor w) (previous : prior.PaidRoom w floor)
    (hosts : A.clip.venue.hosts=(a).H) (groups : A.clip.venue.groups=(a).G)
    (work : A.clip.working=v.rasterLanes) (split : (d).groups*2^(a).k=(a).G)
    (lanes : 0<(d).paidLanes) (room : v.rasterEnd floor<2^w) :
    v.FundedRoom floor (v.fundedFromEntry floor A paths) prior.io w := by
  have order_:=A.inlet_order v floor
  have mount_:=v.mount_order floor
  have routed_:=v.routed_order floor
  have tail_ : v.refsStart floor≤v.endAddress floor:=by
    rcases mount_ with ⟨u₀,u₁⟩
    rcases routed_ with ⟨u₂,u₃,u₄,u₅,u₆⟩
    omega
  have finished : A.finish v floor≤v.endAddress floor:=(match_.atRefs.le).trans tail_
  have clipLo : A.priorStart v floor≤v.endAddress floor:=
    order_.2.1.trans (order_.2.2.1.trans (order_.2.2.2.1.trans (order_.2.2.2.2.trans finished)))
  have signedLo : v.signedEnd floor≤v.endAddress floor:=order_.1.trans clipLo
  have topped : v.endAddress floor≤top:=by
    have early : begin_=v.endAddress floor+StageVenueTail.OrdinaryRaster.prepared a d v.rasterLanes 0:=
      DescentOrdinaryAtomFieldRAM.RoleCounts.Repitch.translate ..
    have lower : v.endAddress floor≤begin_:=by rw [early]; exact Nat.le_add_right ..
    apply lower.trans
    change begin_≤Sweep.roof begin_ p D₀ (a).cap (d).paidBits n (a).H (a).G v.rasterLanes
    rw [Sweep.roof_affine]
    exact Nat.le_add_right ..
  have topFit : top<2^w:=(DescentOrdinaryRasterReturn.after dims top).trans_lt room
  have fieldFit : (A.clip.fieldBank (v.signedEnd floor)).Fits w (v.endAddress floor):=
    allocated_bank_fits _ clipLo (topped.trans_lt topFit)
  have countBound : DescentOrdinaryPeerCount.roof (v.materialEnd floor) (a).H (a).D (d).hosts (d).degree≤v.peerTail floor:=by
    unfold peerTail DescentOrdinaryVenueReturn.roof DescentOrdinaryVenueReturn.hubs DescentOrdinaryVenueReturn.bookStart
    dsimp only
    omega
  have countTop:=countBound.trans ((v.signed_stage_paid floor).2.2.trans (signedLo.trans topped))
  have count := (DescentOrdinaryPeerCount.output_fit (v.materialEnd floor) (a).H (a).D (d).hosts (d).degree
    (countTop.trans_lt topFit)).2.2
  have oldPos : 0<A.previous.blocks:=by rw [match_.oldBlocks]; exact Nat.two_pow_pos _
  let x : Fin A.previous.blocks:=⟨0,oldPos⟩
  have popLo : (A.population v floor).outBase≤A.finish v floor:=Nat.le_add_right ..
  have visible:=ports_later (inlet.walk x) (popLo.trans finished)
  refine ⟨⟨A.labels v floor x,?_⟩,fieldFit,fun i _=>ProtocolRAMGeneratedWrite.fits_mono _ (v.spent floor).1 (previous.stock i),topFit,
    ⟨0,v.funded_compact_room floor split lanes room (allocated_bank_later count countTop)⟩⟩
  apply accessible_cast paths (A.ports v floor)
  change @Accessible A.clip.venue.paths (A.ports v floor) (A.labels v floor x)
    A.clip.venue.hosts A.clip.venue.groups A.clip.working w (v.endAddress floor) at visible
  simpa only [hosts,groups,work] using visible

/-- The registered program uses precisely the clipped field bank and predecessor
atoms. Its three input chart identifications are definitional. -/
theorem registered_funded_room (prior : DatePorts) (stageFloor : ℕ)
    (enoughArgs : prior.argumentsPerNode≤v.vector.operands)
    (paths : (v.registeredEntry prior stageFloor).clip.venue.paths=StageVenueTail.OrdinaryRaster.paths v.area)
    {w : ℕ} (inlet : (v.registeredEntry prior stageFloor).Room (v.registeredFrom prior stageFloor) stageFloor w)
    (previous : prior.PaidRoom w stageFloor) (split : (d).groups*2^(a).k=(a).G)
    (positive : 0<(v.registeredEntry prior stageFloor).clip.postPitch)
    (room : (v.registeredFrom prior stageFloor).rasterEnd stageFloor<2^w) :
    let W:=v.registeredFrom prior stageFloor
    W.FundedRoom stageFloor (W.fundedFromEntry stageFloor (v.registeredEntry prior stageFloor) paths) prior.io w := by
  let W:=v.registeredFrom prior stageFloor
  change W.FundedRoom stageFloor _ prior.io w
  exact W.funded_room_from_entry stageFloor prior (v.registeredEntry prior stageFloor)
    (v.registered_match prior stageFloor enoughArgs) paths inlet previous rfl rfl rfl split positive room

theorem raster_below_full (root : ℕ) : v.rasterEnd (v.stageStart root)≤v.fullEnd root := by
  let t:=v.stageStart root
  have venue : v.rasterEnd t≤v.venueEnd t:=by
    rw [venueEnd,v.venue.translates]; exact Nat.le_add_right ..
  have «meta» : v.venueEnd t≤v.metaEnd t:=by
    rw [metaEnd,v.metadata.ordinary_translate]; exact Nat.le_add_right ..
  have op : v.metaEnd t≤v.operandEnd t:=by
    rw [operandEnd,v.operandBook.affine]; exact Nat.le_add_right ..
  have prim : v.operandEnd t≤v.primitiveEnd t:=(v.primitive_spent _).2
  have last : v.primitiveEnd t≤v.returnedEnd t:=by
    exact (Nat.le_add_right (v.primitiveEnd t) (2^v.countBits)).trans
      ((Nat.le_add_right _ v.area.batch).trans (Nat.le_add_right _ 1))
  exact venue.trans («meta».trans (op.trans (prim.trans last)))

end
end Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary

end OAI
