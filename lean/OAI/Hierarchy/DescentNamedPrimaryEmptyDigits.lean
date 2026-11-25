import OAI.Hierarchy.DescentNamedPrimaryEmptyShape
import OAI.Hierarchy.DescentCalendarRootCensus
import OAI.Hierarchy.DescentCalendarVacantRootRange

namespace OAI
/-! # All three native span digits vanish at a vacant registered primary -/
namespace Hierarchy.DescentDatedAddressBook.PhysicalReset
open DescentSixParty.Chronology DescentSixParty DescentCompiler DescentPackedWalsh DescentSIMDLookup
open DescentCommonHost DescentDenseHostOrder DescentFallbackPeriod DescentRecordedRotorLayers
open ProtocolRAM
noncomputable section
set_option quotPrecheck false
set_option hygiene false
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open DescentActorRaster DescentPackedZip DescentPackedColony DescentColonies
open scoped Classical Fin.CommRing
variable {F X : Type} [Field F] {d : ℕ} {abits : X→ℕ} {W : MarkedWorld F d X abits}
  {G : PoweredGadget F} {q ε : ℝ} {S : DescentCompiler.AtomSchedule} {k age z wire hist D n h C f g cut tail p : ℕ}
  {input : Reached W G q ε S k age z D wire hist} {ctl : ResetRates G S k D n h C f g cut tail}
  {B : ClosedReset input ctl} (accepted : B.Recorded p)
local notation "board" => ctl.board
local notation "packet" => ctl.bitsR
variable (drift degree payload e previous M nextM oldLanes primitiveLanes printedBits : ℕ)
  (venue : StageVenueTail.Date) (io : Hierarchy.DescentPacking.PackedMatch.Local.Stage.Dated.Operands) (floor w : ℕ)
local notation "namedReset" => named G S board k tail age p f g drift degree payload e previous M nextM C packet
  oldLanes primitiveLanes printedBits venue io.wire io.roster floor
local notation "namedSuccessor" => (namedReset).successor
local notation "start" => (namedReset).stageStart floor
local notation "base₀" => (namedReset).rebased start
local notation "cc" => S.groupWidth k tail age
local notation "cal" => capCalendar G.b S.rounds g S.height
local notation "cap" => ((cal).take age).prod*256
local notation "wide" => laneBits (cc+k) payload (S.localWalshBits p (cc+k) f (quota S.rounds))
variable (fitsStencil : e≤wide-k) (fitsSigned : e≤previous) (fitsCut : previous≤cc) (count : Bank)
local notation "sh" => namedStencil G S board k tail age p f g drift degree payload e previous M nextM C packet
  oldLanes primitiveLanes printedBits venue io floor fitsStencil
local notation "roots" => namedRoots G S board k tail age p f g drift degree payload e previous M nextM C packet
  oldLanes primitiveLanes printedBits venue io floor fitsSigned fitsCut
local notation "atlas" => namedAtlas G S board k tail age p f g drift degree payload e previous M nextM C packet
  oldLanes primitiveLanes printedBits venue io floor sh count
local notation "rc" => (namedReset).rootPhase sh start count io.hubs g (2^n) roots w
local notation "book" => atlasBook atlas sh start count io.hubs g (2^n) roots w
local notation "early" => (namedSuccessor).actorEnd base₀

local notation "older" => namedOriginals G S board k tail age p f g drift degree payload e previous M nextM C packet
  oldLanes primitiveLanes printedBits venue io floor w fitsStencil fitsSigned fitsCut count
local notation "I₀" => DateInputs.fromNamed G S board k tail age p f g drift degree payload e previous M nextM C packet
  oldLanes primitiveLanes printedBits venue io floor w fitsStencil fitsSigned fitsCut count
variable (previousMeta previousArguments : ℕ) (initial : Bool) (prepared : (rc).PreparedFits book)
  (sceneRoom : (namedSuccessor).front.SceneRoom early ((namedSuccessor).issuedScene base₀ older) w)
local notation "dateInput" => I₀ previousMeta previousArguments initial prepared sceneRoom
local notation "Z" => B.reset
local notation "T" => B.terminals
local notation "idx" => input.vertex.trans (Fin.castLEEmb input.valid.host)
local notation "rank" => B.frame.host.symm.toEmbedding.trans idx
local notation "HH" => S.hostSize age

open DescentGL DescentColonies DescentMeasuredHeader DescentBaseProfile DescentBaseVariance DescentWalshPrecision
open DescentGLPacked DescentGLPacked.BankImage
local notation "digits" => S.resetInputDigits ctl.base ctl.radix age

local notation "res" => (Z).k-(T).commonDepth
local notation "rows" => (roster (Z).graph res (GroupStage.depthBound D n f g)).card

open DescentSortedRoster
local notation:max "imageOf" degreeAt:arg capAt:arg => fromNamed_root_image (B:=B) drift degree payload e previous M nextM
  oldLanes primitiveLanes printedBits venue io floor w fitsStencil fitsSigned fitsCut count prepared degreeAt capAt
open DescentSixParty.ClosedReset.Window DescentOperandRootPull DescentSixParty.PackedFlow.Channels
local notation "setup" => (namedSuccessor).setup
local notation "r" => (setup).retained
local notation "M₁" => 2^e
local notation "coarse" => (T).commonDepth
local notation "span" => (Z).k-coarse
local notation "field" => (namedSuccessor).middle.rootField
local notation "A₁" => input.placement
local notation "rn₁" => (calendar_residual B).symm
local notation "half₁" => (show (namedReset).c/2=cap by change (2*cap)/2=cap;omega)

open DescentSixParty.Chronology.DatePorts
open DescentLocalArchiveOrder DescentKernelHistory DescentPrimitivePalette DescentRetainedRangeDigits
open DescentFallbackShapeTable DescentRelativeContacts DescentIssuedFallbackPanel
variable (degreeAt : venue.degree=D) (capAt : input.placement.cap=cap)
local notation "im_" => imageOf degreeAt capAt
variable (oldA : Archive W) (num : Local oldA.bit) (hp : 0<p) (whole : p∣(Z).unit)
local notation "after_" => (resetArchive B p hp whole oldA).bit
local notation "newNum" => DescentLocalArchiveOrder.reset B p hp whole oldA num
variable (ports : DatePorts) (places : DatePorts.RangeRoom ports B.next after_)
    (block : Fin (2^ports.venue.k)) (node : Fin ports.nodes) (rack : Fin ports.operandHosts) (group : Fin ports.venue.groups)
variable (present:rack.val<Fintype.card B.next.V)
    (absent:DatePorts.slotAt ports B.next after_ newNum places block node rack group=none)
    (size:HH*rows=(setup).placement.sparse)
local notation "dirs" => fun j:Fin (Fintype.card B.next.V)=>((Z).rawAtIndex T rank j).cast size
local notation "tok" => (setup).placement.shape (dirs ⟨rack.val,present⟩)
local notation:max "oldHost" t:arg => B.frame.host.symm ((T).code t).1
local notation "res_" => (Z).k-(T).commonDepth
local notation:max "code" t:arg => DescentFallbackShapeTable.cell res_ (shortName (T).commonDepth ((T).code t)).2
local notation:max "primaryHigh" t:arg => (Z).rootBlock T (.inr t)
local notation "out" => S.resetOutputDigits ctl.base ctl.radix B.age B.commonDepth
local notation "high_" => (out).symm (group.cast places.groups.symm,block.cast (congrArg (2^·) places.radix.symm))

open DescentRetainedControl DescentPaidResidentCount.Reset DescentResetLocalNodes
open DescentRetainedRangeDigits DescentPlainTerminal DescentPacking.PackedMatch.Local.Stage
variable (measured:Memory w) (hdr:OriginalHeader B input.valid.host (im_).receiver (im_).book measured)
    (xs:OriginalArrays B input.valid.host field) (windows:(setup).seven.Packets)
    (matrixRead:∀v hi,(windows v hi).val=(encode field (DescentRotorWindowArchive.count (A₁).degree (2^span) (A₁).cap)
      (calendar_sender_matrix B M₁ field (im_).receiver (im_).book (im_).prepared measured hdr xs v
        ⟨hi.val,by rw [B.commonDepth];exact hi.isLt⟩)).val)
    (geo:(setup).MovementShape) (basis:DescentGL.Layout ((r).high+(r).low)) (won:HEq basis B.frame.basis) (oldValues:(r).Values)
    (total:(r).high+(r).low=cc+k) (groupSize:(r).groups=S.groupCount age) (blockSize:(r).blocks=2^k)
    (population:OriginalRootCounts (input:=input) (oldA:=oldA) (r) oldValues
      geo.size geo.cut basis input.valid.host groupSize blockSize)
    (operand:Fin (r).args) (slot:Fin (r).nodes) (rh:Fin (setup).placement.newHosts) (rg:Fin (setup).placement.groups)
    (x₀:Fin (setup).placement.blocks) (nodeAt:slot.val=node.val) (hostAt:rh.val=rack.val)
    (groupAt:rg.val=group.val) (blockAt:x₀.val=block.val)
local notation "cut_" => (show (r).cut=coarse from B.commonDepth.symm)
local notation "coords" => finCongr (congrArg (fun t=>2^t) (congrArg₂ Nat.sub total cut_))
local notation "physicalHi" => (high_).cast (congrArg (2^·) cut_).symm
local notation "strips" => fun j=>blockValues geo.cut ((r).before geo.size oldValues j) basis
local notation "prev_" => ((setup).placement.previous (dirs ⟨rack.val,present⟩)).cast geo.host
local notation "physicalHigh" => (finProdFinEquiv (rg,x₀)).cast geo.groups
local notation:max "src" hi:arg lo:arg => (rearrange B.frame.basis).symm (join (B.frame.enough.trans (Nat.sub_le ..)) hi lo)

set_option maxHeartbeats 900000 in
include absent degreeAt matrixRead won population nodeAt groupAt blockAt total in
theorem DateInputs.decoded_primary_empty (kept:(dateInput).menu.keep tok=true) (axis:Fin 3) :
    (setup).seven.decoded (dateInput).bank.which windows strips ((r).outputID 1 (page axis) operand slot)
      tok prev_ physicalHigh=0:=by
  obtain ⟨t₀,key,hAt,alternatives⟩:=DateInputs.named_empty_primary_shape (B:=B)
    drift degree payload e previous M nextM oldLanes primitiveLanes printedBits venue io floor w
    fitsStencil fitsSigned fitsCut count previousMeta previousArguments initial prepared sceneRoom degreeAt
    oldA num hp whole ports places block node rack group present absent size kept
  have holder : prev_=idx (oldHost t₀):=Fin.ext hAt
  have highNum:(finProdFinEquiv (out high_)).val=(high_).val:=by
    simp [AtomSchedule.resetOutputDigits,AtomSchedule.resetInputDigits,finCongr]
  rw [Equiv.apply_symm_apply] at highNum
  have highAt:physicalHigh=physicalHi:=by
    apply Fin.ext
    simp only [Fin.val_cast,finProdFinEquiv_apply_val,groupAt,blockAt] at highNum ⊢
    have placementBlocks : (setup).placement.blocks = 2^k := rfl
    simpa only [placementBlocks,Nat.mul_comm,Nat.add_comm] using highNum
  refine (congrArg₂ (fun h q => (setup).seven.decoded (dateInput).bank.which windows strips
    ((r).outputID 1 (page axis) operand slot) tok h q) holder highAt).trans ?_
  let v₀:=oldHost t₀
  let host:=idx v₀
  let q₀:=high_
  let word:=xs.stencil host q₀
  have fit (lo) : word lo+1<2^field :=
    (congrArg (· + 1) (xs.localRead v₀ q₀ lo)).trans_lt (xs.fits _)
  have fits lo : word lo<2^field:=Nat.lt_trans (Nat.lt_succ_self _) (fit lo)
  have nonzero:0<field:=by
    by_contra neg
    have zero_:field=0:=Nat.eq_zero_of_not_pos neg
    have bad:=fit (0:DescentColonies.Block ((cc+k)-coarse))
    rw [zero_,pow_zero] at bad
    omega
  have sameRead:=matrixRead host physicalHi
  have deg_:(setup).seven.degree=input.placement.degree:=degreeAt.trans input.branch.symm
  have cap_:(setup).seven.capacity=input.placement.cap:=(dateInput).menu.capacity.trans ((half₁).trans capAt.symm)
  have paired:=registered_window_selectors B M₁ field (im_).receiver (im_).book (im_).prepared measured hdr xs
    setup (dateInput).bank.which windows tok host physicalHi host q₀ (code t₀) key deg_
    ((dateInput).menu.donors.trans (congrArg (2^·) rn₁)) cap_ rfl sameRead nonzero fits
  have owns:ownerAt setup (dateInput).bank.which windows tok host physicalHi=
      (fun i=>decide (word (coords i)/2=code t₀)):=by
    refine paired.1.trans ?_
    funext i
    apply congrArg (fun lo => decide (word lo / 2 = code t₀))
    exact Fin.ext rfl
  have order_:priorAt setup windows host physicalHi=(fun i j=>decide (src q₀ (coords i)<src q₀ (coords j))):=by
    refine paired.2.trans ?_
    funext i j
    apply congrArg₂ (fun lo lo' => decide (src q₀ lo < src q₀ lo'))
    · exact Fin.ext rfl
    · exact Fin.ext rfl
  have stencil:=primary_original_stencil B xs v₀ q₀
  rcases alternatives with ⟨t,⟨h,atHigh,codeEq⟩,padded⟩|empty_
  · have oldAt:oldHost t=v₀:=by rw [h,Equiv.symm_apply_apply]
    have selected (v' : input.V) (z' : DescentColonies.Block coarse) (k' : ℕ)
        (hv : v' = v₀) (hz : z' = q₀) (hk : k' = code t₀) :
        ownerAt setup (dateInput).bank.which windows tok (idx v') (z'.cast (congrArg (2^·) cut_).symm) =
          (fun i => decide (xs.stencil (idx v') z' (coords i) / 2 = k')) := by
      subst v'; subst z'; subst k'
      exact owns
    have compared (v' : input.V) (z' : DescentColonies.Block coarse)
        (hv : v' = v₀) (hz : z' = q₀) :
        priorAt setup windows (idx v') (z'.cast (congrArg (2^·) cut_).symm) =
          (fun i j => decide (src z' (coords i) < src z' (coords j))) := by
      subst v'; subst z'
      exact order_
    have answer:=(calendar_empty_primary (b:=B) (a:=oldA) (chart:=setup) (total:=total) (axis:=cut_)
      (blocks:=blockSize) (groups:=groupSize) (size:=geo.size) (fits:=geo.cut) (L:=basis) (won:=won)
      (room:=input.valid.host) (t:=t) (which:=(dateInput).bank.which) (window:=windows) (shape:=tok)
      (input:=oldValues) (word:=xs.stencil (idx (oldHost t)) (primaryHigh t))
      (owns:=selected _ _ _ oldAt atHigh codeEq)
      (compared:=compared _ _ oldAt atHigh)
      (stencil:=primary_original_stencil B xs (oldHost t) (primaryHigh t))
      (counts:=fun lo=>population _ _ ((coords).symm lo)) slot (by simpa only [nodeAt] using padded) operand axis)
    let decoded (v' : input.V) (z' : DescentColonies.Block coarse) :=
      (setup).seven.decoded (dateInput).bank.which windows strips ((r).outputID 1 (page axis) operand slot)
        tok (idx v') (z'.cast (congrArg (2^·) cut_).symm)
    exact (congrArg₂ decoded oldAt atHigh).symm.trans answer
  · apply calendar_vacant_root_range B.frame _ _ _ _ _ _ _ _ _ _ (ClosedReset.Recorded.old_roster (reset:=B))
      v₀ q₀ (code t₀) word stencil empty_ setup coords tok host physicalHi
      (dateInput).bank.which windows strips slot operand axis (fun s=>Fintype.card (oldA.bit.recipe s).Node)
    · intro lo
      exact calendar_row_census (b:=B) (a:=oldA) (chart:=setup) (total:=total) (axis:=cut_) (blocks:=blockSize)
        (groups:=groupSize) (size:=geo.size) (fits:=geo.cut) (L:=basis) (won:=won) (room:=input.valid.host)
        (prev:=v₀) (hi:=q₀) (input:=oldValues) (counts:=population) lo
    · exact owns
    · exact order_

end
end Hierarchy.DescentDatedAddressBook.PhysicalReset

end OAI
