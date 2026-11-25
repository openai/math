import OAI.Hierarchy.DescentResetStemRackGeometry
import OAI.Hierarchy.DescentResetStemComplete
import OAI.Hierarchy.DescentResetStemIssuedDeck
import OAI.Hierarchy.DescentResetStemTemplateScene
import OAI.Hierarchy.DescentResetStemProjected
import OAI.Hierarchy.DescentResetStemIssuedWindows

namespace OAI
/-! # The measured public stem template resolves to the physical row emitted at every occupied host -/
namespace Hierarchy.DescentSixParty.ClosedReset.Window
open DescentSharedCableNames DescentIssuedFallbackPanel DescentGL DescentSIMDLookup DescentSharedCableNames.Stage
open DescentResetCableSlots DescentResetLocalRoster DescentParallelBase DescentResetAttachments
open DescentCompiler DescentColonies DescentCommonHost DescentChosenRouter DescentMixedRouter
open DescentStageEdgeReceipt DescentDenseHostOrder DescentResetTrunks
open scoped Classical
open scoped Fin.CommRing
noncomputable section

variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits}
  {G : PoweredGadget F} {q ε : ℝ} {S : AtomSchedule} {k i z D n h C f g cut tail w hist : ℕ}
  {input : Reached W G q ε S k i z D w hist} {ctl : ResetRates G S k D n h C f g cut tail}
  (B : ClosedReset input ctl)

set_option quotPrecheck false
local notation "Z" => B.reset
local notation "T" => B.terminals
local notation "vertexCode" => B.frame.host.symm.toEmbedding.trans input.vertex
local notation "groups" => S.groupCount (i+1)
local notation "height" => GroupStage.depthBound D n f g

local notation "A" => input.placement
local notation "digitsIn" => S.resetInputDigits ctl.base ctl.radix i
local notation "c" => (T).commonDepth
local notation "m" => S.groupWidth k tail i+k
local notation "before" => input.order.trans Fin.valEmbedding
local notation "fits" => B.frame.enough.trans (Nat.sub_le ..)

local notation "Slot" => Fin (2^(m-c))×Fin (2*(A).cap)

open DescentResetFieldAssembler DescentResetWindowResidentSources

open DescentResetStemDecoder DescentRelativeContacts
local notation "Y" => 2^(Z).n
local notation "shapeBits" => (Z).k-c

local notation "shapeCount" => DescentFallbackShapeTable.rows shapeBits Y
local notation "K" => 2*shapeCount

open DescentResetStemPackedIssue DescentResetStemPackedIssue.Mixed
open DescentSIMDLookup DescentResetStemIncidence
local notation "pool" => DescentDenseHostOrder.roster (Z).graph shapeBits height
local notation "rows" => Fintype.card B.next.V

open DescentResetStemPackedIssue.Mixed DescentPackedZip DescentDyadicSpan ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure
local notation "L" => 2^(m-c)
local notation "Q" => DescentResetStemPackedIssue.count L (A).cap
local notation "sid" => DescentResetStemPackedIssue.side L (A).cap
local notation "ord" => DescentResetStemPackedIssue.ordinal L (A).cap
local notation "X" => 2^k
local notation "degree" => (A).degree

open DescentGroupPeerOrder DescentGL DescentTreePrefixIntervals DescentPacking.PackedMatch.Local.Stage
open DescentSharedBookScan DescentFallbackPeriod DescentPackedColony
local notation "OldHost" => Stage.Host (Fin (S.groupCount i)) input.V k
local notation "beforeRank" => input.vertex.trans Fin.valEmbedding
local notation "groupKey" => Fin.valEmbedding (n:=S.groupCount i)
local notation "donors" => donor digitsIn B.frame.basis fits
local notation "oldNames" => cableNames k (groupRank groupKey beforeRank)
local notation "oldRoster" => hostRoster A beforeRank
local notation "signs" => signedPanel A before S input.valid oldNames
variable {field HP prev t M₀ w₀ : ℕ}

open DescentResetStemMaskedPorts DescentResetStemKeyReindex DescentSortedRoster DescentResetPeerUnionRAM
variable (ptr b M : ℕ) (previous : Fintype.card input.V≤prev)
local notation "actorId" => input.vertex.trans (Fin.castLEEmb previous)
local notation "vr" => (vertexCode).trans (Fin.castLEEmb previous)
local notation "Parea" => prev*(pool).card
local notation "padded" => (Z).rawHostRank T (vr)
local notation "denseHere" => (Z).rawAtIndex T (vr)
local notation "denseParent" => (Z).parentIndex T (vr)
local notation "honestHub" => priorHub (vr) (fun z=>input.placement.hub (B.frame.host.symm z))
local notation "realRack" => originalTrunkRack (H:=HP) B

theorem issued_from_registers (value : OldHost→ℕ) (room : ∀u,value u+1<2^field)
    (signBits : DescentSignedCableCodec.width degree (A).cap≤field)
    (onWire : ∀s (e : Grain A),value (home A (endSite A s e))=signedStemWord B s (home A (endSite A s e)))
    (values : Fin prev→Block c→Fin L→Cell t)
    (roster : Fin prev→Fin degree→Option (Fin prev))
    (chips : Fin prev→Block c→Fin L→Fin (2*(A).cap)→Option (Live degree (A).cap))
    (own : ∀v hi lo,(values (actorId v) hi lo).val=value (donors v hi lo))
    (chart : ∀v j,roster (actorId v) j=(oldRoster v j).map actorId)
    (saved : ∀v hi lo z,chips (actorId v) hi lo z=signs (donors v hi lo) z)
    (base : ℕ) (peers : DescentPackedColony.Ports degree)
    (bank : DescentFallbackPeriod.Projected.Column L (A).cap→Bank) (initial : Memory w₀)
    (fit : ∀i,(bank i).Fits w₀ base) (size : ∀i,prev*chunks (2^c) M₀≤(bank i).size)
    (peer : ∀lo,Accessible peers (bank (.inl (1,lo))) prev (2^c) M₀ w₀ base)
    (stored : Mounted peers roster initial (2^c) M₀)
    (local_ : ∀lo,DescentPackedColony.Reads (bank (.inl (0,lo))) (fun v j=>((values v j lo).val:Cell field)) M₀ initial)
    (tagged : ∀lo,DescentPackedColony.Reads (bank (.inl (1,lo))) (fun v j=>((values v j lo).val+1:Cell field)) M₀ initial)
    (signed : ∀z lo,DescentPackedColony.Reads (bank (.inr (z,lo))) (fun v j=>((DescentSignedCableCodec.encode (chips v j lo z)).val:Cell field)) M₀ initial)
    (number : Bank) (banks : DescentResetStemTemplatePorts.Banks)
    (near : Fin Parea→Fin 3→Option (Fin Parea)) (physical : 0<HP→0<Parea)
    (measured : DescentResetStemMaskedPorts.Stored banks number (denseHere) (denseParent) near (honestHub) initial)
    (registers : DescentResetStemTemplatePorts.Room banks rows prev (pool).card w₀ base) (numFit : number.Fits w₀ base)
    (_capacity : rows≤HP) (directory : Directory ptr (denseParent) initial)
    (ghost : ∀j : Fin HP,rows≤j.val→initial (ptr+j.val)=0) (ha : 0<M₀) (hm : 0<M)
    (ptrFit : ptr+span HP≤base) (hostFit : Parea<2^w₀) (width : (b*7)*M≤w₀)
    (limit : Projected.extent base ptr degree field b K prev HP groups X M₀ M Q<2^w₀)
    {p : ℕ} (record : B.Recorded p)
    (four : ∀v,present (selfPeers near) ((padded) v)=(insert v ((Z).emittedNear T v)).map (padded))
    (absence : ∀v,(∀j,near ((padded) v) j≠some ((padded) v)) ↔ v∉(Z).emittedNear T v) :
    let ports:=DescentResetStemMaskedPorts.ports banks number prev (stemTemplates B)
    let rack:=realRack
    let parse:=DescentResetStemKey.parse degree (A).cap field
    let src:=DescentResetStemPackedIssue.operands peers bank prev
    let cut:=Projected.splitAt base Q degree prev groups X field M₀ M
    let arena:=plan cut ptr K HP
    let last:=Projected.image base ptr b prev HP groups X M₀ M parse sid src ports initial
    (Projected.program base ptr b prev HP groups X M₀ M parse sid src ports w₀).Exec initial (last)
      (Projected.ticks base ptr b prev HP groups X M₀ M parse sid src ports w₀) ∧
    ∀x s (slot : Slot) (p : Row HP groups M),
      last (arena.out degree field (b*7) K M prev HP groups (X*Q)+
        (finProdFinEquiv (x,(ord) (s,slot))).val*(HP*chunks groups M)+(row HP groups M p).val)=
        ((data (fun r g₀=>(rack r).elim 0 (fun v=>DescentResetFieldAssembler.raw b («meta» B ((g₀,v),x)
          (localOrigin B ((g₀,v),x) (stemIndex B s slot))))) p).val:Word w₀) := by
  let operands:=DescentResetStemMaskedPorts.ports banks number prev (stemTemplates B)
  have nonempty : 0<HP→0<prev:=fun live=>Nat.pos_of_ne_zero (by intro zero;have pos:=physical live;rw [zero,Nat.zero_mul] at pos;omega)
  let owner:=paddedParent (denseParent) (le_refl prev) nonempty
  have full : Directory ptr owner initial:=padded_directory ptr (denseParent) (le_refl prev) nonempty initial directory ghost
  have selected (j : Fin HP) v (held : (realRack) j=some v) := (input_rack B previous j).trans held
  have located (j : Fin HP) v (held : (realRack) j=some v) :=(Z).rack_located T (vr) j v (selected j v held)
  have idle (j : Fin HP) (empty : (realRack) j=none) :=(Z).rack_idle T (vr) j ((input_rack B previous j).trans empty)
  have ownerAt (j : Fin HP) v (held : (realRack) j=some v) :=(Z).rack_owner T (vr) nonempty j v (selected j v held)
  have rowWord : HP ≤ 2^w₀ := by
    have baseWord : base < 2^w₀ := by
      rw [Projected.extent,DescentResetStemPackedIssue.Mixed.affine,Projected.splitAt,DescentResetStemProject.extent] at limit
      omega
    exact (span_ge HP).trans ((Nat.le_add_left _ ptr).trans (ptrFit.trans baseWord.le))
  have mounted:=DescentResetStemMaskedPorts.read banks number (denseHere) (denseParent) physical near (honestHub)
    (stemTemplates B) initial registers numFit rowWord measured
  have safe:=DescentResetStemMaskedPorts.fits banks number prev (stemTemplates B) registers numFit
  refine issued_from_prepared B ptr b M operands (denseHere) (denseParent) physical near (honestHub)
    value room signBits onWire (actorId) values roster chips own chart saved base peers bank initial
    fit size peer stored local_ tagged signed (realRack) owner ownerAt ha hm mounted safe full ptrFit hostFit width limit
    located idle ?_ ?_ ?_ ?_
  · intro j v held
    exact (calibrated_rack B previous j v held).1
  · intro j v held
    exact (calibrated_rack B previous j v held).2.1
  · intro j v held
    have hit:=(Z).rack_registers T (vr) (fun z=>input.placement.hub (B.frame.host.symm z)) j v (selected j v held)
    exact (congrArg (fun u : Fin Parea => (present near u).map Fin.valEmbedding) hit.1).trans
      (calibrated_halo B previous record near v (four v) (absence v))
  · intro j v held
    exact (calibrated_rack B previous j v held).2.2

end
end Hierarchy.DescentSixParty.ClosedReset.Window

end OAI
