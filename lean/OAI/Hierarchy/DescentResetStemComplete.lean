import OAI.Hierarchy.DescentResetStemPreparedOperands
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

local notation "rawRank" => ((Z).rawHostRank T vertexCode).trans Fin.valEmbedding

local notation "A" => input.placement
local notation "digitsIn" => S.resetInputDigits ctl.base ctl.radix i
local notation "c" => (T).commonDepth
local notation "m" => S.groupWidth k tail i+k
local notation "before" => input.order.trans Fin.valEmbedding
local notation "fits" => B.frame.enough.trans (Nat.sub_le ..)

local notation "Slot" => Fin (2^(m-c))×Fin (2*(A).cap)

open DescentResetFieldAssembler DescentResetWindowResidentSources
local notation "rank" => (Z).rawHostRank T vertexCode

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

variable (ptr b M : ℕ)
variable (ports : DescentResetStemIncidence.Ports
  (2*(2*DescentFallbackShapeTable.rows (B.reset.k-B.terminals.commonDepth) (2^B.reset.n))))
local notation "paletteSize" B₀:arg D₀:arg n₀:arg f₀:arg g₀:arg =>
  (DescentDenseHostOrder.roster (B₀).reset.graph ((B₀).reset.k-(B₀).terminals.commonDepth)
    (GroupStage.depthBound D₀ n₀ f₀ g₀)).card
variable (here : Fin (Fintype.card B.next.V)→Fin (prev*(paletteSize B D n f g)))
  (parent : Fin (Fintype.card B.next.V)→Fin prev)
  (physical : 0<HP→0<prev*(paletteSize B D n f g))
  (near : Fin (prev*(paletteSize B D n f g))→Fin 3→Option (Fin (prev*(paletteSize B D n f g))))
  (hub : Fin prev→Bool)
local notation "scene" => DescentResetStemMaskedPorts.scene (count:=rows) (oldH:=prev)
  (palette:=(pool).card) (H:=HP) («K»:=2*K) here parent physical near hub (stemTemplates B)

theorem issued_from_prepared (value : OldHost→ℕ) (room : ∀u,value u+1<2^field)
    (signBits : DescentSignedCableCodec.width degree (A).cap≤field)
    (onWire : ∀s (e : Grain A),value (home A (endSite A s e))=signedStemWord B s (home A (endSite A s e)))
    (actorId : input.V↪Fin prev) (values : Fin prev→Block c→Fin L→Cell t)
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
    (rack : Fin HP→Option B.next.V) (owner : Fin HP→Fin prev)
    (parentAt : ∀r v,rack r=some v → owner r=actorId (B.frame.host.symm (position (Z).graph v.val)))
    (ha : 0<M₀) (hm : 0<M)
    (mounted : DescentResetStemIncidence.Reads ports (scene) initial) (safe : ports.All (Expr.Fits w₀ base))
    (directory : DescentResetStemKeyReindex.Directory ptr owner initial)
    (ptrFit : ptr+span HP≤ base) (hostFit : prev*(pool).card<2^w₀) (width : (b*7)*M≤ w₀)
    (limit : Projected.extent base ptr degree field b K prev HP groups X M₀ M Q<2^w₀)
    (located : ∀r v,rack r=some v → r.val< rows) (idle : ∀r,rack r=none → rows≤ r.val)
    (id : ∀r v,(h₁ : rack r=some v)→(here ⟨r.val,located r v h₁⟩).val=(rank v).val)
    (root : ∀r v,(h₁ : rack r=some v)→(parent ⟨r.val,located r v h₁⟩).val=
      ((vertexCode) (position (Z).graph v.val)).val)
    (halo : ∀r v,(h₁ : rack r=some v)→(DescentSortedRoster.present near (here ⟨r.val,located r v h₁⟩)).map
      Fin.valEmbedding=(B.next.placement.near v).map rawRank)
    (oldHub : ∀r v,(h₁ : rack r=some v)→hub (parent ⟨r.val,located r v h₁⟩)=(A).hub (B.frame.host.symm (position (Z).graph v.val))) :
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
  obtain ⟨data_,fitsData,read,key⟩:=prepared_stem_operands B value room signBits onWire actorId values roster chips own chart saved
    base peers bank initial fit size peer stored local_ tagged signed rack owner parentAt
  exact emitted_stems B base ptr b M₀ M (DescentResetStemKey.parse degree (A).cap field) (DescentResetStemPackedIssue.operands peers bank prev)
    ports here parent physical near hub initial ha hm data_ fitsData read mounted safe owner directory ptrFit hostFit width
    (DescentResetStemKey.parse_zero degree (A).cap field) limit rack located idle id root halo oldHub key

end
end Hierarchy.DescentSixParty.ClosedReset.Window

end OAI
