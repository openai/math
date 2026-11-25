import OAI.Hierarchy.DescentResetStemProjectIndex
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
local notation "groups" => S.groupCount (i+1)

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

open DescentResetStemPackedIssue DescentResetStemPackedIssue.Mixed
open DescentSIMDLookup DescentResetStemIncidence

open DescentResetStemPackedIssue.Mixed DescentPackedZip DescentDyadicSpan ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure
local notation "L" => 2^(m-c)
local notation "Q" => DescentResetStemPackedIssue.count L (A).cap
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

theorem prepared_stem_registers (value : OldHost→ℕ) (room : ∀u,value u+1<2^field)
    (signBits : DescentSignedCableCodec.width degree (A).cap≤field)
    (onWire : ∀s (e : Grain A),value (home A (endSite A s e))=signedStemWord B s (home A (endSite A s e)))
    (actorId : input.V↪Fin prev) (values : Fin prev→Block c→Fin L→Cell t)
    (roster : Fin prev→Fin degree→Option (Fin prev))
    (chips : Fin prev→Block c→Fin L→Fin (2*(A).cap)→Option (Live degree (A).cap))
    (own : ∀v hi lo,(values (actorId v) hi lo).val=value (donors v hi lo))
    (chart : ∀v j,roster (actorId v) j=(oldRoster v j).map actorId)
    (saved : ∀v hi lo z,chips (actorId v) hi lo z=signs (donors v hi lo) z)
    (base : ℕ) (ports : DescentPackedColony.Ports degree)
    (bank : DescentFallbackPeriod.Projected.Column L (A).cap→Bank) (initial : Memory w₀)
    (fit : ∀i,(bank i).Fits w₀ base) (size : ∀i,prev*chunks (2^c) M₀≤(bank i).size)
    (peer : ∀lo,Accessible ports (bank (.inl (1,lo))) prev (2^c) M₀ w₀ base)
    (stored : Mounted ports roster initial (2^c) M₀)
    (local_ : ∀lo,DescentPackedColony.Reads (bank (.inl (0,lo))) (fun v j=>((values v j lo).val:Cell field)) M₀ initial)
    (tagged : ∀lo,DescentPackedColony.Reads (bank (.inl (1,lo))) (fun v j=>((values v j lo).val+1:Cell field)) M₀ initial)
    (signed : ∀z lo,DescentPackedColony.Reads (bank (.inr (z,lo))) (fun v j=>((DescentSignedCableCodec.encode (chips v j lo z)).val:Cell field)) M₀ initial)
    (rack : Fin HP→Option B.next.V) (owner : Fin HP→Fin prev)
    (parent : ∀r v,rack r=some v → owner r=actorId (B.frame.host.symm (position (Z).graph v.val))) :
    let src:=DescentResetStemPackedIssue.operands ports bank prev
    let parser:=DescentResetStemKey.parse degree (A).cap field
    ∃old : Fin Q→Fin prev→Fin (groups*X)→Fin (degree+2)→Cell field,
      (∀q i,(src q i).Fits w₀ base) ∧ (∀q i,Source (src q i) (fun h g=>old q h g i) M₀ initial) ∧
      (∀j h g₀,old j h g₀ (0:Fin (degree+1)).succ=
        ((DescentSignedCableCodec.encode (chips h (Fin.cast (stem_project_size B).symm g₀)
          (((ord).symm j).2.1) (((ord).symm j).2.2))).val:Cell field)) ∧
      ∀s (slot : Slot) r v g₀ x,rack r=some v→
        (DescentResetStemKey.word parser s (old ((ord) (s,slot)) (owner r) (finProdFinEquiv (g₀,x)))).val=
        DescentResetStemKey.code ((oldStemAt B ((g₀,v),x) s slot).map (stemTicket B s)) := by
  let ranks:=fun (_ : Fin prev) (_ : Fin (DescentSharedBookScan.width shapeBits Y degree))=>0
  let pane:=fun v h=>inputs (r:=shapeBits) (n:=(Z).n) (field:=field) (fun v j lo=>(values v j lo).val) roster chips ranks v h
  let original (q : Fin Q) (h : Fin prev) (j : Block c) :=
    let t:=((ord).symm q).2
    DescentResetStemKey.panel (pane h j) t.1 t.2
  let actual (q : Fin Q) (h : Fin prev) (j : Fin (groups*X)):=original q h (Fin.cast (stem_project_size B).symm j)
  refine ⟨actual,fun q i=>DescentResetStemKey.readers_fit ports bank base fit peer _ _ i,?_,fun _ _ _=>rfl,?_⟩
  · intro q i
    have native_:=DescentResetStemKey.operand_sources ports bank base values roster chips ranks initial fit size peer
      stored local_ tagged signed ((ord).symm q).2.1 ((ord).symm q).2.2 i
    exact DescentResetStemProjectIndex.flat_source (stem_project_size B)
      (fun (q' : Fin Q) h j=>original q' h j i) q _ initial native_
  · intro s slot h v g₀ x at_
    have observed:=stem_projected_operand_key (field:=field) B value room signBits onWire actorId values roster chips ranks
      own chart saved ((g₀,v),x) s slot
    dsimp only [actual,original,Equiv.symm_apply_apply]
    have low : (ord).symm ((ord) (s,slot))=(s,slot) := (ord).symm_apply_apply _
    have high : Fin.cast (stem_project_size B).symm (finProdFinEquiv (g₀,x)) =
        (receiverRoot B ((g₀,v),x)).2 := stem_project_rack B ((g₀,v),x)
    rw [parent h v at_,low,high]
    exact observed

theorem prepared_stem_operands (value : OldHost→ℕ) (room : ∀u,value u+1<2^field)
    (signBits : DescentSignedCableCodec.width degree (A).cap≤field)
    (onWire : ∀s (e : Grain A),value (home A (endSite A s e))=signedStemWord B s (home A (endSite A s e)))
    (actorId : input.V↪Fin prev) (values : Fin prev→Block c→Fin L→Cell t)
    (roster : Fin prev→Fin degree→Option (Fin prev))
    (chips : Fin prev→Block c→Fin L→Fin (2*(A).cap)→Option (Live degree (A).cap))
    (own : ∀v hi lo,(values (actorId v) hi lo).val=value (donors v hi lo))
    (chart : ∀v j,roster (actorId v) j=(oldRoster v j).map actorId)
    (saved : ∀v hi lo z,chips (actorId v) hi lo z=signs (donors v hi lo) z)
    (base : ℕ) (ports : DescentPackedColony.Ports degree)
    (bank : DescentFallbackPeriod.Projected.Column L (A).cap→Bank) (initial : Memory w₀)
    (fit : ∀i,(bank i).Fits w₀ base) (size : ∀i,prev*chunks (2^c) M₀≤(bank i).size)
    (peer : ∀lo,Accessible ports (bank (.inl (1,lo))) prev (2^c) M₀ w₀ base)
    (stored : Mounted ports roster initial (2^c) M₀)
    (local_ : ∀lo,DescentPackedColony.Reads (bank (.inl (0,lo))) (fun v j=>((values v j lo).val:Cell field)) M₀ initial)
    (tagged : ∀lo,DescentPackedColony.Reads (bank (.inl (1,lo))) (fun v j=>((values v j lo).val+1:Cell field)) M₀ initial)
    (signed : ∀z lo,DescentPackedColony.Reads (bank (.inr (z,lo))) (fun v j=>((DescentSignedCableCodec.encode (chips v j lo z)).val:Cell field)) M₀ initial)
    (rack : Fin HP→Option B.next.V) (owner : Fin HP→Fin prev)
    (parent : ∀r v,rack r=some v → owner r=actorId (B.frame.host.symm (position (Z).graph v.val))) :
    let src:=DescentResetStemPackedIssue.operands ports bank prev
    let parser:=DescentResetStemKey.parse degree (A).cap field
    ∃old : Fin Q→Fin prev→Fin (groups*X)→Fin (degree+2)→Cell field,
      (∀q i,(src q i).Fits w₀ base) ∧ (∀q i,Source (src q i) (fun h g=>old q h g i) M₀ initial) ∧
      ∀s (slot : Slot) r v g₀ x,rack r=some v→
        (DescentResetStemKey.word parser s (old ((ord) (s,slot)) (owner r) (finProdFinEquiv (g₀,x)))).val=
        DescentResetStemKey.code ((oldStemAt B ((g₀,v),x) s slot).map (stemTicket B s)) := by
  obtain ⟨data_,fitsData,read,_,keys⟩:=prepared_stem_registers B value room signBits onWire actorId values roster chips own chart saved
    base ports bank initial fit size peer stored local_ tagged signed rack owner parent
  exact ⟨data_,fitsData,read,keys⟩

end
end Hierarchy.DescentSixParty.ClosedReset.Window

end OAI
