import OAI.Hierarchy.DescentInstalledRotorRoleRun
import OAI.Hierarchy.DescentRecordedPublicBoard
import OAI.Hierarchy.DescentMeasuredSenderDesk
import OAI.Hierarchy.DescentRecordedRotorLayers

namespace OAI
/-! # Rotor operation digits from the observed reservation matrix of the reached reset -/
namespace Hierarchy.DescentSixParty.ClosedReset.Window
open DescentCompiler DescentColonies DescentGL DescentResetHostSize DescentSIMDLookup DescentSharedBookScan
open DescentRotorWindowArchive DescentFallbackPeriod DescentFallbackPeriod.Projected DescentGroupPeerOrder
open DescentPaidResidentCount.Reset DescentOldContactSender DescentStageEdgeReceipt DescentRosterOrder
open DescentSharedCableNames.Stage DescentIssuedFallbackPanel DescentResetLocalRoster DescentPacking
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false
variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits}
  {G : PoweredGadget F} {q ε : ℝ} {S : AtomSchedule} {k i z w hist D n h C f g cut tail field : ℕ}
  {input : Reached W G q ε S k i z D w hist} {ctl : ResetRates G S k D n h C f g cut tail}
  (B : ClosedReset input ctl)
local notation "A" => input.placement
local notation "Z" => B.reset
local notation "T" => B.terminals
local notation "c" => (T).commonDepth
local notation "r" => (Z).k-c
local notation "Y" => 2^(Z).n
local notation "H" => S.hostSize i
local notation "dep" => GroupStage.depthBound D n f g
local notation "host" => input.vertex.trans (Fin.castLEEmb input.valid.host)
local notation "dim" => S.groupWidth k tail i+k
local notation "L" => 2^(dim-c)
local notation "short" => B.frame.enough.trans (Nat.sub_le ..)
local notation "name" => Recorded.oldName input
local notation "next" => PackedFlow.Padded.roster (D:=(A).degree) (A) name input.valid.host
local notation "paid" => Recorded.paddedValue (b:=field) c r next (Recorded.oldDepth B) (Recorded.oldWidth B)
variable (obs : PaddedSnapshot B input.valid.host field)
local notation "rank" => ranks (a:=r) («Y»:=Y) (D:=(A).degree) obs.chart (2^dep) (dep+2) obs.memory

open DescentPackedResetRotorRoles DescentResetGates DescentPackedFallbackTree.Image
variable {p tokenBits : ℕ} (record : B.Recorded p)
local notation "vAt" root:arg => B.frame.host.symm (root).val.1
local notation "hiAt" root:arg => (Z).rootBlock T (.inl root)
local notation "count₀" => DescentRotorWindowArchive.count (A).degree L (A).cap

include record in
/-- At the actual base's attained old host and block, the published signed window
recovers the rotor's true symbolic operation at every occupied layer and batch. -/
theorem recorded_rotation_word (elapsed : 0< i) (sorted : SourceSorted W input.order)
    (wide : max (max r Y) (2^r)<2^field) (nWide : (Z).n<field)
    (side : Bool) (g' : (Z).placement.Good) (gate : Fin Y) (m stop : ℕ)
    (primitive : CanonicalTag Y→Cell tokenBits) (x : Fin (count₀+1)→Cell field)
    (reads : ∀j,x (Fin.castSucc (ix j))=RootSources.paddedRow obs.stencil next obs.marks
      (fun u j=>((rank) u j).val)
      (fun _=>Receiver.matrixBefore B.frame.basis short) paid (host (vAt g')) (hiAt g') (ix j))
    (capRead : (x (Fin.last count₀)).val=(A).cap)
    (layer : Fin ((Z).circuit side g').layers) (batch : Fin m) (stopAt : layer.val*m+batch.val<stop) :
    digit tokenBits (layer.val*m+batch.val) (DescentIssuedRotorRoles.issue
      (D:=(A).degree) («L»:=L) (cap:=(A).cap) (Z).n r (Z).width f m stop
      (DescentRecordedRotorLayers.width f (A).cap) primitive side ((Z).goodLabel T g').val gate x).val=
        (primitive (.inl (((Z).circuit side g').rotation layer,gate))).val:=by
  have original:=snapshot_matrix B obs (vAt g') (hiAt g') (fun j=>x (Fin.castSucc (ix j))) reads
  have prior:=DescentRecordedRotorLayers.from_prior_cap B record side g' (A).cap rfl
  have rows:=Recorded.old_roster (reset:=B)
  rw [PackedFlow.mutual_near (A)] at rows
  have donor:=GroupStage.scheduledDonorOrder (S:=S) (A) ctl.base ctl.radix input.vertex
    input.valid.coordinates (input.siteName elapsed)
  rcases input with @⟨V,vFin,vDec,phase,ready,rfl,rfl,history,degree,oldOrder,compact,edgeOrder,siteOrder⟩
  rcases B with ⟨ct,rfl,fit₀,order,eq_,Z₀,T₀,age,date,extent,tickets,unit,dimension,tape,board,
    frame,listed,raw,geometry,hubs,valid,grain,wire,atoms,branch,capacity⟩
  subst order
  let digits:=S.resetInputDigits ctl.base ctl.radix i
  let groups:=Fin.valEmbedding (n:=S.groupCount i)
  let large:=compact.trans (Fin.castLEEmb ready.host)
  exact GroupStage.installed_rotor_role phase S ready digits oldOrder Z₀ T₀ frame groups large obs.word
    (ranks obs.chart (2^(GroupStage.depthBound D n f g)) (GroupStage.depthBound D n f g+2) obs.memory)
    obs.wordFits obs.signedFits obs.onWire f (phase.wire*(phase.z*G.b)*phase.cap) phase.wire (quota S.rounds)
    (phase.resetFlow digits) (phase.resetLoad digits) rows side g' m stop _ primitive gate x
    (fun j=>congrFun original j) capRead prior.1 prior.2 donor sorted tickets wide nWide layer batch stopAt

include record in
/-- The previous matrix has the original calendar width. The physical bank can
use the equal residual-geometry width, with the same actual flat addresses. -/
theorem recorded_rotation_cast {L₀ : ℕ} (width : L₀=L)
    (elapsed : 0< i) (sorted : SourceSorted W input.order)
    (wide : max (max r Y) (2^r)<2^field) (nWide : (Z).n<field)
    (side : Bool) (g' : (Z).placement.Good) (gate : Fin Y) (m stop : ℕ)
    (primitive : CanonicalTag Y→Cell tokenBits)
    (x : Fin (DescentRotorWindowArchive.count (A).degree L₀ (A).cap+1)→Cell field)
    (reads : ∀j,x (Fin.castSucc ((ix j).cast (congrArg
        (fun t=>DescentRotorWindowArchive.count (A).degree t (A).cap) width.symm)))=
      RootSources.paddedRow obs.stencil next obs.marks (fun u j=>((rank) u j).val)
        (fun _=>Receiver.matrixBefore B.frame.basis short) paid (host (vAt g')) (hiAt g') (ix j))
    (capRead : (x (Fin.last _)).val=(A).cap)
    (layer : Fin ((Z).circuit side g').layers) (batch : Fin m) (stopAt : layer.val*m+batch.val<stop) :
    digit tokenBits (layer.val*m+batch.val) (DescentIssuedRotorRoles.issue
      (D:=(A).degree) («L»:=L₀) (cap:=(A).cap) (Z).n r (Z).width f m stop
      (DescentRecordedRotorLayers.width f (A).cap) primitive side ((Z).goodLabel T g').val gate x).val=
        (primitive (.inl (((Z).circuit side g').rotation layer,gate))).val:=by
  subst L₀
  exact recorded_rotation_word B obs record elapsed sorted wide nWide side g' gate m stop primitive x
    reads capRead layer batch stopAt

end
end Hierarchy.DescentSixParty.ClosedReset.Window

end OAI
