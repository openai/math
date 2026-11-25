import OAI.Hierarchy.DescentResetArgumentAtSocket

namespace OAI
/-! An original private rotor edge's issued header at the archived recipe slot. -/
namespace Hierarchy.DescentSixParty.ClosedReset.Window
open DescentKernelHistory DescentBundleHistory DescentLocalArchiveOrder DescentCompiler DescentColonies
open DescentResetTrunks DescentRotor DescentResetGates DescentChosenRouter DescentRouterBank
open DescentResetAttachments DescentNamedContact DescentPrimitivePalette Chronology Computability.BorderVNP.Crossing
open DescentStageEdgeReceipt ThreeFlat.Routing
open scoped Classical
noncomputable section
set_option quotPrecheck false
open scoped Fin.CommRing
variable {F P : Type} [Field F] {d p R : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits}
variable {q ε : ℝ} {S : AtomSchedule} {k i z D wire hist n h C f g cut tail : ℕ} {G : PoweredGadget F}
    {cap : Reached W G q ε S k i z D wire hist} {ctl : ResetRates G S k D n h C f g cut tail}
    (B : ClosedReset cap ctl) (hp : 0<p) (one : 1≤R) (pos : 0<B.reset.unit) (whole : p∣B.reset.unit)
    (wide : max 1 (max B.reset.width (C*B.reset.width))≤R) (a : Archive W) (sh : WorldShape p R a.bit)
local notation "split_" => sh.granular B.count (z*G.b) B.fit hp (B.unit ▸ pos) (B.unit ▸ whole)
local notation "birth" => DescentOrderedReset.grains W B.count B.order
local notation "unit" => B.reset.unit/p
local notation "splitEq" => ((Nat.div_mul_cancel whole).symm : B.reset.unit=unit*p)
local notation "installed" => reentryWorldShape split_ B.reset B.terminals birth _ hp splitEq (resetMenu B) one wide
local notation "after_" => WorldShape.follow hp pos whole B.reblock B.cuts installed
local notation "next_" => (resetArchive B p hp whole a).bit
local notation "coarse" => B.reset.orderedReentry B.terminals birth
local notation "world" => B.reset.orderedOrdinary B.terminals birth
local notation "cnt" => fun e=>(coarse).graph.width e/B.reset.unit
local notation "geo" => B.reset.counts_fit B.terminals
local notation "vertexCode" => B.frame.host.symm.toEmbedding.trans cap.vertex
local notation "dense" => (B.reset.rawHostRank B.terminals vertexCode).trans Fin.valEmbedding
local notation "tape" => B.reset.nativeResetEdges B.terminals vertexCode birth
local notation "rawSite" => B.raw.siteFrom (groupRank (Fin.valEmbedding (n:=S.groupCount (i+1))) dense) B.valid.coordinates
local notation "hop" => DescentPhysicalOrder.rename rawSite
local notation "sparse" => DescentResetLocalOrder.allCode B.raw ((tape).order.trans Fin.valEmbedding) S B.valid rawSite
local notation "edgeName" => DescentPhysicalOrder.rename sparse

open DescentSharedCableNames DescentParallelBase DescentNextSignedWindow DescentOperandStateBanks
local notation "A₁" => B.next.placement
local notation "ord₁" => B.next.order.trans Fin.valEmbedding
local notation "Host" => Stage.Host (Fin (S.groupCount (i+1))) B.next.V k
local notation:max "present" x:arg => (installed).sites ((hop).symm x.1)
local notation:max "result" rank:arg pin:arg args:arg x:arg j:arg => Reached.argumentPointer B.next next_ rank after_ hp pin args x j

open DescentRotorOperandQueryROM DescentDenseHostOrder DescentHostDirectory DescentResetHostSize
open DescentPhysicalSplit DescentBatchedNodeOrder DescentRotor DescentLaneGates DescentCommonHost
open DescentSIMDLookup DescentOperandCandidateLookup DescentDatedAddressBook.ResetOutput
local notation "Z" => B.reset
local notation "A" => B.next.placement
local notation "ord" => B.next.order.trans Fin.valEmbedding
local notation "C₀" => blocks B
theorem registered_rotor_header {H₀ G₀ candidates queryBits : ℕ}
    (cfg : DescentRotorOperandQueryROM.Shape) (host : Host) (face : Roster.Face A ord C₀ host)
    (p₀ : PrivateOccurrence B) (isEdge : face.val.1=privateWire B p₀)
    (mult grain node arg : ℕ) (x : Fin 4→Cell cfg.fieldBits) (side : Bool)
    (key : Code cfg.residual) (v₀ : (DescentCommonPalette.rotor (Z).graph).Site)
    (badge : ↥(DescentDenseHostOrder.roster (Z).graph cfg.residual cfg.depth))
    (lane : DescentRotorOperandQueryROM.Shape.PrivateLane (Z).graph) (within : ℕ)
    (depth : (x 1).val=key.val.1+1) (safe : (x 2).val%2=0)
    (seen : (x 3).val=(localRank (Z).graph cfg.residual cfg.depth badge).val)
    (good : badge.val=.good side ((),key.val.2) v₀)
    (fetch : (cfg.flattened (Z).graph mult (DescentRecordedRotorLayers.layers (Z).n cfg.packet cfg.gain (x 0).val)
      grain node v₀)[arg]?=some (lane,within)) (bound : lane.address<cfg.addresses)
    (owns : (lane.start/grain+within)/unit<(C₀).count face.val.1) (signed coeff : ℕ)
    (digit : Fin 4) (width : max ((A).degree+1) ((A).cap+1)≤2^signed)
    (count : candidates=totalLocal B) (room : 2*candidates<2^queryBits)
    (location : Fin H₀→Fin G₀→Option Host) (q₀ : Fin H₀→Fin G₀→Option (Fin (2*candidates)))
    (rh : Fin H₀) (rg : Fin G₀) (whereAt : location rh rg=some host)
    (issued : (code room (q₀ rh rg)).val=cfg.flatReg (Z).graph mult grain unit node arg 0 x)
    (onWire : (cfg.value (Z).graph (side,lane.face,key,lane.edge,⟨lane.address,bound⟩) (cfg.registers x)).val=
      (Roster.addr A ord C₀ host (localRoster B host) face).val+1)
    (rank : Local next_) (pin : P→ℕ) (arity : ℕ) (y : NodeOrder.All next_)
    (source : Incident (coarse).graph ((hop).symm y.1)) (faceAt : face.val.1=source.val)
    (fits : (lane.start/grain+within+1)*p≤(coarse).graph.width source.val)
    (read : ((present y).keys y.2)[arg]?=some (.inl ⟨.inl source,lane.start/grain+within,fits⟩))
    (endAt : (if face.val.2 then (coarse).graph.dst source.val else (coarse).graph.src source.val)=(hop).symm y.1)
    (small : (result rank pin arity y arg).header digit<2^coeff) :
    ((cfg.flatReg (Z).graph mult grain unit node arg (digit.castLE (by decide : 4≤7)).succ x:ℕ):Cell coeff).val+
      (selected q₀ (fun col h v=>nativeCandidateField signed coeff (digit.castLE (by decide : 4≤7))
        ((location h v).bind (fun peer=>candidateRows B (fieldNames B) peer (col.cast (congrArg (2*·) count))))) rh rg).val=
      (result rank pin arity y arg).header digit :=by
  have actual:=registered_rotor_field B (fieldNames B) cfg host face p₀ isEdge mult grain unit node arg x side
    key v₀ badge lane within depth safe seen good fetch bound owns signed coeff (digit.castLE (by decide : 4≤7))
    width count room location q₀ rh rg whereAt issued onWire
  have declared := private_reference_marked B (fieldNames B) host face p₀ isEdge unit _ owns
  have mark : decide (face.val.1∈(coarse).core)=true :=
    (congrArg (@decide (face.val.1∈(coarse).core)) (Subsingleton.elim _ _)).trans declared
  have ptr:=argument_at_tagged_socket B hp one pos whole wide a sh rank pin arity y arg host face _ true source
    faceAt fits owns read endAt (Or.inl mark)
  let window : Span := ⟨lane.start%grain, lane.stride,
    lane.count (Z).graph cfg mult (DescentRecordedRotorLayers.layers (Z).n cfg.packet cfg.gain (x 0).val) grain⟩
  let f₁ := digit.castLE (by decide : 4≤7)
  have headerEq : (result rank pin arity y arg).fields window f₁=(result rank pin arity y arg).header digit := by
    simp only [Pointer.fields,f₁,Fin.val_castLE,dite_eq_left digit.isLt]
  have sourceEq := (congrArg (fun pointer : Pointer => pointer.fields window f₁) ptr).trans headerEq
  exact (actual (lt_of_eq_of_lt sourceEq small)).trans sourceEq

end
end Hierarchy.DescentSixParty.ClosedReset.Window

end OAI
