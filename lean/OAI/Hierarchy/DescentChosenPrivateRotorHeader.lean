import OAI.Hierarchy.DescentResetRotorArgumentHeader
import OAI.Hierarchy.DescentActualPrivateRotorFace

namespace OAI
/-! The emitted private operand header at its attained rotor socket. -/
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
variable {H₀ G₀ candidates queryBits lanes span fb priorP : ℕ}
local notation "cfg" => rotorQueryShape B unit span fb queryBits lanes
local notation "height_" => GroupStage.depthBound D n f g
local notation "residual" => (Z).k-(B.terminals).commonDepth
local notation "rotor" => DescentCommonPalette.rotor (Z).graph

/-- The chosen original good rotor issues all four pointer-header fields through
its genuine positive receiver. Only the already installed recipe-key read and
the value and coordinates of the dated query are needed at this interface. -/
theorem private_rotor_header (recorded : B.Recorded priorP)
    (side : Bool) (root : (Z).placement.Good) (site : (rotor).Site) (node arg within : ℕ)
    (lane : DescentRotorOperandQueryROM.Shape.PrivateLane (Z).graph) (x : Fin 4→Cell fb)
    (matched : (x 0).val=cap.placement.cap)
    (depth : (x 1).val=((Z).goodLabel B.terminals root).val.1+1) (safe : (x 2).val%2=0)
    (badge : ↥(DescentDenseHostOrder.roster (Z).graph residual height_))
    (seen : (x 3).val=(localRank (Z).graph residual height_ badge).val)
    (good : badge.val=.good side ((),((Z).goodLabel B.terminals root).val.2) site)
    (fetch : ((cfg).flattened (Z).graph C ((Z).circuit side root).layers p node site)[arg]?=some (lane,within))
    (registered : ((Z).circuit side root).layers*unit≤ span)
    (signed coeff : ℕ) (digit : Fin 4) (width : max ((A).degree+1) ((A).cap+1)≤2^signed)
    (count : candidates=totalLocal B) (room : 2*candidates<2^queryBits)
    (location : Fin H₀→Fin G₀→Option Host) (q₀ : Fin H₀→Fin G₀→Option (Fin (2*candidates)))
    (rh : Fin H₀) (rg : Fin G₀)
    (whereAt : location rh rg=some (Stage.home A (hop ((Z).rotorSiteAt B.terminals side root site))))
    (issued : (code room (q₀ rh rg)).val=(cfg).flatReg (Z).graph C p unit node arg 0 x)
    (rank : Local next_) (pin : P→ℕ) (arity : ℕ) (y : NodeOrder.All next_)
    (siteAt : (hop).symm y.1=(Z).rotorSiteAt B.terminals side root site)
    (entry : ∃(e:Incident (coarse).graph ((hop).symm y.1)) (fit:(lane.start/p+within+1)*p≤(coarse).graph.width e.val),
      e.val=privateWire B (goodOccurrence B side root lane.edge) ∧
      ((present y).keys y.2)[arg]?=some (.inl ⟨.inl e,lane.start/p+within,fit⟩))
    (small : (result rank pin arity y arg).header digit<2^coeff) :
    (((cfg).flatReg (Z).graph C p unit node arg (digit.castLE (by decide : 4≤7)).succ x:ℕ):Cell coeff).val+
      (selected q₀ (fun col h v=>nativeCandidateField signed coeff (digit.castLE (by decide : 4≤7))
        ((location h v).bind (fun peer=>candidateRows B (fieldNames B) peer (col.cast (congrArg (2*·) count))))) rh rg).val=
      (result rank pin arity y arg).header digit:=by
  have room':2*totalLocal B<2^queryBits:=count ▸ room
  obtain ⟨bound,face,faceData,owns,home,value⟩:=
    observed_private_rotor_face B recorded side root site node arg within lane ((cfg).registers x)
      matched ⟨depth,safe⟩ fetch registered room'
  obtain ⟨e,fit,raw,read⟩:=entry
  have edge:=congrArg Prod.fst faceData
  have sign:=congrArg Prod.snd faceData
  change face.val.1=privateWire B (goodOccurrence B side root lane.edge) at edge
  change face.val.2=lane.face at sign
  have levels : ((Z).circuit side root).layers =
      DescentRecordedRotorLayers.layers (Z).n (cfg).packet (cfg).gain (x 0).val :=
    (DescentRecordedRotorLayers.from_prior_cap B recorded side root _ matched).1
  apply registered_rotor_header B hp one pos whole wide a sh (cfg) _ face (goodOccurrence B side root lane.edge)
    edge C p node arg x side ((Z).goodLabel B.terminals root) site badge lane within depth safe seen good
    (by simpa only [←levels] using fetch) bound (by simpa only [edge] using owns) signed coeff digit width count
    room location q₀ rh rg whereAt issued value rank pin arity y e (edge.trans raw.symm) fit read _ small
  rw [sign,raw,home,siteAt]

end
end Hierarchy.DescentSixParty.ClosedReset.Window

end OAI
