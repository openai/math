import OAI.Hierarchy.DescentRegisteredSocketKeys
import OAI.Hierarchy.DescentResetOriginalOperandSite
import OAI.Hierarchy.DescentMeasuredRelayLookup

namespace OAI
/-! # The issued lookup and signed candidate recover the archived relay argument -/
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

local notation "before_" => BitDescription.granular W B.count (z*G.b) B.fit a.bit
local notation "pre_" => (before_).batchedReset B.reset B.terminals birth unit p hp splitEq (resetMenu B)
local notation:max "middle_" x:arg => NodeOrder.followNames B.reblock pre_ x
open DescentSIMDLookup DescentOperandCandidateLookup DescentDatedAddressBook.ResetOutput DescentResetOperandComponents
local notation:max "pubCfg" b:arg q:arg l:arg bat:arg nd:arg ar:arg gr:arg => publicOperandConfig B b q l bat unit nd ar gr
open DescentResetFreshWires
local notation "old_" => W.granular B.count (z*G.b) B.fit
local notation:max "land_" e:arg => B.terminals.home ((old_).graph.dst e)
local notation:max "relayEdge" e:arg a:arg => if a<unit then trunkParent B (land_ e) else stemParent B (true,e)
local notation:max "relayWord" e:arg a:arg => if a<unit then earlierIncoming B e*unit+a else a-unit


open DescentHostDirectory DescentDenseHostOrder DescentPacking.PackedMatch.Local
open DescentFallbackItemSelect DescentResetLocalRoster
local notation:max "host_" e:arg => (blocks B).dst (trunkParent B (land_ e))
local notation:max "cfg_" b:arg q:arg lanes:arg nodes:arg args:arg gr:arg => publicOperandConfig B b q lanes unit unit nodes args gr
local notation:max "short_" e:arg => DescentRelativeContacts.shortName B.terminals.commonDepth (B.terminals.code (land_ e))
local notation "rr" => B.reset.k-B.terminals.commonDepth
local notation "height" => GroupStage.depthBound D n f g

theorem relay_argument_header {b query lanes nodes «arguments» grain H₀ G₀ candidates coeff signed : ℕ}
    (earlier : Local a.bit) (pin : P→ℕ) (arity : ℕ)
    (y : NodeOrder.All next_) (e : (old_).graph.Edge) (birthAt : resetOrigin B hp whole a y=.inr (.inl e))
    (arg : Fin «arguments») (node : Fin nodes) (row : (cfg_ b query lanes nodes «arguments» grain).Data B.reset.n)
    (width : max ((A₁).degree+1) ((A₁).cap+1)≤2^signed) (card : candidates=totalLocal B)
    (room : 2*candidates<2^query) (location : Fin H₀→Fin G₀→Option Host)
    (q₀ : Fin H₀→Fin G₀→Option (Fin (2*candidates))) (rh : Fin H₀) (rg : Fin G₀)
    (siteAt : location rh rg=some (host_ e)) (f₀ : Fin 4) :
    let cfg:=cfg_ b query lanes nodes «arguments» grain
    let old:=cfg.oldConfig
    let input:=cfg.basic row
    let request:=finProdFinEquiv (arg,node)
    let f₁:=f₀.castLE (by decide : 4≤7)
    let rank:=DescentLocalArchiveOrder.reset B p hp whole a earlier
    arg.val<(DescentRetainedRangeDigits.occurrences ((after_).sites y.1) y.2).length →
    node.val=(rank y.1 y.2).val →
    (old.header input 0).val≠0 →
    (old.header input 1).val=cap.placement.cap →
    (∃shape : ↥(DescentDenseHostOrder.roster B.reset.graph rr height),
      (old.header input 2).val=(localRank B.reset.graph rr height shape).val ∧ shape.val=.trunk true ((),(short_ e).2)) →
    (∃j : Fin old.count,j.val=(incomingIndex B e).val ∧
      select (old.relayItems input) (old.relayRows input (short_ e).2) (earlierIncoming B e)=some j) →
    code room (q₀ rh rg)=cfg.column B.reset.graph query none request row →
    (result rank pin arity y arg.val).header f₀<2^coeff →
    (cfg.column B.reset.graph coeff (some f₁) request row).val+
      (selected q₀ (fun col h v=>nativeCandidateField signed coeff f₁ ((location h v).bind (fun peer=>
        candidateRows B (fieldNames B) peer (col.cast (congrArg (2*·) card))))) rh rg).val=
      (result rank pin arity y arg.val).header f₀ :=by
  intro cfg old input request f₁ rank valid located active oldCap shape selectedRow issued small
  obtain ⟨raw,rawAt,kind⟩:=shape
  obtain ⟨j,jLocation,hit⟩:=selectedRow
  have enough : arg.val<2*unit:=by
    rw [←relay_slot_count B hp one pos whole wide a sh y e birthAt]
    exact valid
  let ij : Fin (2*unit):=⟨arg.val,enough⟩
  have ordinal : node.val=earlierIncoming B e:=located.trans (relay_node_number B hp whole a earlier y e birthAt)
  obtain ⟨number,socket,edge,side,mixed⟩:=reached_relay_request (batches:=unit) B e ij row raw active rawAt kind
    oldCap rfl j jLocation hit
  have read:=relay_flat_key B hp one pos whole wide a sh y e birthAt ij
  rw [←edge] at read
  have home : (if socket.face.val.2 then (coarse).graph.dst socket.face.val.1 else (coarse).graph.src socket.face.val.1)=(hop).symm y.1:=by
    rw [side,edge]
    by_cases low : ij.val<unit
    · simp only [low, decide_true, ite_true]
      exact (relay_original_site B hp whole a y e birthAt).symm
    · simp only [low, decide_false, ite_false]
      exact (relay_original_stem B hp whole a y e birthAt).symm
  exact PublicSocket.keyed_header B hp one pos whole wide a sh socket arg node row width card room location q₀ rh rg
    siteAt rank pin arity y arg.val read home f₀ issued (by rw [ordinal];exact mixed) small

end
end Hierarchy.DescentSixParty.ClosedReset.Window

end OAI
