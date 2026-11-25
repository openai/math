import OAI.Hierarchy.DescentCalendarRelayArgumentHeader
import OAI.Hierarchy.DescentRangePage

namespace OAI
/-! # The three recorded range columns for either leg of an old relay -/
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


open DescentTerminalSliceRuns DescentTerminalCombinedRole DescentRetainedRangeDigits
open DescentResetOperandComponents

theorem relay_range_at (y : NodeOrder.All next_) (e : (old_).graph.Edge)
    (origin : resetOrigin B hp whole a y=.inr (.inl e)) (j : ℕ) (digit : Fin 3) :
    atSlot ((after_).sites y.1) y.2 j digit =
      if j<2*unit then value ⟨0,1,1⟩ digit else 0 :=by
  have rangeLaw:=reset_range_origin B hp whole a sh one pos wide y
  change (after_).nodeFields y=_ at rangeLaw
  rw [origin] at rangeLaw
  change ((after_).sites y.1).sliceFields y.2=relayFields p ((old_).graph.width e) at rangeLaw
  unfold DescentRetainedRangeDigits.atSlot
  rw [←DescentRetainedRangeDigits.layout ((after_).sites y.1) y.2, rangeLaw, B.reset.allWidths e]
  by_cases inside : j<2*unit <;>
    simp [relayFields,repeatFields,List.flatMap_replicate,List.getElem?_replicate,inside]
  <;> split <;> first | rfl | omega

theorem relay_range_digits {b query lanes nodes «arguments» grain : ℕ}
    (priorRank : Local a.bit) (y : NodeOrder.All next_) (e : (old_).graph.Edge)
    (origin : resetOrigin B hp whole a y=.inr (.inl e))
    (arg : Fin «arguments») (node : Fin nodes) (row : (cfg_ b query lanes nodes «arguments» grain).Data B.reset.n)
    (digit : Fin 3) (bits₁ : ℕ) :
    let cfg:=cfg_ b query lanes nodes «arguments» grain
    let old:=cfg.oldConfig
    let input:=cfg.basic row
    node.val=(DescentLocalArchiveOrder.reset B p hp whole a priorRank y.1 y.2).val →
    (old.header input 0).val≠0 →
    (old.header input 1).val=cap.placement.cap →
    (∃shape : ↥(DescentDenseHostOrder.roster B.reset.graph rr height),
      (old.header input 2).val=(localRank B.reset.graph rr height shape).val ∧ shape.val=.trunk true ((),(short_ e).2)) →
    (∃j : Fin old.count,j.val=(incomingIndex B e).val ∧
      select (old.relayItems input) (old.relayRows input (short_ e).2) (earlierIncoming B e)=some j) →
    cfg.column B.reset.graph bits₁ (some (page digit)) (finProdFinEquiv (arg,node)) row=
       (atSlot ((after_).sites y.1) y.2 arg.val digit : Cell bits₁) :=by
  intro cfg old input whereAt live capAt shape chosen
  obtain ⟨raw,seen,kind⟩:=shape
  obtain ⟨j,jAt,yes⟩:=chosen
  have ordinal := whereAt.trans (relay_node_number B hp whole a priorRank y e origin)
  rw [relay_range_at B hp one pos whole wide a sh y e origin]
  by_cases proper : arg.val<2*unit
  · obtain ⟨number,socket,edge,side,hit⟩:=reached_relay_request (batches:=unit) B e
      ⟨arg.val,proper⟩ row raw live seen kind capAt rfl j jAt yes
    rw [←ordinal] at hit
    rw [ite_eq_left proper,public_produced B.reset.graph cfg arg node row _ _ 1 bits₁ _ hit]
    fin_cases digit <;> rfl
  · have missing : cfg.mixed B.reset.graph node.val arg.val row=none:=by
      rw [cfg.mixed_relay B.reset.graph row raw live seen kind]
      have outside : ¬ arg.val < 2*cfg.batches := proper
      simp [DescentFallbackOperandBranch.Config.relay,outside]
    rw [ite_eq_right proper,public_empty B.reset.graph cfg arg node row bits₁ missing]
    rfl

end
end Hierarchy.DescentSixParty.ClosedReset.Window

end OAI
