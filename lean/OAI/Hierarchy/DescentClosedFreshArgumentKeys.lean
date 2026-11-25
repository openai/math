import OAI.Hierarchy.DescentInstalledFreshArgument
import OAI.Hierarchy.DescentRetainedRelayFee

namespace OAI
/-! # A dated fresh reset node reads its own original ordered relay or selected router socket -/
namespace Hierarchy.DescentSixParty.ClosedReset.Window
open DescentKernelHistory DescentBundleHistory DescentLocalArchiveOrder DescentCompiler DescentColonies
open DescentResetTrunks DescentRotor DescentResetGates DescentChosenRouter DescentRouterBank
open DescentResetAttachments DescentNamedContact DescentPrimitivePalette Chronology Computability.BorderVNP.Crossing
open DescentStageEdgeReceipt ThreeFlat.Routing
open scoped Classical
noncomputable section
set_option quotPrecheck false
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



open DescentResetFreshWires DescentResetLocalNodes DescentOrderedWords
local notation "raw_" => W.granular B.count (z*G.b) B.fit
local notation "before_" => BitDescription.granular W B.count (z*G.b) B.fit a.bit
local notation "pre_" => (before_).batchedReset B.reset B.terminals birth unit p hp splitEq (resetMenu B)
local notation "middle_" x:arg => NodeOrder.followNames B.reblock pre_ x
local notation "where_" x:arg => resetOrigin B hp whole a x
local notation "dev_" => B.reset.laneShape birth unit p hp splitEq
local notation "loc_" => (fun e : (raw_).graph.Edge => B.terminals.home ((raw_).graph.dst e))

theorem relay_node_number (earlier : Local a.bit) (x : NodeOrder.All next_) (e : (raw_).graph.Edge)
    (origin : where_ x=.inr (.inl e)) :
    ((DescentLocalArchiveOrder.reset B p hp whole a earlier) x.1 x.2).val=earlierIncoming B e :=by
  rw [reached_node_rank,origin]
  change (DescentRosterOrder.compact (relayKey (raw_).graph B.terminals.home birth (loc_ e)) ⟨e,rfl⟩).val=_
  rw [DescentRosterOrder.compact_read]
  unfold earlierIncoming
  apply Finset.card_bij (fun j _=>j.val)
  · intro j old
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,j.property,(Finset.mem_filter.mp old).2⟩
  · intro j _ k _ eqn
    exact Subtype.ext eqn
  · intro j member
    obtain ⟨_,atSite,older⟩:=Finset.mem_filter.mp member
    exact ⟨⟨j,atSite⟩,Finset.mem_filter.mpr ⟨Finset.mem_univ _,older⟩,rfl⟩

/-- In the first half the p-word is at the measured prefix of incoming grains.
The second half is the matching old stem at its unchanged p-offset. -/
theorem relay_installed_word (x : NodeOrder.All next_) (e : (raw_).graph.Edge)
    (origin : where_ x=.inr (.inl e)) (face : Fin 2) (j : Fin unit) :
    let edge:=if face.val=0 then trunkParent B (loc_ e) else stemParent B (true,e)
    let word:=(if face.val=0 then earlierIncoming B e*unit else 0)+j.val
    keyCable installed (middle_ x) (finProdFinEquiv (face,j)).val=some (edge,word) :=by
  let eWidth : (raw_).graph.width e=B.reset.unit:=B.reset.allWidths e
  let d:=j.cast (congrArg (·/p) eWidth.symm)
  let t:=loc_ e
  let bits₀:=DescentRetainedCableBlock.incomingPrefix (W:=raw_) B.terminals.home birth e
  have rowAt : keyCable installed (middle_ x) (finProdFinEquiv (face,d)).val=
      some ((motherNames B).symm (if face.val=0 then .inr (.inl t) else .inl (true,e)),
        (if face.val=0 then bits₀/p else 0)+d.val) :=by
    unfold reentryWorldShape
    apply installed_relay (origin:=origin)
  have sameIndex : (finProdFinEquiv (face,d)).val=(finProdFinEquiv (face,j)).val:=by
    simp only [d,finProdFinEquiv_apply_val,Fin.val_cast,eWidth]
  have alive : 0<weight B (stemParent B (true,e)):=by
    change 0<(blocks B).count (stemParent B (true,e))
    rw [stem_one]
    decide
  have step : DescentRetainedCableBlock.incomingPrefix (W:=raw_) B.terminals.home birth e/p=earlierIncoming B e*unit :=
    (incoming_chunks B e alive p unit hp splitEq).trans (congrArg (·*unit) (incoming_sourceTicket B e alive))
  change bits₀/p=earlierIncoming B e*unit at step
  rw [sameIndex,step] at rowAt
  by_cases side : face.val=0 <;> simpa only [side,ite_true,ite_false,stemParent,trunkParent,d,Fin.val_cast,t] using rowAt

theorem device_installed_wire (x : NodeOrder.All next_) (v : B.reset.bank.Site)
    (u : (B.reset.laneRecipe birth unit p hp splitEq v).Node) (origin : where_ x=.inr (.inr ⟨v,u⟩))
    (slot word : ℕ) (wire₀ : Incident B.reset.bank v) (fit : (word+1)*p≤B.reset.bank.width wire₀.val)
    (read : ((dev_ v).keys u)[slot]?=some (.inl ⟨.inl wire₀,word,fit⟩)) :
    keyCable installed (middle_ x) slot=some ((motherNames B).symm (.inr (.inr wire₀.val)),word) :=by
  unfold reentryWorldShape
  apply installed_device_wire (origin:=origin) (read:=read)

theorem device_installed_socket (x : NodeOrder.All next_) (v : B.reset.bank.Site)
    (u : (B.reset.laneRecipe birth unit p hp splitEq v).Node) (origin : where_ x=.inr (.inr ⟨v,u⟩))
    (slot word : ℕ) (socket : Attached B.reset.bank v)
    (fit : (word+1)*p≤boundaryWidth B.reset.bank v (.inr socket))
    (read : ((dev_ v).keys u)[slot]?=some (.inl ⟨.inr socket,word,fit⟩)) :
    let order:=DescentOrderedReset.fibreKey birth (B.reset.placement.input socket.val.1) socket.val.2
    let w₀:=fun _ : Fibre (B.reset.placement.input socket.val.1) socket.val.2=>B.reset.unit
    let ref : BlockRef p (boundaryWidth B.reset.bank v):=⟨.inr socket,word,fit⟩
    let picked:=(DescentOrderedWords.address order w₀).symm (ref.atBit ⟨0,hp⟩).2
    keyCable installed (middle_ x) slot=some (stemParent B (socket.val.1,picked.1.val),picked.2.val/p) :=by
  unfold reentryWorldShape
  apply installed_device_socket (origin:=origin) (read:=read)

end
end Hierarchy.DescentSixParty.ClosedReset.Window

end OAI
