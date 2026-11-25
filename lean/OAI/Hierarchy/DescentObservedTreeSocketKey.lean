import OAI.Hierarchy.DescentCalendarFallbackSocketKey
import OAI.Hierarchy.DescentResetOriginalOperandSite
import OAI.Hierarchy.DescentClosedResetSlotCount

namespace OAI
/-! # Previously observed packet fields and the installed exceptional socket -/
namespace Hierarchy.DescentSixParty.ClosedReset.Window
open DescentCompiler DescentPhysicalOrder DescentStageEdgeReceipt ThreeFlat.Routing
open DescentIssuedFallbackPanel DescentSharedCableNames.Stage DescentGL DescentColonies
open DescentChosenRouter DescentRelativeContacts DescentRouterSlots DescentSharedBookScan
open DescentResetStemCompactOrder DescentPackedTicketChronology DescentPacking DescentStageEdgeReceipt
open DescentFallbackItemSelect DescentNamedContact
open DescentPrimitivePalette DescentLaneGates DescentBundleHistory DescentResetGates DescentResetFreshWires
open DescentResetLocalNodes DescentLocalArchiveOrder DescentKernelHistory DescentTreeLaneProgram DescentContactTree
open Chronology Computability.BorderVNP.Crossing
open scoped Classical BigOperators Fin.CommRing
noncomputable section
set_option quotPrecheck false
set_option maxHeartbeats 1400000
variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits}
  {G : PoweredGadget F} {q ε : ℝ} {S : DescentCompiler.AtomSchedule} {k i z D n h C f g cut tail w hist : ℕ}
  {input : Reached W G q ε S k i z D w hist} {ctl : ResetRates G S k D n h C f g cut tail}
  (B : ClosedReset input ctl)
local notation "A" => input.placement
local notation "Z" => B.reset
local notation "T" => B.terminals
local notation "R" => (Z).placement
local notation "words" => S.resetInputDigits ctl.base ctl.radix i
local notation "m" => S.groupWidth k tail i+k
local notation "c" => (T).commonDepth
local notation "Ht" => GroupStage.depthBound D n f g
local notation "r" => (Z).k-c
local notation "Y" => (2^(Z).n : ℕ)
local notation "native" => input.order.trans Fin.valEmbedding
local notation:max "item" s:arg t:arg => DescentRouterSlots.Item (R).contact (R).owner s (.inr t)
local notation:max "token" t:arg => ((Z).fallLabel T t,((T).code t).2.2)
local notation:max "num" t:arg => ((T).leaves.window (shortName c ((T).code t))).card
local notation:max "who" t:arg => B.frame.host.symm ((T).code t).1
local notation:max "hiAt" t:arg => (Z).rootBlock T (.inr t)
local notation "small" => B.frame.enough.trans (Nat.sub_le ..)
local notation "widthCast" => congrArg (fun l=>2^(l-c)) B.keyWidth
local notation:max "posOld" s:arg e:arg => localAddress A native S input.valid words B.frame.basis («c»:=c) s (beforeStem B e)
local notation:max "row" s:arg e:arg => finProdFinEquiv (((posOld s e).1.cast (widthCast).symm),(posOld s e).2)
variable {H field query lanes nodes args grain p size : ℕ} (hp : 0<p) (one : 1≤ size)
  (positive : 0<B.reset.unit) (whole : p∣B.reset.unit) (wide : max 1 (max B.reset.width (C*B.reset.width))≤ size)
  (a : Archive W) (sh : DescentBundleHistory.WorldShape p size a.bit)
local notation "batches" => (Z).unit/p
local notation "unitFit" => ((Nat.div_mul_cancel whole).symm : (Z).unit=batches*p)
local notation "cfg" => flatConfig B field query lanes batches batches nodes args
variable (grp : Fin (S.groupCount i)↪ℕ) (padded : Fintype.card input.V≤H)
local notation "pad" => input.vertex.trans (Fin.castLEEmb padded)
variable (snap : GroupStage.RootObservation input.placement S input.valid (S.resetInputDigits ctl.base ctl.radix i) (input.order.trans Fin.valEmbedding) grp (input.vertex.trans (Fin.castLEEmb padded)) B.reset B.terminals B.frame field)
local notation "ranks₀" => ranks (a:=r) («Y»:=Y) (D:=(A).degree) snap.chart (2^Ht) (Ht+2) snap.memory


local notation "pub" => publicOperandConfig B field query lanes batches batches nodes args grain
local notation "birth" => DescentOrderedReset.grains W B.count B.order
local notation "split_" => sh.granular B.count (z*G.b) B.fit hp (B.unit ▸ positive) (B.unit ▸ whole)
local notation "installed" => reentryWorldShape split_ (Z) (T) birth _ hp unitFit (resetMenu B) one wide
local notation "old_" => BitDescription.granular W B.count (z*G.b) B.fit a.bit
local notation "pre_" => (old_).batchedReset (Z) (T) birth batches p hp unitFit (resetMenu B)
local notation "installedArchive" => (resetArchive B p hp whole a).bit
local notation:max "ord" earlier:arg => DescentLocalArchiveOrder.reset B p hp whole a earlier
variable (s : Bool) (t : B.reset.Fallback)
local notation "bk" => (R).fallbackBook s t
local notation:max "venue" q:arg => (⟨(s,.inr t),q⟩ : (Z).bank.Site)
local notation:max "gateAt" q:arg => (Z).laneRecipe birth batches p hp unitFit (venue q)
local notation:max "header" x:arg => (cfg).header ((pub).basic x)
local notation:max "here" q:arg => (Z).localShape T ((Z).placed T ((Z).privateSiteAt T s (.inr t) q))

/-- The data in the public lookup row comes from the attained old root panel,
old archive ordering, and the original source group and fine word. -/
structure FallbackRegisters (x : (pub).Data (Z).n) : Prop where
  packet : (cfg).packet ((pub).basic x)=DescentFallbackPeriod.inputs (n:=(Z).n) («r»:=r) (field:=field)
      (fun u hi lo=>snap.stencil u hi (lo.cast widthCast)) snap.peers
      (fun u hi lo=>snap.marks u hi (lo.cast widthCast)) (fun u j=>(ranks₀ u j).val)
      (pad (who t)) (hiAt t)
  hostRead : ((cfg).header ((pub).basic x) 3).val=DescentResetStemWord.hostCode
      (compress (hostDomain A input.vertex (who t)) (input.vertex (who t)).val)
      (decide (who t∉(A).near (who t)))
  groupWord : ∀e : item s t,((cfg).digit ((pub).basic x) (row s e.val) 0).val=
      compress (groupDomain words B.frame.basis small (who t) (hiAt t)) ((A).pos (W.graph.src e.val.1)).1.val
  fineWord : ∀e : item s t,((cfg).digit ((pub).basic x) (row s e.val) 1).val=((A).block (W.graph.src e.val.1)).val
  indexed : ∀u,originalId W.graph.Site u=((A).site input.vertex input.valid.coordinates u).val
  sorted : SourceSorted W input.order

/-- A paid earlier observation and its readings in this original lookup row. -/
def FallbackRows (x : (pub).Data (Z).n) : Prop :=
  ∃ (height : ℕ) (groupId : Fin (S.groupCount i)↪ℕ) (space : Fintype.card input.V≤height)
    (seen : GroupStage.RootObservation A S input.valid words native groupId
      (input.vertex.trans (Fin.castLEEmb space)) (Z) (T) B.frame field),
    FallbackRegisters (p:=p) (query:=query) (lanes:=lanes) (nodes:=nodes) (args:=args) (grain:=grain)
      B groupId space seen s t x

local notation "after_" => WorldShape.follow hp positive whole B.reblock B.cuts installed
local notation "coarse" => B.reset.orderedReentry B.terminals birth
local notation "rank" => B.frame.host.symm.toEmbedding.trans input.vertex
local notation "dense" => (B.reset.rawHostRank B.terminals rank).trans Fin.valEmbedding
local notation "rawSite" => B.raw.siteFrom (groupRank (Fin.valEmbedding (n:=S.groupCount (i+1))) dense) B.valid.coordinates
local notation "hop" => DescentPhysicalOrder.rename rawSite

open DescentRetainedRangeDigits DescentCompiler DescentStageEdgeReceipt

theorem tree_original_receiver (q₀ : Physical.Site (bk).height) (gate : (gateAt q₀).Node)
    (out : NodeOrder.All installedArchive) (origin : resetOrigin B hp whole a out=.inr (.inr ⟨venue q₀,gate⟩)) :
    treeReceiver B (venue q₀)=DescentSharedCableNames.Stage.home B.next.placement out.1 :=by
  have placed:=device_original_site B hp whole a out (venue q₀) gate origin
  apply congrArg (DescentSharedCableNames.Stage.home B.next.placement)
  exact (congrArg (fun v => hop v) placed.symm).trans ((hop).apply_symm_apply out.1)

/-- Every occupied authored tree operand returns the physical original
socket and its precise word, with the signed end at the same current site. -/
theorem tree_observed_socket_key (q₀ : Physical.Site (bk).height) (gate : (gateAt q₀).Node)
    (out : NodeOrder.All installedArchive) (origin : resetOrigin B hp whole a out=.inr (.inr ⟨venue q₀,gate⟩))
    (x : (pub).Data (Z).n)
    (rows : FallbackRows (p:=p) (field:=field) (query:=query) (lanes:=lanes) (nodes:=nodes) (args:=args)
      (grain:=grain) B s t x)
    (active : (header x 0).val≠0) (capRead : (header x 1).val=(A).cap)
    (shapeRead : (header x 2).val=(DescentDenseHostOrder.localRank (Z).graph r Ht (here q₀)).val)
    (slot : Fin nodes) (numbered : slot.val=(Z).nodeIndex birth batches p hp unitFit (venue q₀) gate)
    (arg : Fin args) (bound : arg.val<(occurrences ((after_).sites out.1) out.2).length) :
    ∃number word count mark, ∃socket : PublicSocket B (treeReceiver B (venue q₀)) batches word mark number,
      (pub).mixed (Z).graph slot.val arg.val x=some (number,word,count,mark) ∧
      keyCable installed (NodeOrder.followNames B.reblock pre_ out) arg.val=some (socket.face.val.1,word) ∧
      (if socket.face.val.2 then (coarse).graph.dst socket.face.val.1 else (coarse).graph.src socket.face.val.1)=
        (hop).symm out.1:=by
  obtain ⟨height,groupId,space,seen,known⟩:=rows
  have pair:=fallback_socket_key (field:=field) (query:=query) (lanes:=lanes) (nodes:=nodes)
    (args:=args) (grain:=grain) B hp one positive whole wide a sh groupId space seen s t q₀ gate out origin x
    known.packet known.hostRead known.groupWord known.fineWord known.indexed known.sorted active capRead shapeRead
    slot numbered arg
  obtain ⟨number,word,count,mark,socket,hit,route⟩:=pair.1 (bound.trans_eq
    (device_slot_count B hp one positive whole wide a sh out (venue q₀) gate origin))
  refine ⟨number,word,count,mark,socket,hit,route,?_⟩
  exact (treeReceiver_endpoint B (venue q₀) socket.face).trans
    (device_original_site B hp whole a out (venue q₀) gate origin).symm

end
end Hierarchy.DescentSixParty.ClosedReset.Window

end OAI
