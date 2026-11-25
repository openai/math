import OAI.Hierarchy.DescentClosedDeviceArgumentKeys
import OAI.Hierarchy.DescentRetainedResetRangeOrigin
import OAI.Hierarchy.DescentRetainedRangeDigits

namespace OAI
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
local notation "loc_" => fun e : (raw_).graph.Edge=>B.terminals.home ((raw_).graph.dst e)

open DescentLaneGates
local notation "prog_" v:arg => B.reset.laneProgram birth unit p hp splitEq v
local notation "words_" v:arg => fun t : Boundary B.reset.bank v=>boundaryWidth B.reset.bank v t/p
local notation "fit_" v:arg => B.reset.laneWidth_eq unit p splitEq v

open DescentTerminalSliceRuns DescentTerminalCombinedRole DescentRetainedRangeDigits

/-- Following the split and the final site renaming preserves the full device
operand list length at its original program node. -/
theorem device_slot_count (x : NodeOrder.All next_) (v : B.reset.bank.Site)
    (u : (prog_ v).Node) (origin : where_ x=.inr (.inr ⟨v,u⟩)) :
    (occurrences ((after_).sites x.1) x.2).length=((dev_ v).keys u).length :=by
  have rowFields:=reset_range_origin B hp whole a sh one pos wide x
  change (after_).nodeFields x=_ at rowFields
  rw [origin] at rowFields
  change ((after_).sites x.1).sliceFields x.2=((dev_ v).sliceFields u) at rowFields
  refine (congrArg List.length (DescentRetainedRangeDigits.layout ((after_).sites x.1) x.2).symm).trans ?_
  refine (congrArg (fun rows : List (List SliceCode) => (repeatFields rows.flatten).length) rowFields).trans ?_
  refine (congrArg List.length (DescentRetainedRangeDigits.layout (dev_ v) u)).trans ?_
  exact DescentRetainedRangeDigits.length (dev_ v) u hp

theorem device_original_key (x : NodeOrder.All next_) (v : B.reset.bank.Site) (u : (prog_ v).Node)
    (origin : where_ x=.inr (.inr ⟨v,u⟩)) (slot : Fin (occurrences ((after_).sites x.1) x.2).length) :
    ∃ (left : List (Lane p (boundaryWidth B.reset.bank v))) (l : Lane p (boundaryWidth B.reset.bank v))
      (right : List (Lane p (boundaryWidth B.reset.bank v))) (i : Fin (l.count (words_ v))),
      List.ofFn ((prog_ v).op u).arg=left++l::right ∧ slot.val=(left.map (fun b=>b.count (words_ v))).sum+i.val ∧
      keyCable installed (middle_ x) slot.val=some (deviceRoute B hp v (laneBlock (words_ v) (fit_ v) hp l i)) :=by
  apply device_word_cases B hp one pos whole wide a sh x v u origin slot.val
  simpa only [device_slot_count B hp one pos whole wide a sh x v u origin] using slot.isLt

theorem relay_slot_count (x : NodeOrder.All next_) (e : (raw_).graph.Edge)
    (origin : where_ x=.inr (.inl e)) :
    (occurrences ((after_).sites x.1) x.2).length=2*unit :=by
  have rowFields:=reset_range_origin B hp whole a sh one pos wide x
  change (after_).nodeFields x=_ at rowFields
  rw [origin] at rowFields
  change ((after_).sites x.1).sliceFields x.2=relayFields p ((raw_).graph.width e) at rowFields
  refine (congrArg List.length (DescentRetainedRangeDigits.layout ((after_).sites x.1) x.2).symm).trans ?_
  refine (congrArg (fun rows : List (List SliceCode) => (repeatFields rows.flatten).length) rowFields).trans ?_
  rw [B.reset.allWidths e]
  simp [relayFields,List.replicate_succ,repeatFields,List.length_flatMap,two_mul]

/-- Every live relay operand lies in exactly one of the two complete equal
words. The cable and offset here are those registered by the old local fibre. -/
theorem relay_original_key (x : NodeOrder.All next_) (e : (raw_).graph.Edge)
    (origin : where_ x=.inr (.inl e)) (slot : Fin (occurrences ((after_).sites x.1) x.2).length) :
    let pair:=finProdFinEquiv.symm (slot.cast (relay_slot_count B hp one pos whole wide a sh x e origin))
    let edge:=if pair.1.val=0 then trunkParent B (loc_ e) else stemParent B (true,e)
    let word:=(if pair.1.val=0 then earlierIncoming B e*unit else 0)+pair.2.val
    keyCable installed (middle_ x) slot.val=some (edge,word) :=by
  intro pair edge word
  have row:=relay_installed_word B hp one pos whole wide a sh x e origin pair.1 pair.2
  have same : (finProdFinEquiv (pair.1,pair.2)).val=slot.val:=by
    simp only [pair,Prod.mk.eta,Equiv.apply_symm_apply]
    rfl
  rw [same] at row
  exact row

end
end Hierarchy.DescentSixParty.ClosedReset.Window

end OAI
