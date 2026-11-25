import OAI.Hierarchy.DescentRetainedOriginalLanding
import OAI.Hierarchy.DescentCarriedOriginFields
import OAI.Hierarchy.DescentOldSenderReturn
import OAI.Hierarchy.DescentCalendarRootProfile

namespace OAI
/-! # Original retained node and earlier signed grain at the reached primary terminal -/
namespace Hierarchy.DescentSixParty.ClosedReset.Window
open DescentCompiler DescentColonies DescentSharedCableNames DescentStageEdgeReceipt
open DescentParallelBase DescentResetSignedScan DescentNextSignedWindow DescentCableDonorNames
open scoped Classical BigOperators
noncomputable section
set_option quotPrecheck false
open scoped Fin.CommRing
variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits}
  {G : PoweredGadget F} {q ε : ℝ} {S : AtomSchedule} {k i z D n h C f g cut tail w hist : ℕ}
  {input : Reached W G q ε S k i z D w hist} {ctl : ResetRates G S k D n h C f g cut tail}
  (B : ClosedReset input ctl)
local notation "Z" => B.reset
local notation "T" => B.terminals
local notation "vertexCode" => B.frame.host.symm.toEmbedding.trans input.vertex
local notation "birth" => DescentOrderedReset.grains W B.count B.order
local notation "coarse" => (Z).orderedReentry T birth
local notation "cnt" => fun e=>(coarse).graph.width e/(Z).unit
local notation "world" => (Z).orderedOrdinary T birth
local notation "tape" => (Z).nativeResetEdges T vertexCode birth
local notation "index" => (tape).order.trans Fin.valEmbedding
local notation "dense" => ((Z).rawHostRank T vertexCode).trans Fin.valEmbedding
local notation "nextGroups" => S.groupCount (i+1)
local notation "rawSite" => B.raw.siteFrom (DescentStageEdgeReceipt.groupRank (Fin.valEmbedding (n:=nextGroups)) dense) B.valid.coordinates
local notation "hop" => DescentPhysicalOrder.rename rawSite
local notation "sparse" => DescentResetLocalOrder.allCode B.raw index S B.valid rawSite
local notation "renameEdge" => DescentPhysicalOrder.rename sparse
local notation "next" => B.reblock.result
local notation "A" => B.next.placement
local notation "ord" => B.next.order.trans Fin.valEmbedding
local notation "stream'" => Stage.stream A ord
local notation "board" => Stage.source A ord
local notation "wt" => weight B
local notation "grains" => emit B
local notation "piece'" => piece B
local notation "base'" => first B


open scoped BigOperators
open DescentNextSignedWindow
local notation "C₀" => blocks B
local notation "Host" => Stage.Host (Fin (S.groupCount (i+1))) B.next.V k
local notation "live" => fun e : (coarse).graph.Edge=>e∈(coarse).core
local notation "fit" => Stage.measured A ord S B.next.valid
variable (names : Stage.Host (Fin (S.groupCount (i+1))) B.next.V k ↪ ℕ)

open DescentNextSignedWindow.Native
open DescentDatedAddressBook.ResetOutput DescentSIMDLookup DescentOperandStateBanks
open DescentResetOperandComponents DescentResetOperandSlices
set_option quotPrecheck false
local notation "unitAt" host => GrainPorts.Unit A ord C₀ host
local notation "faceAt" host:max u:max => Roster.face A ord C₀ host u
local notation "peerAt" host:max u:max => DescentResetWindowFields.neighbor A ord S B.next.valid names C₀ host (faceAt host u)
local notation "liveAt" host:max u:max => Stage.live A ord S B.next.valid names host (GrainPorts.port A ord C₀ host u)


open DescentIssuedFallbackPanel DescentOperandCandidateLookup
local notation "old" => W.granular B.count (z*G.b) B.fit
local notation "before" => input.order.trans Fin.valEmbedding
local notation "digitsIn" => S.resetInputDigits ctl.base ctl.radix i
local notation "addr" j => localAddress (c:=(T).commonDepth) input.placement before S input.valid digitsIn B.frame.basis false (beforeStem B j)


local notation "oldHost" side:max edge:max => (blocks B).src (carriedParent B side edge)
local notation "actual" side:max edge:max => carriedUnit B side edge
local notation "land" edge => (T).home ((old).graph.dst edge)


open DescentOperandPriorIncidence DescentKernelHistory DescentResetTrunks DescentResetAttachments
local notation "prior" => input.placement
local notation "J₀" => Fin (S.groupCount i)
local notation "L" => 2^(S.groupWidth k tail i+k-(T).commonDepth)
local notation "End" => (old).graph.Edge
local notation "rawEnd" e:max j:max => (⟨(e).val,j⟩:Stage.Grain (prior))
local notation "hOld" v:max => Stage.home (prior) v
local notation "tag" v:max e:max => originFace v e
local notation "atSlot" v:max e:max j:max => Stage.signed (prior) before S input.valid (hOld v).1 (hOld v).2 (originPort (prior) v e j)
local notation "sub" v:max => subcell (c:=(T).commonDepth) digitsIn B.frame.basis (hOld v)
local notation "same" => funext (fun e=>((Z).allWidths e).symm)
local notation "wires" => installedWireNames (old) (T).home (Z).placement.input (T).hub same (Z).bank (Z).tables

open DescentPacking.PackedMatch.Local.Stage
open DescentCommonHost DescentGL DescentPlainTerminal DescentOldSenderReturn DescentResetOppositePayload
open DescentOperandPriorIncidence DescentSIMDLookup
local notation "lowFits" => B.frame.enough.trans (Nat.sub_le ..)
local notation "primary" v:max => Stage.home A (hop ((Z).oldOwner T v))
local notation "chart" v:max => receiverRoot B (primary v)
local notation "whole" v:max => rearrange B.frame.basis (oldBlock digitsIn (hOld v))

/-- The new primary records the earlier vertex at the actually selected
high column. Inverting the chosen GL remap returns the old full group and block. -/
theorem old_primary_root (v : W.graph.Site) :
    chart v=(B.frame.host ((prior).pos v).2,high lowFits (whole v)):=by
  have parentEq : (Z).resetNames T ((Z).oldOwner T v)=.inl (false,(T).home v):=
    Equiv.apply_symm_apply _ _
  erw [named_home B ((Z).oldOwner T v),receiverRoot_site B ((Z).oldOwner T v)]
  apply Prod.ext
  · have decoded := congrArg (rawName (Z).placement (Z).graph (T).commonDepth (T).code
        (Z).positive (Z).pay (Z).circuit d) parentEq
    exact (congrArg (DescentDenseHostOrder.position (Z).graph) decoded).trans (B.frame.homeHost v)
  · apply Fin.ext
    change rawCoordinate (Z).placement (Z).graph (T).commonDepth (T).code
      (Z).positive (Z).pay (Z).circuit d ((Z).resetNames T ((Z).oldOwner T v)) = _
    rw [parentEq]
    exact B.frame.homeHigh v

theorem old_primary_donor (v : W.graph.Site) :
    donor digitsIn B.frame.basis lowFits (B.frame.host.symm (chart v).1) (chart v).2 (sub v)=hOld v:=by
  rw [old_primary_root,Equiv.symm_apply_apply]
  exact donor_locates digitsIn B.frame.basis lowFits _ _ _ rfl rfl

/-- The all-slot old window readback specializes at the exact compacted new
primary and the unpermuted donor of the chosen old operand. -/
theorem old_primary_signed {HP KP : ℕ} (hosts : input.V↪Fin HP) (groups : J₀↪Fin KP)
    (v : W.graph.Site) (slot : Fin (2*(prior).cap)) (b : ℕ) :
    DescentOldSenderReturn.previousSigned (b:=b) (prior) before S input.valid groups hosts digitsIn
      B.frame.basis lowFits (sub v) slot (hosts (B.frame.host.symm (chart v).1)) (chart v).2 =
    widened (prior).degree (prior).cap b (Stage.signedPanel (prior) before S input.valid
      (cableNames k (groupRank (groups.trans Fin.valEmbedding) (hosts.trans Fin.valEmbedding))) (hOld v) slot):=by
  rw [DescentOldSenderReturn.previous_signed_at,old_primary_donor]


open DescentPaidResidentCount.Reset
local notation "oldHostName" => input.vertex.trans (Fin.castLEEmb input.valid.host)
local notation "oldWireNames" => cableNames k (groupRank (Fin.valEmbedding (n:=S.groupCount i)) ((oldHostName).trans Fin.valEmbedding))
local notation "loCast" => congrArg (fun u=>2^(u-(T).commonDepth)) B.keyWidth
/-- The original rank packet already physically contains all signed candidate slots,
including its one actual incoming or outgoing slot at a retained old site. -/
theorem original_cable_at_primary {field : ℕ} (xs : OriginalArrays B input.valid.host field)
    (v : W.graph.Site) (slot : Fin (2*(prior).cap)) :
    originalCable B xs ((oldHostName) (B.frame.host.symm (chart v).1)) (chart v).2 ((sub v).cast (loCast).symm) slot=
      Stage.signedPanel (prior) before S input.valid oldWireNames (hOld v) slot:=by
  unfold originalCable
  simp only [Fin.cast_cast,Fin.cast_refl]
  rw [xs.markRead]
  erw [old_primary_donor B v]
  rw [B.order_eq]

end
end Hierarchy.DescentSixParty.ClosedReset.Window

end OAI
