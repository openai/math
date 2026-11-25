import OAI.Hierarchy.DescentCalendarLiveOperand
import OAI.Hierarchy.DescentRetainedFoundGrain
import OAI.Hierarchy.DescentRetainedRelayFee
import OAI.Hierarchy.DescentResetTrunkMeta

namespace OAI
/-! # The paid stem or trunk unit belonging to a genuine retained original grain -/
namespace Hierarchy.DescentSixParty.ClosedReset.Window
open DescentCompiler DescentColonies DescentSharedCableNames DescentStageEdgeReceipt
open DescentParallelBase DescentResetSignedScan DescentNextSignedWindow DescentCableDonorNames
open scoped Classical BigOperators
noncomputable section
set_option quotPrecheck false
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
local notation "groups" => S.groupCount (i+1)
local notation "rawSite" => B.raw.siteFrom (DescentStageEdgeReceipt.groupRank (Fin.valEmbedding (n:=groups)) dense) B.valid.coordinates
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
local notation "unitAt" host:arg => GrainPorts.Unit A ord C₀ host
local notation "faceAt" host:arg u:arg => Roster.face A ord C₀ host u
local notation "peerAt" host:arg u:arg => DescentResetWindowFields.neighbor A ord S B.next.valid names C₀ host (faceAt host u)
local notation "liveAt" host:arg u:arg => Stage.live A ord S B.next.valid names host (GrainPorts.port A ord C₀ host u)


open DescentResetTrunks
local notation "old" => W.granular B.count (z*G.b) B.fit
local notation "End" => (old).graph.Edge
local notation "land" => fun j:End=>(T).home ((old).graph.dst j)
local notation "rows" => blocks B

theorem incoming_before_end (j : End) : earlierIncoming B j<(rows).count (trunkParent B (land j)):=by
  have un : 0<(Z).unit:=by rw [B.unit,←B.next.grain];exact Nat.mul_pos B.next.placement.unitPos G.base_pos
  have width:=congrArg RawFields.width ((Z).trunkFields T (land j))
  change (coarse).graph.width (trunkParent B (land j))=Fintype.card {x:End // land x=land j}*(Z).unit at width
  change _<weight B _
  rw [weight_quotient,width,Nat.mul_div_cancel _ un,Fintype.card_subtype]
  unfold earlierIncoming
  apply Finset.card_lt_card
  apply (Finset.ssubset_iff_of_subset ?_).2
  · exact ⟨j,by simp,by simp⟩
  · intro t ht
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Finset.mem_filter.mp ht).2.1⟩

def carriedParent (side : Bool) (j : End) : (coarse).graph.Edge:=
  if side then trunkParent B (land j) else stemParent B (false,j)

def carriedUnit (side : Bool) (j : End) : unitAt ((rows).src (carriedParent B side j)):=
  ⟨(⟨carriedParent B side j,⟨if side then earlierIncoming B j else 0,by
    cases side
    · simp only [carriedParent,Bool.false_eq_true,ite_false,stem_one B];decide
    · exact incoming_before_end B j⟩⟩,false),rfl⟩

theorem carried_face (s : Bool) (j : End) :
    (Roster.face A ord (rows) _ (carriedUnit B s j)).val=(carriedParent B s j,false):=rfl

/-- The previous chunk inside one paid grain remains inside the outgoing
stem. On an incoming old edge the measured earlier incoming count is the
quotient in the genuine new trunk. -/
theorem carried_unit_read (shape : DescentResetRetainedCableLaw.Shape) (x : shape.Input)
    (z₀ : shape.Donor) (s : Bool) (slot : shape.Slot) (j : End)
    (pos : 0<shape.units)
    (ticket : s=true→shape.ticket x z₀ slot=earlierIncoming B j)
    (hub : s=true→decide ((shape.hubCell x).val=1)=(T).hub (land j)) :
    let u:=carriedUnit B s j
    let raw:=shape.oldIndex x z₀ s slot
    raw/shape.units=u.val.1.2.val ∧
      (marked (if s then .trunk else .stem) (decide ((shape.hubCell x).val=1))=
        (grainRecord B names _ u).marked ∨ raw<shape.units):=by
  intro u raw
  have tail:=(Nat.mod_lt (shape.header x 3).val pos)
  cases s
  · constructor
    · change shape.oldIndex x z₀ false slot / shape.units = 0
      simp [DescentResetRetainedCableLaw.Shape.oldIndex,Nat.div_eq_of_lt tail]
    · exact Or.inr (by simpa [raw,DescentResetRetainedCableLaw.Shape.oldIndex] using tail)
  · have shift:shape.oldIndex x z₀ true slot=earlierIncoming B j*shape.units+(shape.header x 3).val%shape.units:=by
      simp [DescentResetRetainedCableLaw.Shape.oldIndex,ticket rfl]
    constructor
    · change shape.oldIndex x z₀ true slot/shape.units=earlierIncoming B j
      rw [shift,Nat.mul_comm (earlierIncoming B j),Nat.mul_add_div pos,Nat.div_eq_of_lt tail,Nat.add_zero]
    · left
      have badge:=congrArg RawFields.core ((Z).trunkFields T (land j))
      change decide (trunkParent B (land j)∈(coarse).core)=(!((T).hub (land j))) at badge
      have markedTrunk := (congrArg Bool.not (hub rfl)).trans badge.symm
      exact markedTrunk.trans (@Bool.decide_congr _ _ inferInstance (Classical.propDecidable _) Iff.rfl)

end
end Hierarchy.DescentSixParty.ClosedReset.Window

end OAI
