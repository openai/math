import OAI.Hierarchy.DescentRetainedOriginalUnit
import OAI.Hierarchy.DescentIssuedSerialCap
import OAI.Hierarchy.DescentScheduledLaneReset

namespace OAI
/-! The actual retained source indexes a bounded-numbered segment in its new trunk. -/
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
local notation "unitAt" host => GrainPorts.Unit A ord C₀ host
local notation "faceAt" host:max u:max => Roster.face A ord C₀ host u
local notation "peerAt" host:max u:max => DescentResetWindowFields.neighbor A ord S B.next.valid names C₀ host (faceAt host u)
local notation "liveAt" host:max u:max => Stage.live A ord S B.next.valid names host (GrainPorts.port A ord C₀ host u)


open DescentResetTrunks
local notation "old" => W.granular B.count (z*G.b) B.fit
local notation "End" => (old).graph.Edge
local notation "land" => fun j:End=>(T).home ((old).graph.dst j)
local notation "rows" => blocks B



theorem incoming_cap (j : End) : earlierIncoming B j<(A).cap:=by
  let link:=trunkParent B (land j)
  let h:=(rows).src link
  have inside:=incoming_before_end B j
  let l : DescentParallelBase.Local (rows) h:=⟨link,Nat.zero_lt_of_lt inside,Or.inl rfl⟩
  exact inside.trans_le (DescentResetWindowFields.count_room A ord S B.next.valid (rows) h l)

theorem carried_index_lt (shape : DescentResetRetainedCableLaw.Shape) (x : shape.Input)
    (z₀ : shape.Donor) (side : Bool) (slot : shape.Slot) (j : End) (pos : 0<shape.units)
    (ticket : side=true→shape.ticket x z₀ slot=earlierIncoming B j) :
    shape.oldIndex x z₀ side slot<shape.units*(A).cap:=by
  have cap:=incoming_cap B j
  have rem:=Nat.mod_lt (shape.header x 3).val pos
  have capBound : (earlierIncoming B j+1)*shape.units≤(A).cap*shape.units:=
    Nat.mul_le_mul_right _ (Nat.succ_le_of_lt cap)
  rw [Nat.add_mul,Nat.one_mul] at capBound
  rw [Nat.mul_comm shape.units]
  cases side with
  | false =>
    simp only [DescentResetRetainedCableLaw.Shape.oldIndex,Bool.false_eq_true,ite_false,Nat.zero_add]
    exact rem.trans_le ((Nat.le_add_left ..).trans capBound)
  | true =>
    simp only [DescentResetRetainedCableLaw.Shape.oldIndex,ite_true,ticket rfl]
    omega

/-- The adjustment added to an already ranked serial is the actual earlier incoming
count on a marked trunk. On outgoing stems and hub erasures the correction is zero. -/
theorem carried_serial_cap (shape : DescentResetRetainedCableLaw.Shape) (x : shape.Input)
    (z₀ : shape.Donor) (side : Bool) (slot : shape.Slot) (j : End) (pos : 0<shape.units)
    (found : shape.found x=some (z₀,side,slot))
    (ticket : side=true→shape.ticket x z₀ slot=earlierIncoming B j) :
    (shape.priceField 2 x).val≤(A).cap:=by
  have cap:=(incoming_cap B j).le
  have rem : (shape.header x 3).val%shape.units<shape.units:=Nat.mod_lt _ pos
  cases side with
  | false => simp [DescentResetRetainedCableLaw.Shape.priceField,DescentResetRetainedCableLaw.Shape.correction,found]
  | true =>
    by_cases hub : (shape.hubCell x).val=1
    · simp [DescentResetRetainedCableLaw.Shape.priceField,DescentResetRetainedCableLaw.Shape.correction,found,hub]
    · have div : (shape.ticket x z₀ slot*shape.units+(shape.header x 3).val%shape.units)/shape.units=
          earlierIncoming B j:=by
        rw [Nat.mul_comm (shape.ticket x z₀ slot),Nat.mul_add_div pos,Nat.div_eq_of_lt rem,Nat.add_zero,ticket rfl]
      simpa [DescentResetRetainedCableLaw.Shape.priceField,DescentResetRetainedCableLaw.Shape.correction,
        found,hub,div] using (Nat.mod_le (earlierIncoming B j) (2^shape.fieldBits)).trans cap

/-- Keep the date's actual outgoing cap and physical grain multiplier in the proof of
bounded reconstruction, including the last valid zero-based chunk. -/
theorem carried_index_room (shape : DescentResetRetainedCableLaw.Shape) (x : shape.Input)
    (z₀ : shape.Donor) (side : Bool) (slot : shape.Slot) (j : End) (date : ℕ)
    (units : shape.units=ResetInput.calendarLanes S G.b date) (gadget : G.b≤2^S.capGain)
    (ticket : side=true→shape.ticket x z₀ slot=earlierIncoming B j)
    (drift namedDegree : ℕ) (field : DescentOperandWidth.s G S k tail drift namedDegree≤ shape.fieldBits) :
    shape.oldIndex x z₀ side slot<2^shape.fieldBits:=by
  have pos : 0<shape.units:=by
    rw [units]
    dsimp only [ResetInput.calendarLanes,DescentCompiler.AtomSchedule.grainAt]
    have positive := G.base_pos
    positivity
  have size:=carried_index_lt B shape x z₀ side slot j pos ticket
  have grain : shape.units≤S.epochPower^S.localGrainExponent:=by
    rw [units]
    exact (S.grain_le_first G.b 1 date G.base_pos).trans (by simpa using S.first_width_payload ctl.height gadget 1)
  have maxCap:=S.local_capacity ctl.height B.age B.next.valid.capacity
  have total : shape.units*(A).cap≤DescentOperandWidth.slices S:=by
    simpa only [DescentOperandWidth.slices,pow_add] using Nat.mul_le_mul grain maxCap
  exact ((DescentOperandWidth.rangeField G S (k:=k) (tail:=tail) (drift:=drift) (degree:=namedDegree)
    (size.le.trans total))).trans_le (Nat.pow_le_pow_right (by decide) field)
end
end Hierarchy.DescentSixParty.ClosedReset.Window


namespace Hierarchy.DescentResetRetainedCableLaw.Shape
open DescentPackedZip DescentSIMDLookup
/-- A retained serial correction uses at most the largest actual incoming ticket. -/
theorem priceField_le_tickets (S : Shape) (x : S.Input) (cap : ℕ)
    (units : 0<S.units) (amount : ∀d j,S.ticket x d j≤cap) :
    (S.priceField 2 x).val≤cap:=by
  cases hit : S.found x with
  | none => simp [priceField,correction,hit]
  | some t =>
    rcases t with ⟨d,side,j⟩
    cases side with
    | false => simp [priceField,correction,hit]
    | true =>
      by_cases mark : (S.hubCell x).val=1
      · simp [priceField,correction,hit,mark]
      · have low:=(Nat.mod_lt (S.header x 3).val units)
        have shift : (S.ticket x d j*S.units+(S.header x 3).val%S.units)/S.units=S.ticket x d j:=by
          rw [Nat.mul_comm (S.ticket x d j),Nat.mul_add_div units,Nat.div_eq_of_lt low,Nat.add_zero]
        simpa [priceField,correction,hit,mark,shift] using
          (Nat.mod_le (S.ticket x d j) (2^S.fieldBits)).trans (amount d j)
end Hierarchy.DescentResetRetainedCableLaw.Shape

end OAI
