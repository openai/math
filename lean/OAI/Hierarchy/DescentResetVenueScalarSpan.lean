import OAI.Hierarchy.DescentDatedResetRangeFields
import OAI.Hierarchy.DescentDatedRolePriorFrames

namespace OAI
/-! # Original scalar span counts at the reset venue checkpoint -/
namespace Hierarchy.DescentDatedAddressBook.PhysicalReset.FinalInputs
open DescentSIMDLookup DescentPackedColony DescentPackedZip DescentOperandCandidateLookup
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
noncomputable section
set_option quotPrecheck false
variable {a : PhysicalReset} {floor w : ℕ} {u : a.DateInputs floor w} (z : u.FinalInputs)
local notation "v" => a.successor
local notation "b" => a.rebased floor
local notation "A" => (v).receiver
local notation "s" => u.operand
local notation "plan" => (v).linkedRankInputs u.sectors ((v).sheetsStart b)
local notation "rendered" => (v).renderFromRanks plan b
local notation "actorBase" => (v).middle.stop b
local notation "head" => a.throughPublishedRoots u.shape floor u.count u.hub u.g u.Y u.roots u.book u.src u.sourceRows u.oldDegree w u.bookFits
local notation "ht" => a.throughPublishedTicks u.shape floor u.count u.hub u.g u.Y u.roots u.book u.sourceRows u.oldDegree w u.bookFits

/-- Every scalar f6 row in the metadata reader still contains the count issued for the
same operand.  Node packing and the venue writers preserve its original address. -/
theorem venue_span (ok : u.Ready) (room : z.Room) {m mid : Memory w}
    (earlier : u.throughOperandDate.Runs m mid) :
    ∃actorMem,((head).seq ((v).actor.actorBody u.actor actorBase w)).Exec m actorMem
        (ht+(v).actor.actorTicks u.actor actorBase w) ∧
      ∀(x : Fin (v).metadata.chart.blocks) (n : Fin (v).metadata.chart.nodes) (j : Fin (s).slots)
        (kept : Fin (A).hosts→Fin (A).groups→Cell (s).coeff),
        Source ((s).kept ((v).operandOrdinal (s) 6 j (x.cast z.metaBlocks) (n.cast z.metaNodes)))
          kept (A).lanes (u.operandEntry ok actorMem) →
        Source (z.spans x n j) kept (A).lanes (z.venueImage mid) := by
  obtain ⟨actorMem,acted,equal⟩:=u.sheets_result ok earlier
  refine ⟨actorMem,acted,?_⟩
  let before:=u.operandEntry ok actorMem
  let words:=(A).hosts*chunks (A).groups (A).lanes
  have widths : (A).fields=(v).nodeNames*(v).nodes:=by
    simpa only [ok.nodes,ok.slots,ResetOutput.nodeNames] using u.operand.channels
  have prior : (v).operandDictionaryEnd b+((v).nodeNames*(v).nodes)*words≤(v).scalarEnd b:=by
    change (v).operandDictionaryEnd b+_≤(v).operandDictionaryEnd b+(A).fields*_
    rw [widths]
  have frame:=DescentResetNodeBooks.any ((v).scalarEnd b) ((v).operandDictionaryEnd b)
    (v).nodeNames (v).nodes (A).hosts (A).groups (v).nodeBits (A).lanes
    ((v).operandMemory (s) rendered b before) prior ok.full
  intro x n j kept old
  let i:=(v).operandOrdinal (s) 6 j (x.cast z.metaBlocks) (n.cast z.metaNodes)
  let page:=DescentResetMetadataInputs.spanBank (v) (s) b (x.cast z.metaBlocks) (n.cast z.metaNodes) j
  have cap : words≤page.size := (Nat.le_succ _).trans (Nat.le_pow_clog (by decide) _)
  apply source_column page _ (room.spans x n j).1 _ kept cap
  intro t
  let addr:=DescentOperandStateBanks.address ((v).operandDictionaryEnd b) words i (row _ _ _ t)
  have below : addr<(v).scalarEnd b := DescentOperandStateBanks.address_lt _ i (row _ _ _ t)
  have zero : (v).previous (s) rendered b i=(fun _=>.lit 0) := by
    funext c
    exact (v).previous_range (s) b rendered (2 : Fin 3) j (x.cast z.metaBlocks) (n.cast z.metaNodes) c
  have small:=((v).final_ge b).trans_lt ok.full
  have rd:=(v).operand_source_at (s) rendered b before ok.fields small i kept (by
    rw [zero]
    exact DescentOperandFieldJoin.stored_blank _ _ before kept (ok.fields.1 _) (ok.fields.2.1 _) old
      le_rfl (((v).operand_order b).2.trans_lt small)) t
  exact (z.venue_prior_frame room mid addr (below.trans_le ((v).final_ge b))).trans
    ((congrFun equal addr).trans ((frame.2 addr (.inl below)).trans rd))

private theorem same_axes {H H₁ G G₁ bits bits₁ M M₁ : ℕ} {e₀ e₁ : Expr} {before after_ : Memory w}
    (hosts : H=H₁) (groups : G=G₁) (coeff : bits=bits₁) (lanes : M=M₁)
    (copy : ∀value : Fin H→Fin G→Cell bits, Source e₀ value M before → Source e₁ value M after_)
    (value : Fin H₁→Fin G₁→Cell bits₁) (read : Source e₀ value M₁ before) :
    Source e₁ value M₁ after_ := by
  subst H₁;subst G₁;subst bits₁;subst M₁
  exact copy value read

/-- The primitive birth decoder reads the very same scalar count with its own
block and node indices.  A named reset gives all four rectangular equalities by reduction. -/
theorem root_span_acquired (ok : u.Ready) (room : z.Room) {m mid : Memory w}
    (earlier : u.throughOperandDate.Runs m mid)
    (hosts : (A).hosts=(v).birth.placement.newHosts) (groups : (A).groups=(v).birth.placement.groups)
    (coeff : (s).coeff=(v).birth.spanBits) (lanes : (A).lanes=(v).birth.placement.lanes) :
    ∃actorMem,((head).seq ((v).actor.actorBody u.actor actorBase w)).Exec m actorMem
        (ht+(v).actor.actorTicks u.actor actorBase w) ∧
      ∀(x : Fin (v).primitive.chart.blocks) (n : Fin (v).primitive.chart.nodes) (j : Fin (v).birth.arguments)
        (value : Fin (v).birth.placement.newHosts→Fin (v).birth.placement.groups→Cell (v).birth.spanBits),
        Source ((s).kept ((v).operandOrdinal (s) 6 (j.cast z.birthArgs)
          (x.cast (z.censusBlocks.trans z.metaBlocks)) (n.cast (z.censusNodes.trans z.metaNodes))))
          value (v).birth.placement.lanes (u.operandEntry ok actorMem) →
        Source (z.spans (x.cast z.censusBlocks) (n.cast z.censusNodes) (j.cast z.birthArgs))
          value (v).birth.placement.lanes (z.venueImage mid) := by
  obtain ⟨actorMem,acted,rows⟩:=z.venue_span ok room earlier
  refine ⟨actorMem,acted,?_⟩
  intro x n j value seen
  exact same_axes hosts groups coeff lanes
    (rows (x.cast z.censusBlocks) (n.cast z.censusNodes) (j.cast z.birthArgs)) value seen

end
end Hierarchy.DescentDatedAddressBook.PhysicalReset.FinalInputs

end OAI
