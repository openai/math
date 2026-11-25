import OAI.Hierarchy.DescentResetWindowResidentSources
import OAI.Hierarchy.DescentResetWindowTicket

namespace OAI
/-! # A four-source bounded comparison for the post-reset signed scan -/
namespace Hierarchy.DescentSixParty.ClosedReset.Window
open Computability.BorderVNP.Crossing DescentCompiler DescentColonies DescentPhysicalOrder DescentPacking
open DescentSharedCableNames DescentSharedCableNames.Siblings DescentParallelBase
open DescentStageEdgeReceipt DescentCableUnbundling
open scoped Classical BigOperators
noncomputable section
variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits}
  {G : PoweredGadget F} {q ε : ℝ} {S : AtomSchedule} {k i z D n h C f g cut tail w hist : ℕ}
  {input : Reached W G q ε S k i z D w hist} {ctl : ResetRates G S k D n h C f g cut tail}
  (B : ClosedReset input ctl)
set_option quotPrecheck false
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

/-- Each real receiver compresses the source key in its own at-most-four-item
roster. The source's within-cell handle is the true raw chronological ticket. -/
def priority (h₀ : Host) (x : Local C₀ h₀) : Fin (((A).degree+1)*B.raw.cap) :=
  finProdFinEquiv (sourceClass B h₀ x,sourceTicket B x.val x.property.1)

theorem priority_val (h₀ : Host) (x : Local C₀ h₀) :
    (priority B h₀ x).val=(sourceClass B h₀ x).val*B.raw.cap+(sourceTicket B x.val x.property.1).val := by
  simp only [priority,finProdFinEquiv_apply_val]
  ring

theorem priority_lt (h₀ : Host) (x y : Local C₀ h₀) :
    priority B h₀ x<priority B h₀ y ↔ (C₀).first x.val<(C₀).first y.val := by
  rw [Fin.lt_def,priority_val,priority_val,DescentCableDonorNames.digit_lt
    (sourceTicket B x.val x.property.1).isLt (sourceTicket B y.val y.property.1).isLt]
  change sourceClass B h₀ x<sourceClass B h₀ y ∨
    (sourceClass B h₀ x).val=(sourceClass B h₀ y).val ∧
      sourceTicket B x.val x.property.1<sourceTicket B y.val y.property.1 ↔ _
  rw [sourceClass_lt,←Fin.ext_iff,sourceClass_eq]
  exact (earlier_tickets B x.val y.val x.property.1 y.property.1).symm

theorem priority_room (h₀ : Host) (x : Local C₀ h₀) : (priority B h₀ x).val<4*(2^g*input.placement.cap) := by
  apply (priority B h₀ x).isLt.trans_le
  rw [B.next.branch, B.capacity]

/-- The two receivers may have different compressed source classes or handles
for an unrelated row. For a shared pair their precedence is nevertheless
exactly the same published relation. -/
theorem both_priorities (left right : Host) (x y : Local C₀ left) (a b : Local C₀ right)
    (first : x.val=a.val) (second : y.val=b.val) :
    priority B left x<priority B left y ↔ priority B right a<priority B right b := by
  rw [priority_lt,priority_lt,first,second]

end
end Hierarchy.DescentSixParty.ClosedReset.Window

end OAI
