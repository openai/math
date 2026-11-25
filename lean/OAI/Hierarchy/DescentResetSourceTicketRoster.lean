import OAI.Hierarchy.DescentResetSourceTicketObserved
import OAI.Hierarchy.DescentClosedRosterCoverage

namespace OAI
/-! # The genuine five-family raw directory supplies the source-prefix scan -/
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

open DescentNextSignedWindow DescentResetSourceTicketRAM

theorem incident_restart (e f : (coarse).graph.Edge) : atRawSource B e f ↔
    ((blocks B).src f=(blocks B).src e ∨ (blocks B).dst f=(blocks B).src e) := by
  have nodes (u v : (coarse).graph.Site) :
      Stage.home B.raw u=Stage.home B.raw v ↔ Stage.home A (hop u)=Stage.home A (hop v) := by
    constructor
    · intro eqn;exact congrArg _ (congrArg hop (B.valid.coordinates eqn))
    · intro eqn;exact congrArg _ ((hop).injective (B.next.valid.coordinates eqn))
  exact or_congr (nodes _ _) (nodes _ _)

def rawResidents (e : (coarse).graph.Edge) :
    {f : (coarse).graph.Edge // 0<(coarse).graph.width f/(Z).unit ∧ atRawSource B e f} ≃
      Local (blocks B) ((blocks B).src e) where
  toFun f:=⟨f.val,by
    refine ⟨?_,(incident_restart B e f.val).mp f.property.2⟩
    change 0<weight B f.val
    rw [weight_quotient];exact f.property.1⟩
  invFun f:=⟨f.val,by
    refine ⟨?_,(incident_restart B e f.val).mpr f.property.2⟩
    rw [←weight_quotient B];exact f.property.1⟩
  left_inv _:=rfl
  right_inv _:=rfl

/-- The rank scan now uses the unique slot of every actual positive parent;
only the short values read from those slots enter its comparisons. -/
theorem measured_values (e : (coarse).graph.Edge) (he : 0<weight B e)
    (values : Fin (totalLocal B)→ℕ)
    (read : ∀k,values k=(localOrigin B ((blocks B).src e) k).elim 0
      (fun f=>if (tape).rank f.val<(tape).rank e then (blocks B).count f.val else 0)) :
    (∑k,values k)=(sourceTicket B e he).val := by
  simp_rw [read]
  rw [local_sum,sourceTicket_count_atRawSource]
  let pay (f : (coarse).graph.Edge):=
    if atRawSource B e f ∧ (tape).rank f<(tape).rank e then (coarse).graph.width f/(Z).unit else 0
  change _=∑f,pay f
  rw [←(rawResidents B e).sum_comp]
  have each (f : {f : (coarse).graph.Edge // 0<(coarse).graph.width f/(Z).unit ∧ atRawSource B e f}) :
      (if (tape).rank ((rawResidents B e f).val)<(tape).rank e then (blocks B).count (rawResidents B e f).val else 0)=pay f.val := by
    change (if (tape).rank f.val < (tape).rank e then weight B f.val else 0)=_
    simp [pay,f.property.2,weight_quotient]
  simp_rw [each]
  rw [←Fintype.sum_subtype_add_sum_subtype
    (fun f : (coarse).graph.Edge=>0<(coarse).graph.width f/(Z).unit ∧ atRawSource B e f) pay]
  have absent (f : {f : (coarse).graph.Edge // ¬(0<(coarse).graph.width f/(Z).unit ∧ atRawSource B e f)}) : pay f.val=0:=by
    by_cases yes : atRawSource B e f.val
    · have zero:=Nat.eq_zero_of_not_pos (fun h=>f.property ⟨h,yes⟩)
      simp [pay,zero]
    · simp [pay,yes]
  simp [absent]

theorem measured_ticket {b : ℕ} (e : (coarse).graph.Edge) (he : 0<weight B e)
    (j : Fin (totalLocal B)) (x : Fields (totalLocal B) b)
    (read : ∀k,fee x j k=(localOrigin B ((blocks B).src e) k).elim 0
      (fun f=>if (tape).rank f.val<(tape).rank e then (blocks B).count f.val else 0)) :
    (∑k,fee x j k)=(sourceTicket B e he).val :=
  measured_values B e he (fee x j) read

end
end Hierarchy.DescentSixParty.ClosedReset.Window

end OAI
