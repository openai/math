import OAI.Computability.BorderVNP.CubePhysicalPreparedFinish
import OAI.Computability.BorderVNP.RoutingISAScheduleClockCube

/-! # The actual owned cube vertices and original power slots charged after the private calls -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.SignedTaskArena

open Crossing BorderVNP.Cube Physical Padding.Banks Cube.TeamRows TeamRowClock FiniteEvaluator VPVNP.BurstRAM
open Evaluator.ScheduleClock
open scoped Classical BigOperators

variable {w : ℕ} (sa : Layout) (pub : Arg → Word w) (owner : Fin sa.cube.header.d → ℕ) (R : ℕ)
    (u : Fin (R+1)) (demand : ℕ) (data : Data sa.cube.n sa.cube.header.d sa.cube.header.blocks sa.cube.b
        sa.cube.h sa.cube.K sa.cube.s) (before after : ℕ → ℕ)
local notation "groups" => sa.cube.header.d
local notation "scan" => sa.cube.scanner (Fin.val (pub 0)) u.val data.axis.val sa.cube.rowSelectorBits
local notation "weights" => LocalRow.weightLayout sa.cube (Fin.val (pub 0)) data.axis.val
local notation "teams" => LocalRow.teamLayout sa.cube R

/-- Every reference actually emitted for this team's signed cube tally was
visited in the physical group scan. Its local budget uses exactly the groups
assigned by the checked owner memory. -/
theorem gadgetLookup_visited_le {Operand : Type*} [Fintype Operand]
    {decl : LengthDeclaration sa.cube.n sa.cube.header.d}
    {label : Fin sa.cube.cells → Label (sa.cube.n+1) sa.cube.header.d}
    {recv : Operand → Fin sa.cube.cells} {incoming : Operand → ℕ}
    (scheduled : GroupWeights.ScheduleResult weights teams before after)
    (image : GroupWeights.PhysicalImage weights before sa.cube.header.blocks sa.cube.b sa.cube.K sa.cube.h
      decl label recv incoming) (stored : ∀ i : Fin groups, owner i = after ((teams).owners+i.val))
    (X : ℕ) (positive : 0 < sa.cube.h*sa.cube.b) (alphabet : 0<groups)
    (pass : (TeamBudget.Layout.mk (R+1) X (teams).totals).Passes after) :
    (gadgetLookup sa pub owner u.val demand data).frame.count ≤
      physicalCoefficient sa.cube.n sa.cube.b sa.cube.h sa.cube.K sa.cube.s * ((groups^(sa.cube.n+1))^2+X) := by
  let cap := groups*groups
  have seen := CubeTriple.prefix_length (l:=scan) data.axis sa.cube.header.blocks owner cap le_rfl
  have full : CubeTriple.visited data.axis sa.cube.header.blocks owner u.val cap =
      CubeVisits.teamList data.axis sa.cube.header.blocks owner u.val := by
    simp only [CubeTriple.visited,CubeVisits.teamList,List.take_of_length_le (show (List.finRange (groups*groups)).length ≤ cap by simp [cap])]
  change (CubeTriple.visited data.axis sa.cube.header.blocks owner u.val cap).length =
    vertexPrefix scan (wordOwner owner) sa.cube.n sa.cube.header.blocks cap at seen
  change (CubeVisits.teamList data.axis sa.cube.header.blocks owner u.val).length ≤ _
  rw [←full,seen]
  have names : vertexPrefix scan (wordOwner owner) sa.cube.n sa.cube.header.blocks cap =
      vertexPrefix scan (fun i => after ((teams).owners+i)) sa.cube.n sa.cube.header.blocks cap := by
    unfold vertexPrefix
    apply Finset.sum_congr rfl
    intro j hj
    let i : Fin (groups*groups) := ⟨j,Finset.mem_range.mp hj⟩
    have word : wordOwner owner (j/groups) = after ((teams).owners+j/groups) := by
      change wordOwner owner i.divNat.val = after ((teams).owners+i.divNat.val)
      simpa only [wordOwner,dite_eq_left i.divNat.isLt,Fin.eta] using stored i.divNat
    exact congrArg (fun v => if v = u.val ∧ j/groups ≠ j%groups then
      strictVertices sa.cube.n groups sa.cube.header.blocks else 0) word
  rw [names]
  exact (vertexPrefix_le_roleTicks scan (fun i => after ((teams).owners+i)) sa.cube.n sa.cube.header.blocks
    sa.cube.b sa.cube.h sa.cube.K sa.cube.s (d:=groups) rfl decl.1).trans
    (checkedTeamTicks_le_sq scheduled image u scan rfl rfl X sa.cube.s positive alphabet pass)

end RoutingISA.SignedTaskArena

namespace DiagonalTallyCellReports

open Diagonal.CellEntries
open scoped BigOperators

/-- Each unary operand occupies one cell, bundle and marked copy ordinal. -/
theorem teamWeighted_eq_card {l : ReportLayout} (cs : List (ReportCell l)) :
    teamWeighted cs = Fintype.card (UseOccurrence cs) := by
  rw [occurrence_card]
  simp only [←List.sum_ofFn]
  have inner (c : ReportCell l) :
      (List.ofFn (fun j : Fin c.bundles.length => c.bundles[j].useCount)).sum = weightedCopies c.bundles :=
    congrArg List.sum (List.ofFn_getElem_eq_map c.bundles ReportBundle.useCount)
  simp_rw [inner]
  exact (congrArg List.sum (List.ofFn_getElem_eq_map cs (fun c => weightedCopies c.bundles))).symm

/-- The expanded count of unary operands at an owning team fits the global
original slot roster, even when some unchecked shared report bits are zero. -/
theorem teamWeighted_le_powerSlots {l : ReportLayout} {Team Param : Type} [Fintype Team] [Fintype Param]
    {B : ℕ} (cs : List (ReportCell l)) (toSlot : UseOccurrence cs ↪ PowerSlot Team Param B) :
    teamWeighted cs ≤ Fintype.card (PowerSlot Team Param B) := by
  rw [teamWeighted_eq_card]
  exact Fintype.card_le_of_injective _ toSlot.injective

/-- Embed the work positions of a local returning report into its actual
reserved capacity, using the complete physical owned-cell permutation. This
counts arbitrary locally received words before any cross-team acceptance. -/
noncomputable def ReportAllocation.ownedUseSlots {l : ReportLayout} {p : DiagonalTallyAllocation.BeforeTasks}
    {a : DiagonalTallyAllocation.AfterTasks} {banks : BorderVNP.RoutingISA.CellBanks.Layout}
    {q : ReportCursor} {cs : List (ReportCell l)} (space : ReportAllocation p a banks l cs q)
    {C R H B : ℕ} (owner : Fin C → ℕ) (u : ℕ) (reports : Fin C → ReportCell l)
    (order : Fin cs.length ≃ {c : Fin C // owner c=u})
    (grouped : ∀ j, cs[j].bundles=(reports (order j).val).bundles) (reserved : a.bound.uses ≤ R*(H*B)) :
    ((c : {c : Fin C // owner c=u}) × UsePositions (reports c.val).bundles) ↪
      PowerSlot (Fin R) (Fin H) B := by
  classical
  let slots := PowerSlot (Fin R) (Fin H) B
  let retained : UseOccurrence cs ≃ ((c : {c : Fin C // owner c=u}) × UsePositions (reports c.val).bundles) :=
    (Equiv.sigmaCongrRight fun i => Equiv.cast (congrArg UsePositions (grouped i))).trans
      (Equiv.sigmaCongrLeft (β := fun c : {c : Fin C // owner c=u} => UsePositions (reports c.val).bundles) order)
  have fits : Fintype.card (UseOccurrence cs) ≤ Fintype.card slots := by
    rw [←teamWeighted_eq_card]
    simpa only [slots,PowerSlot,Fintype.card_prod,Fintype.card_fin] using space.uses.trans reserved
  exact retained.symm.toEmbedding.trans ((Fintype.equivFin _).toEmbedding.trans
    (Fin.castLEEmb fits |>.trans (Fintype.equivFin slots).symm.toEmbedding))

end DiagonalTallyCellReports

end BorderVNP
end Computability
end OAI
