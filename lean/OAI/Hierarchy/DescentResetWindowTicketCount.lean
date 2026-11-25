import OAI.Hierarchy.DescentResetWindowTicket
import OAI.Hierarchy.DescentParallelIncidentPosition

namespace OAI
/-! # Counting the original chronological source ticket before the signed window scan -/
namespace Hierarchy.DescentSixParty.ClosedReset.Window
open Computability.BorderVNP.Crossing DescentCompiler DescentColonies DescentPhysicalOrder DescentPacking
open DescentSharedCableNames DescentSharedCableNames.Siblings DescentParallelBase
open DescentStageEdgeReceipt DescentCableUnbundling
open scoped Classical BigOperators
set_option quotPrecheck false
noncomputable section
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
local notation "rawEnds" => Stage.source B.raw index
local notation "sourceHome" => fun e : (world).graph.Edge=>Stage.home B.raw ((world).graph.src e)
local notation "targetHome" => fun e : (world).graph.Edge=>Stage.home B.raw ((world).graph.dst e)
local notation "rawFit" => Stage.measured B.raw index S B.valid

theorem original_grains (r : (world).graph.Edge) :
    B.raw.grainCount r=(A).grainCount (renameEdge r) := by
  change (world).graph.width r/(B.raw.z*G.b)=
    (PhysicalRename.graph (world).graph hop renameEdge).width (renameEdge r)/((A).z*G.b)
  rw [PhysicalRename.width,B.next.grain,B.grain]

/-- For the first scan, one block is a single cable on the original
normalized tape, in the order that was actually issued on that tape. -/
def chronological : DescentParallelBase.Blocks rawEnds (world).graph.Edge where
  count:=B.raw.grainCount
  first:=ProtocolRAMPortRanks.«prefix» B.raw.grainCount index
  src:=sourceHome
  dst:=targetHome
  order:=Stage.stream B.raw index
  consecutive:=fun _ _=>rfl
  atSource:=by intro a j; simp only [Stage.source,Equiv.symm_apply_apply]
  atTarget:=by intro a j; simp only [Stage.source,Equiv.symm_apply_apply]

/-- Any positive normalized cable contributes its full true width before a
parent head exactly when its own original parent had the earlier issue slot. -/
theorem before_head (e : (coarse).graph.Edge) (he : 0<wt e) (a : (world).graph.Edge)
    (ha : 0<B.raw.grainCount a) :
    (chronological B).first a<(chronological B).first (rawHead B e he) ↔
      (tape).rank ((tape).owner a)<(tape).rank e := by
  let b:=rawHead B e he
  have nb : 0<B.raw.grainCount b:=head_grains B e he
  have idx : (chronological B).first a<(chronological B).first b ↔ index a < index b := by
    exact DescentOrderedGrainPrecedence.first B.raw.grainCount index a b ha nb
  rw [idx,head_index]
  change ((tape).order a).val < _ ↔ _
  rw [(tape).read a]
  exact DescentOrderedGrainPrecedence.before (tape).span (tape).rank _ _
    ((tape).offset a) ((tape).offsetFits a) (span_pos B e he)

/-- Collapse the normalized children in each actual installed row. Marked
rows each contribute one per child, and a tether contributes one unsplit
cable carrying its full number of grains. -/
theorem count_parents (pred : (coarse).graph.Edge→Prop) :
    (∑a : (world).graph.Edge,if pred ((tape).owner a) then B.raw.grainCount a else 0)=
      ∑u,if pred u then wt u else 0 := by
  let childCost (a : (world).graph.Edge) := if pred ((tape).owner a) then B.raw.grainCount a else 0
  let fee (u : (coarse).graph.Edge):=if pred u then wt u else 0
  change (∑a,childCost a)=∑u,fee u
  rw [← Fintype.sum_subtype_add_sum_subtype (fun u : (coarse).graph.Edge=>u∉(coarse).core) fee]
  have split := Fintype.sum_sum_type
    (α₁ := {u : (coarse).graph.Edge // u ∉ (coarse).core})
    (α₂ := (u : ↥((coarse).core)) × Fin ((cnt) u.val)) childCost
  refine split.trans ?_
  congr 1
  · apply Finset.sum_congr rfl
    intro f _
    change (if pred f.val then B.raw.grainCount (.inl f) else 0)=fee f.val
    simp only [fee, weight, dite_eq_right f.property]
    exact congrArg (fun amount => if pred f.val then amount else 0)
      (original_grains B (Sum.inl f))
  · let complement : ↥((coarse).core)≃{u : (coarse).graph.Edge // ¬u∉(coarse).core} :=
      ⟨fun u=>⟨u.val,not_not_intro u.property⟩,fun u=>⟨u.val,Classical.not_not.mp u.property⟩,fun _=>rfl,fun _=>rfl⟩
    erw [Fintype.sum_sigma,←Equiv.sum_comp complement (fun u=>fee u.val)]
    apply Finset.sum_congr rfl
    intro u _
    have one (j : Fin ((cnt) u.val)) : B.raw.grainCount (piece' u j)=1 :=
      (original_grains B _).trans (Siblings.paid_one A _ (core_piece B u j))
    change (∑j : Fin ((cnt) u.val),if pred u.val then B.raw.grainCount (piece' u j) else 0)=fee u.val
    by_cases yes : pred u.val <;> simp [yes,one,fee,weight,u.property]

theorem sourceTicket_count (e : (coarse).graph.Edge) (he : 0<wt e) :
    (sourceTicket B e he).val=∑f,if
      (Stage.home B.raw ((coarse).graph.src f)=Stage.home B.raw ((coarse).graph.src e) ∨
        Stage.home B.raw ((coarse).graph.dst f)=Stage.home B.raw ((coarse).graph.src e)) ∧
        (tape).rank f<(tape).rank e
      then (coarse).graph.width f/(Z).unit else 0 := by
  let b:=rawHead B e he
  let h₀:=sourceHome b
  let r : DescentParallelBase.Local (chronological B) h₀:=⟨b,head_grains B e he,Or.inl rfl⟩
  have start:=DescentParallelBase.Incidence.initial (chronological B) h₀ rawFit r
  change (sourceTicket B e he).val=_ at start
  rw [start]
  let pred (f : (coarse).graph.Edge):= (Stage.home B.raw ((coarse).graph.src f)=Stage.home B.raw ((coarse).graph.src e) ∨
    Stage.home B.raw ((coarse).graph.dst f)=Stage.home B.raw ((coarse).graph.src e)) ∧ (tape).rank f<(tape).rank e
  refine Eq.trans ?_ ((count_parents B pred).trans ?_)
  ·
      apply Finset.sum_congr rfl
      intro a _
      have hs : (world).graph.src a=(coarse).graph.src ((tape).owner a):=by cases a <;> rfl
      have ht : (world).graph.dst a=(coarse).graph.dst ((tape).owner a):=by cases a <;> rfl
      have here : h₀=Stage.home B.raw ((coarse).graph.src e):=congrArg (Stage.home B.raw) (head_fields B e he).2.2.1
      change (if (sourceHome a=h₀ ∨ targetHome a=h₀) ∧ (chronological B).first a<(chronological B).first b
        then B.raw.grainCount a else 0)=_
      by_cases positive : 0<B.raw.grainCount a
      · have rank : (chronological B).first a < (chronological B).first b ↔ (tape).rank ((tape).owner a)<(tape).rank e := before_head B e he a positive
        by_cases hit : pred ((tape).owner a)
        · have yes : (sourceHome a=h₀ ∨ targetHome a=h₀) ∧ (chronological B).first a<(chronological B).first b := by
            simpa only [rank, hs, ht, here, pred] using hit
          rw [ite_eq_left yes, ite_eq_left hit]
        · have no : ¬((sourceHome a=h₀ ∨ targetHome a=h₀) ∧ (chronological B).first a<(chronological B).first b) := by
            simpa only [rank, hs, ht, here, pred] using hit
          rw [ite_eq_right no, ite_eq_right hit]
      · simp only [Nat.eq_zero_of_not_pos positive,ite_self]
  · apply Finset.sum_congr rfl
    intro u _
    by_cases hit : pred u
    · rw [ite_eq_left hit]
      dsimp only [pred] at hit
      rw [ite_eq_left hit,weight_quotient]
    · rw [ite_eq_right hit]
      dsimp only [pred] at hit
      rw [ite_eq_right hit]

end
end Hierarchy.DescentSixParty.ClosedReset.Window

end OAI
