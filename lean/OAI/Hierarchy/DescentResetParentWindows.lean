import OAI.Hierarchy.DescentResetSplitUnits
import OAI.Hierarchy.DescentResetWindowFields

namespace OAI
/-! # Consecutive signed windows for every actually installed reset parent -/
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
local notation "cnt" => fun e : (coarse).graph.Edge => (coarse).graph.width e/(Z).unit
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

/-- The previous native enumeration is the packed parent prefix plus its
physical child offset, even before the next matcher groups by source. -/
theorem emitted_child (u : {e : (coarse).graph.Edge // e∈(coarse).core}) (j : Fin ((cnt) u.val)) :
    index (piece' u j)=ProtocolRAMPortRanks.«prefix» (tape).span (tape).rank u.val+j.val :=
  (tape).read (piece' u j)

theorem names_lt (a b : (world).graph.Edge) :
    ord (renameEdge a)<ord (renameEdge b) ↔ sparse a<sparse b := by
  have named (x : (world).graph.Edge) :
      ord (renameEdge x) = (DescentPhysicalOrder.physical sparse x).val := by
    exact (B.next.edgeName (Nat.zero_lt_succ i) (renameEdge x)).symm.trans
      (congrArg Fin.val (DescentPhysicalOrder.code_rename sparse x))
  rw [named a,named b]
  exact DescentPhysicalOrder.physical_lt_iff sparse a b

theorem child_step (u : {e : (coarse).graph.Edge // e∈(coarse).core}) (j t : Fin ((cnt) u.val))
    (step : t.val=j.val+1) : sparse (piece' u t)=sparse (piece' u j)+1 := by
  apply DescentResetLocalOrder.adjacent B.raw index S B.valid rawSite (x:=piece' u j) (y:=piece' u t) rfl
  rw [emitted_child,emitted_child,step,Nat.add_assoc]

theorem time_next (u : (coarse).graph.Edge) (j t : Fin (wt u)) (st : t.val=j.val+1) :
    (stream' (grains ⟨u,t⟩)).val=(stream' (grains ⟨u,j⟩)).val+1 := by
  by_cases yes : u∈(coarse).core
  · let a : Fin ((cnt) u):=⟨j.val,by simpa [weight,yes] using j.isLt⟩
    let b : Fin ((cnt) u):=⟨t.val,by simpa [weight,yes] using t.isLt⟩
    let x:=piece' ⟨u,yes⟩ a
    let y:=piece' ⟨u,yes⟩ b
    have gap : sparse y=sparse x+1:=child_step B ⟨u,yes⟩ a b st
    have order:=Siblings.before renameEdge sparse ord (names_lt B) gap
    have start:=Siblings.prefix_next (A).grainCount ord (renameEdge x) (renameEdge y) order
    have marked : renameEdge x ∈ (next).core := core_piece B ⟨u,yes⟩ a
    have one := Siblings.paid_one (W:=next) (G:=G) A (renameEdge x) marked
    rw [one] at start
    simp only [emit, dite_eq_left yes, Stage.stream]
    exact start
  · let edge : (world).graph.Edge := .inl ⟨u,yes⟩
    let start := ProtocolRAMPortRanks.«prefix» (A).grainCount ord (renameEdge edge)
    simp only [emit, dite_eq_right yes]
    change start + t.val = start + j.val + 1
    rw [st, Nat.add_assoc]

theorem block_time (u : (coarse).graph.Edge) (j : Fin (wt u)) :
    (stream' (grains ⟨u,j⟩)).val=base' u+j.val := by
  obtain ⟨j,limit⟩:=j
  induction j with
  | zero=>simp [first,limit]
  | succ j ih=>
    let a : Fin (wt u):=⟨j,by omega⟩
    let b : Fin (wt u):=⟨j+1,limit⟩
    have step:=time_next B u a b rfl
    exact step.trans (congrArg Nat.succ (ih a.isLt))

/-- The actual reset mothers are the stems, hub limbs, contacts, rotor rows
and fallback-tree rows. Every emitted signed grain is enumerated once here;
a loop can subsequently occupy one face at each sign of its same cell. -/
def blocks : Blocks board (coarse).graph.Edge where
  count:=wt
  first:=base'
  src u:=Stage.home A (hop ((coarse).graph.src u))
  dst u:=Stage.home A (hop ((coarse).graph.dst u))
  order:=(units B).trans stream'
  consecutive:=block_time B
  atSource:=by
    intro u j
    change (board).src (stream' (grains ⟨u,j⟩))=_
    by_cases yes:u∈(coarse).core <;>
      simp only [Stage.source, Equiv.symm_apply_apply, emit, dite_eq_left, yes]
    all_goals exact congrArg (Stage.home A) (PhysicalRename.src (world).graph hop renameEdge _)
  atTarget:=by
    intro u j
    change (board).dst (stream' (grains ⟨u,j⟩))=_
    by_cases yes:u∈(coarse).core <;>
      simp only [Stage.source, Equiv.symm_apply_apply, emit, dite_eq_left, yes]
    all_goals exact congrArg (Stage.home A) (PhysicalRename.dst (world).graph hop renameEdge _)

def emission : DescentResetWindowFields.Emission A ord (blocks B) (fun u=>u∈(coarse).core) where
  units:=units B
  order_eq:=fun _ _=>rfl
  within_at:=by
    intro e j
    by_cases yes : e∈(coarse).core <;> simpa only [yes,ite_true,ite_false] using! within_at B e j
  core_at:=core_at B
  first_of_edge:=by
    intro e j
    by_cases yes : e∈(coarse).core <;> simpa only [firstGrain,yes,ite_true,ite_false] using! first_of_edge B e j

end
end Hierarchy.DescentSixParty.ClosedReset.Window

end OAI
