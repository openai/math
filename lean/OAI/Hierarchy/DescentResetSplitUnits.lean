import OAI.Hierarchy.DescentClosedReset
import OAI.Hierarchy.DescentSharedCableSiblings
import OAI.Hierarchy.DescentParallelBase

namespace OAI
/-! # The physical grain partition of the named post-reset graph -/
namespace Hierarchy.DescentSixParty.ClosedReset.Window
open Computability.BorderVNP.Crossing DescentCompiler DescentColonies DescentPhysicalOrder DescentPacking
open DescentSharedCableNames DescentSharedCableNames.Siblings DescentParallelBase
open DescentStageEdgeReceipt DescentCableUnbundling
open scoped Classical BigOperators
set_option quotPrecheck false
set_option maxHeartbeats 2000000
set_option maxRecDepth 8192
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

def piece (u : {e : (coarse).graph.Edge // e∈(coarse).core}) (j : Fin ((cnt) u.val)) : (world).graph.Edge :=
  .inr ⟨u,j⟩
local notation "piece'" => piece B
theorem core_piece (u : {e : (coarse).graph.Edge // e∈(coarse).core}) (j : Fin ((cnt) u.val)) :
    renameEdge (piece' u j)∈(next).core := by
  apply (PhysicalRename.core_mem world hop renameEdge (piece' u j)).2
  change Sum.inr (⟨u,j⟩:Row (coarse).graph (coarse).core cnt)∈Finset.univ.map Function.Embedding.inr
  exact Finset.mem_map.mpr ⟨⟨u,j⟩, Finset.mem_univ _, rfl⟩
local notation "paid" => core_piece B
def weight (u : (coarse).graph.Edge) := if yes : u∈(coarse).core then (cnt) u else (A).grainCount (renameEdge (.inl ⟨u,yes⟩))
local notation "wt" => weight B


theorem weight_width (u : (coarse).graph.Edge) : wt u*(Z).unit=(coarse).graph.width u := by
  by_cases core:u∈(coarse).core
  · rw [weight, dite_eq_left core]
    change ((Z).reenter T).graph.width u / (Z).unit * (Z).unit = ((Z).reenter T).graph.width u
    exact ((Z).counts_fit T u core).symm
  · rw [weight,dite_eq_right core]
    let e : (world).graph.Edge:=.inl ⟨u,core⟩
    have eqn:=(A).grainCount_fit S B.next.valid (renameEdge e)
    have unitEq : (A).z*G.b=(Z).unit:=by rw [B.next.grain,B.unit]
    rw [unitEq] at eqn
    change (PhysicalRename.graph (world).graph hop renameEdge).width (renameEdge e)=_ at eqn
    rw [PhysicalRename.width] at eqn
    exact eqn.symm

theorem weight_quotient (u : (coarse).graph.Edge) : wt u=(coarse).graph.width u/(Z).unit := by
  have pos : 0<(Z).unit:=by
    rw [B.unit,←B.next.grain]
    exact Nat.mul_pos (A).unitPos G.base_pos
  rw [←weight_width B u,Nat.mul_div_cancel _ pos]

def emit : (Σ u : (coarse).graph.Edge, Fin (wt u))→Stage.Grain A
  | ⟨u,j⟩=>if yes : u∈(coarse).core then
      let n : Fin ((cnt) u):=⟨j.val,by simpa only [weight,dite_eq_left yes] using j.isLt⟩
      let edge := renameEdge (piece' ⟨u,yes⟩ n)
      ⟨edge,⟨0,(A).quantum_positive edge (paid ⟨u,yes⟩ n)⟩⟩
    else ⟨renameEdge (.inl ⟨u,yes⟩),⟨j.val,by simpa only [weight,dite_eq_right yes] using j.isLt⟩⟩
local notation "grains" => emit B

private theorem emit_core (u : (coarse).graph.Edge) (yes : u∈(coarse).core) (j : Fin (wt u)) :
    let n : Fin ((cnt) u):=⟨j.val,by simpa only [weight,dite_eq_left yes] using j.isLt⟩
    grains ⟨u,j⟩=⟨renameEdge (piece' ⟨u,yes⟩ n),
      ⟨0,(A).quantum_positive (renameEdge (piece' ⟨u,yes⟩ n)) (paid ⟨u,yes⟩ n)⟩⟩:=by
  unfold emit
  exact dite_eq_left yes

private theorem emit_free (u : (coarse).graph.Edge) (off : u∉(coarse).core) (j : Fin (wt u)) :
    grains ⟨u,j⟩=⟨renameEdge (.inl ⟨u,off⟩),
      ⟨j.val,by simpa only [weight,dite_eq_right off] using j.isLt⟩⟩:=by
  unfold emit
  exact dite_eq_right off

theorem within_at (u : (coarse).graph.Edge) (j : Fin (wt u)) :
    (grains ⟨u,j⟩).2.val=(if u∈(coarse).core then 0 else j.val):=by
  by_cases yes:u∈(coarse).core
  · rw [emit_core B u yes j,ite_eq_left yes]
  · rw [emit_free B u yes j,ite_eq_right yes]

theorem core_at (u : (coarse).graph.Edge) (j : Fin (wt u)) : (grains ⟨u,j⟩).1∈(next).core ↔ u∈(coarse).core:=by
  by_cases yes:u∈(coarse).core
  · let idx : Fin ((cnt) u):=⟨j.val,by simpa only [weight,dite_eq_left yes] using j.isLt⟩
    apply iff_of_true _ yes
    rw [emit_core B u yes j]
    with_unfolding_all exact paid ⟨u,yes⟩ idx
  · apply iff_of_false _ yes
    intro mem
    simp only [emit,dite_eq_right yes] at mem
    have unbundled := (PhysicalRename.core_mem world hop renameEdge (.inl ⟨u,yes⟩)).mp mem
    change Sum.inl (⟨u,yes⟩:{t:(coarse).graph.Edge//t∉(coarse).core})∈Finset.univ.map Function.Embedding.inr at unbundled
    obtain ⟨r,_,eqn⟩ := Finset.mem_map.mp unbundled
    cases eqn

def firstGrain (u : (coarse).graph.Edge) (j : Fin (wt u)) : Fin (wt u) := if u∈(coarse).core then j else ⟨0,Nat.zero_lt_of_lt j.isLt⟩

theorem first_of_edge (u : (coarse).graph.Edge) (j : Fin (wt u)) :
    grains ⟨u,firstGrain B u j⟩=
      ⟨(grains ⟨u,j⟩).1,⟨0,Nat.zero_lt_of_lt (grains ⟨u,j⟩).2.isLt⟩⟩:=by
  by_cases yes:u∈(coarse).core
  · rw [show firstGrain B u j = j from ite_eq_left yes,emit_core B u yes j]
  · rw [show firstGrain B u j = ⟨0,Nat.zero_lt_of_lt j.isLt⟩ from ite_eq_right yes,
      emit_free B u yes _,emit_free B u yes j]

private def parentAt (edge : (world).graph.Edge) (t : ℕ) : (coarse).graph.Edge × ℕ :=
  match edge with
  | .inl u=>(u.val,t)
  | .inr ⟨u,j⟩=>(u.val,j.val)

def recover (g : Stage.Grain A) : (coarse).graph.Edge × ℕ :=
  parentAt B ((renameEdge).symm g.1) g.2.val
local notation "get" => recover B

theorem recover_emit (e : Σu,Fin (wt u)) : get (grains e)=(e.1,e.2.val) :=by
  obtain ⟨u,j⟩:=e
  by_cases yes : u∈(coarse).core
  · rw [emit_core B u yes j]
    let n : Fin ((cnt) u):=⟨j.val,by simpa only [weight,dite_eq_left yes] using j.isLt⟩
    exact congrArg (fun raw => parentAt B raw 0) ((renameEdge).symm_apply_apply (piece' ⟨u,yes⟩ n))
  · rw [emit_free B u yes j]
    exact congrArg (fun raw => parentAt B raw j.val) ((renameEdge).symm_apply_apply (.inl ⟨u,yes⟩))

def units : (Σu,Fin (wt u))≃Stage.Grain A :=Equiv.ofBijective grains (by
  constructor
  · intro x y eqn
    have same:=congrArg get eqn;simp only [recover_emit] at same
    have parent:=congrArg Prod.fst same
    exact Sigma.ext parent ((Fin.heq_ext_iff (congrArg wt parent)).mpr (congrArg Prod.snd same))
  · rintro ⟨e,j⟩;obtain ⟨raw,rfl⟩:=(renameEdge).surjective e
    cases raw with
    | inl u=>
      let i : Fin (wt u.val):=⟨j.val,by simpa only [weight,dite_eq_right u.property] using j.isLt⟩
      exact ⟨⟨u.val,i⟩,by simp [emit,u.property,i]⟩
    | inr u=>
      obtain ⟨u,s⟩:=u
      have fits : s.val < (cnt) u.val := s.isLt
      let i : Fin (wt u.val):=⟨s.val,by simpa only [weight,dite_eq_left u.property] using fits⟩
      have single := Siblings.paid_one A (renameEdge (piece' u s)) (paid u s)
      have zero : j.val=0:=by have less:=j.isLt;change j.val<(A).grainCount (renameEdge (piece' u s)) at less;omega
      refine ⟨⟨u.val,i⟩,?_⟩
      have at0 : j=⟨0,(A).quantum_positive (renameEdge (piece' u s)) (paid u s)⟩:=Fin.ext zero
      subst j
      rw [emit_core B u.val u.property i]; with_unfolding_all rfl)
local notation "unit'" => units B

def first (u : (coarse).graph.Edge) :=if live : 0<wt u then (stream' (grains ⟨u,⟨0,live⟩⟩)).val else 0
local notation "base'" => first B


end
end Hierarchy.DescentSixParty.ClosedReset.Window

end OAI
