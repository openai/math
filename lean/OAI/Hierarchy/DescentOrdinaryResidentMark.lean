import OAI.Hierarchy.DescentOrdinaryParentSupport
import OAI.Hierarchy.DescentPackedPhysicalWalk
import OAI.Hierarchy.DescentOrdinaryMarkGather

namespace OAI
/-! # The old normalized source handle determines the surviving parent's core bit -/
namespace Hierarchy.DescentOrdinarySignedMeta
open Computability.BorderVNP.Crossing DescentSixParty DescentSixParty.MarkedWorld DescentCableDonorNames DescentHostDirectory DescentColonies
open DescentStageEdgeReceipt GadgetNetwork
open scoped Classical Fin.CommRing
noncomputable section
variable {F P I C H : Type} [Field F] [Fintype I] [DecidableEq H] {d : ℕ} {bits : P→ℕ}
    (W : MarkedWorld F d P bits) (G : PoweredGadget F)
    (pick : I×Fin 2↪W.graph.Edge) (z : I→ℕ) (hz : ∀i,0<z i)
    (fit : ∀i s,W.graph.width (pick (i,s))=z i*G.b) (pack : W.graph.Site→C) (p : I→Profile G.C)
local notation "sel" => W.selected G pick z hz fit pack p
variable (key : (W.selected G pick z hz fit pack p).graph.Site↪Key H) (flag : H→Bool) (k g : ℕ)
local notation "coarse" => MarkedWorld.coalesced sel key flag k g

def markRole (j : Fin 11) (old : Bool) := if j.val=0 then old else true

set_option backward.isDefEq.respectTransparency false in
theorem core_role (u : (coarse).graph.Edge) :
    markRole (role u.val.val) (decide (anchor pick u.val.val∈W.core))=decide (u∈(coarse).core) := by
  have mem : u∈(coarse).core ↔ u.val∈(sel).core := by
    constructor
    · intro hit
      exact (Finset.mem_filter.mp hit).2
    · intro hit
      apply Finset.mem_filter.mpr
      exact ⟨@Finset.mem_univ _ (Subtype.fintype _) _,hit⟩
  let marked : GadgetNetwork.Edge (I:=I) W.graph → Prop := fun q =>
    match q with | .inl t => t∈W.core | .inr _ => True
  have selected : u.val∈(sel).core ↔ marked u.val.val := by
    have native := GadgetNetwork.mem_nextCore W.graph pick (branchWidth G z p)
      (bestLayout (branchWidth G z p)) pack (fun _=>(0:EuclideanSpace ℝ (Fin d)))
      (fun _=>by simp) W.core u.val
    refine native.trans ?_
    cases u.val.val <;> rfl
  classical
  have bits : decide (marked u.val.val) = decide (u∈(coarse).core) := decide_eq_decide.mpr (mem.trans selected).symm
  refine Eq.trans ?_ bits
  cases edge:u.val.val with
  | inl e => simp [role,anchor,markRole,marked]
  | inr a => rcases a with ⟨j,s⟩|⟨j,s⟩ <;> simp [role,markRole,marked]


section Readback
open DescentSharedCableNames
open DescentPacking.PackedMatch.Local.Stage
variable {J V : Type} [Fintype J] [DecidableEq J] [Fintype V] [DecidableEq V]
    {stage age : ℕ} {price ε : ℝ} (A : GroupStage W G price ε J V stage)
    (native : W.graph.Edge↪ℕ) (S : DescentCompiler.AtomSchedule) (ready : A.StateBounds S age) (rank : (J×V)↪ℕ)

/-- The role discriminator is a literal column number in the eleven-row parent
archive. For the old-cable column its bit is fetched from the source first grain. -/
theorem origin_mark (u : (coarse).graph.Edge) (positive : 0<A.grainCount (anchor pick u.val.val)) :
    let e : Stage.Positive A := ⟨anchor pick u.val.val,positive⟩
    let h:=Stage.home A (W.graph.src e.val)
    let j:=Stage.signed A native S ready h.1 h.2 (originPort A e)
    ∃ handle, Stage.signedPanel A native S ready (cableNames stage rank) h j=some handle ∧
      markRole (role u.val.val) handle.markedOut=decide (u∈(coarse).core) := by
  dsimp only
  refine ⟨sourceHandle A native S ready rank ⟨_,positive⟩,origin_stored A native S ready rank ⟨_,positive⟩,?_⟩
  have bit : (sourceHandle A native S ready rank ⟨_,positive⟩).markedOut=decide (anchor pick u.val.val∈W.core) := by
    simp [sourceHandle,Stage.live,Stage.isMarkedOut,originPort]
  rw [bit]
  exact core_role W G pick z hz fit pack p key flag k g u
/-- The previous normalized report is indexed by sign and first local grain.
The sparse donor archive stores this very outgoing grain ordinal. -/
theorem origin_address (e : Stage.Positive A) :
    let h:=Stage.home A (W.graph.src e.val)
    Stage.signed A native S ready h.1 h.2 (originPort A e)=
      finProdFinEquiv ((0:Fin 2),Stage.outgoing A native S ready e) := rfl

/-- Identify the argument of the literal mark lookup after the true selected
old-halo read. This equality covers each reached emitting candidate. -/
theorem reached_mark {H₀ G₀ P₀ : ℕ} (u : (coarse).graph.Edge)
    (positive : 0<A.grainCount (anchor pick u.val.val))
    (host : Fin H₀→Fin G₀→Stage.Host J V stage) (ticket : Fin A.cap)
    (R : Fin H₀→Fin P₀→Option (Fin H₀)) (v donor : Fin H₀) (path : Fin P₀) (lane : Fin G₀)
    (hit : DescentHaloWalkRAM.Gather.select R v path=some donor)
    (home : host donor lane=Stage.home A (W.graph.src (anchor pick u.val.val)))
    (number : ticket=Stage.outgoing A native S ready ⟨_,positive⟩) :
    let old:=fun x=>Stage.signedPanel A native S ready (cableNames stage rank) (host x lane)
      (finProdFinEquiv ((0:Fin 2),ticket))
    MarkGather.flag (decide ((role u.val.val).val≠0))
      ((DescentHaloWalkRAM.Gather.select R v path).bind old)=
      ((decide (u∈(coarse).core)).toNat:DescentSIMDLookup.Cell 1) := by
  intro old
  obtain ⟨record,stored,core⟩:=origin_mark W G pick z hz fit pack p key flag k g A native S ready rank u positive
  have phys : old donor=some record := by
    dsimp [old]
    rw [home,number,←origin_address W G A native S ready]
    exact stored
  simp only [hit,Option.bind_some,phys,MarkGather.flag,Option.any_some]
  by_cases fresh : (role u.val.val).val=0
  · simpa [markRole,fresh] using congrArg (fun b : Bool=>(b.toNat:DescentSIMDLookup.Cell 1)) core
  · simpa [markRole,fresh] using congrArg (fun b : Bool=>(b.toNat:DescentSIMDLookup.Cell 1)) core
/-- Interpret the actual compact donor rectangle (old block, outgoing grain
ordinal, eleven-way role) against the previous normalized signed bank. -/
def donorPanel {nh groups : ℕ} (lookup : Fin nh→Option V) (group : Fin groups→J)
    (slot : Fin (2^stage*A.cap*11)) (v : Fin nh) (g : Fin groups) :=
  let entry : Fin (2^stage*A.cap) × Fin 11 := finProdFinEquiv.symm slot
  let col : Fin (2^stage) × Fin A.cap := finProdFinEquiv.symm entry.1
  (lookup v).bind (fun a=>Stage.signedPanel A native S ready (cableNames stage rank)
    ((group g,a),col.1) (finProdFinEquiv ((0:Fin 2),col.2)))

/-- On every live physical ordinal of the real shortSlot archive the computed
received flag equals the actual coarse core predicate. Both endpoint visits
use the same address and the same signed source handle. -/
theorem shortSlot_mark [DecidableEq I] {nh groups paths : ℕ} (vertex : V↪Fin nh)
    (lookup : Fin nh→Option V) (installed : ∀v,lookup (vertex v)=some v)
    (group : Fin groups→J) (u : (coarse).graph.Edge)
    (positive : 0<A.grainCount (anchor pick u.val.val))
    (R : Fin nh→Fin paths→Option (Fin nh)) (receiver : Fin nh) (path : Fin paths) (lane : Fin groups)
    (reached : DescentHaloWalkRAM.Gather.select R receiver path=
      some (vertex (A.pos (W.graph.src (anchor pick u.val.val))).2))
    (groupAt : group lane=(A.pos (W.graph.src (anchor pick u.val.val))).1) :
    let slot:=(DescentRawCablePanel.shortSlot A S ready native vertex pick ⟨u.val.val,positive⟩).2
    let code:=((finProdFinEquiv.symm slot : Fin (2^stage*A.cap) × Fin 11).2)
    MarkGather.flag (decide (code.val≠0)) ((DescentHaloWalkRAM.Gather.select R receiver path).bind
      (fun donor=>donorPanel W G A native S ready rank lookup group slot donor lane))=
        ((decide (u∈(coarse).core)).toNat:DescentSIMDLookup.Cell 1) := by
  intro slot code
  obtain ⟨handle,found,core⟩:=origin_mark W G pick z hz fit pack p key flag k g A native S ready rank u positive
  rw [reached,Option.bind_some]
  simp only [code,slot,donorPanel,DescentRawCablePanel.shortSlot,Equiv.symm_apply_apply,
    installed,Option.bind_some,groupAt]
  rw [←origin_address W G A native S ready]
  refine (congrArg (MarkGather.flag (decide ((role u.val.val).val≠0))) found).trans ?_
  by_cases fresh : (role u.val.val).val=0 <;>
    simpa [MarkGather.flag,markRole,fresh] using congrArg (fun b : Bool=>(b.toNat:DescentSIMDLookup.Cell 1)) core

end Readback
end
end Hierarchy.DescentOrdinarySignedMeta

end OAI
