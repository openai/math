import OAI.Hierarchy.DescentOrdinaryParentBlocks
import OAI.Hierarchy.DescentRawCableRoles
import OAI.Hierarchy.DescentParentGroupSlot

namespace OAI
/-! # Ordinary signed parent windows on exactly the surviving positive raw roles -/
namespace Hierarchy.DescentOrdinaryParentSupport
open Computability.BorderVNP.Crossing DescentSixParty DescentSixParty.MarkedWorld DescentPhysicalOrder
open DescentHostDirectory DescentColonies DescentStageEdgeReceipt DescentPacking DescentCableDonorNames
open DescentSharedCableNames DescentSharedCableNames.Siblings DescentOrdinarySiblingSerial DescentParallelBase
open private DescentOrdinarySiblingSerial.physicalBase DescentOrdinarySiblingSerial.physicalKey
  from OAI.Hierarchy.DescentOrdinarySiblingSerial
open GadgetNetwork
open scoped Classical BigOperators
noncomputable section
set_option quotPrecheck false
variable {F P I C H : Type} [Field F] [Fintype I] [DecidableEq H] {d : ℕ} {bits : P→ℕ}
variable (W : MarkedWorld F d P bits) (G : PoweredGadget F)
local notation "N" => W.graph
variable (edge : W.graph.Edge↪Fin (Fintype.card W.graph.Edge)) (pair : I≃Fin (Fintype.card I))
variable (pick : I×Fin 2↪W.graph.Edge) (z : I→ℕ) (hz : ∀i,0<z i)
variable (fit : ∀i s,W.graph.width (pick (i,s))=z i*G.b) (pack : W.graph.Site→C) (p : I→Profile G.C)
local notation "sel" => W.selected G pick z hz fit pack p
variable (key : (W.selected G pick z hz fit pack p).graph.Site↪Key H) (flag : H→Bool) (k g q : ℕ)
variable (old : ∀e∈W.core,q∣W.graph.width e) (picked : ∀j,pick j∈W.core) (affected : ∀i,q∣z i)
local notation "coarse" => coalesced sel key flag k g
local notation "rep" => repetitions W G pick z hz fit pack p key flag k g q
local notation "world" => DescentOrdinarySiblingSerial.physicalBase W G pick z hz fit pack p key flag k g q old picked affected
local notation "tape" => ordinary W G edge pair pick z hz fit pack p key flag k g q old picked affected
variable (site : (coalesced (W.selected G pick z hz fit pack p) key flag k g).graph.Site ↪ ℕ)
local notation "sparse" => DescentOrdinarySiblingSerial.physicalKey W G edge pair pick z hz fit pack p key flag k g q old picked affected site
local notation "next" => PhysicalRename.rankedWorld world site sparse
variable {J V : Type} [Fintype J] [DecidableEq J] [Fintype V] [DecidableEq V] {stage : ℕ} {price ε : ℝ}
variable (A : GroupStage
    (PhysicalRename.rankedWorld
      (DescentOrdinarySiblingSerial.physicalBase W G pick z hz fit pack p key flag k g q old picked affected) site
      (DescentOrdinarySiblingSerial.physicalKey W G edge pair pick z hz fit pack p key flag k g q old picked affected site))
    G price ε J V stage)

local notation "ls" => rename site
local notation "ord" => originalId (next).graph.Edge
local notation "stream'" => Stage.stream A ord
local notation "B" => Stage.source A ord


local notation "raw" => Raw W.graph.Edge I
local notation "sw" => branchWidth G z p
local notation "firstSite" => newSite N pick (bestLayout sw) pack
local notation "lastSite" => MarkedWorld.address sel key flag k g
local notation "bitsAt" => GadgetNetwork.width N pick sw
local notation "src₀" => GadgetNetwork.source (I:=I) N
local notation "dst₀" => GadgetNetwork.target N pick

/-- Original, arm, and supply rows use the same two actual quotient maps. -/
def survives (e : raw) : Prop :=
  lastSite (firstSite (src₀ e)) ≠ lastSite (firstSite (dst₀ e))

local notation "kept" => survives W G pick z hz fit pack p key flag k g

def parent : (coarse).graph.Edge ≃ {e : raw // kept e} where
  toFun e:=⟨e.val.val,e.property⟩
  invFun e:=⟨⟨e.val,fun h=>e.property (congrArg lastSite h)⟩,e.property⟩
  left_inv _:=rfl
  right_inv _:=rfl

theorem picked_dead (i : I) (s : Fin 2) : ¬kept (.inl (pick (i,s))) :=fun different=>
  different (congrArg lastSite (DescentRawCablePanel.picked_old N pick (bestLayout sw) pack i s))
theorem arm_dead (i : I) (s : Fin 2) : ¬kept (.inr (.inl (i,s))) :=fun different=>
  different (congrArg lastSite (DescentRawCablePanel.picked_arm N pick (bestLayout sw) pack i s))

local notation "wt" => DescentOrdinaryParentBlocks.weight W G edge pair pick z hz fit pack p key flag k g q old picked affected site A
variable {i : ℕ} (S : DescentCompiler.AtomSchedule) (ready : A.StateBounds S i)
    (grain : A.z*G.b=q) (qp : 0<q)

include ready grain qp in
theorem positive (u : (coarse).graph.Edge) : 0<wt u ↔ 0<bitsAt u.val.val := by
  have paid:=DescentOrdinaryParentBlocks.weight_width W G edge pair pick z hz fit pack p key flag k g q old picked affected site A S ready grain u
  change wt u*q=bitsAt u.val.val at paid
  rw [←paid]
  constructor
  · exact fun pos=>Nat.mul_pos pos qp
  · intro pos
    by_contra! h
    have zero : wt u=0:=by omega
    simp [zero] at pos

local notation "C₀" => DescentOrdinaryParentBlocks.blocks W G edge pair pick z hz fit pack p key flag k g q old picked affected site A qp
local notation "portAt" => fun s=>Stage.home A (ls (lastSite (firstSite s)))
local notation "positiveParent" => positive W G edge pair pick z hz fit pack p key flag k g q old picked affected site A S ready grain qp

private theorem count_le_incident {E U : Type} [DecidableEq U] {n : ℕ} {ends : Ends U n}
    (blocks : Blocks ends E) (e : E) : blocks.count e ≤ (ends.incident (blocks.src e)).card := by
  let inc (j : Fin (blocks.count e)) : ↥(ends.incident (blocks.src e)) :=
    ⟨blocks.order ⟨e,j⟩, by simp [Ends.incident, blocks.atSource]⟩
  have inj : Function.Injective inc := by
    intro j k eqn
    exact eq_of_heq (Sigma.mk.inj_iff.mp (blocks.order.injective (congrArg Subtype.val eqn))).2
  simpa only [Fintype.card_fin, Fintype.card_coe] using Fintype.card_le_of_injective inc inj

include ready qp in
/-- All grains of one surviving positive parent spend distinct original incidence slots at its source. -/
theorem parent_mass_bound (u : (coarse).graph.Edge) :
    (DescentOrdinaryParentBlocks.weight W G edge pair pick z hz fit pack p key flag k g q old picked affected site A u)≤A.cap :=by
  exact (count_le_incident C₀ u).trans (Stage.measured A ord S ready ((C₀).src u))

include ready grain qp in
/-- The width on the original pre-trim incidence is paid by the new signed output capacity. -/
theorem raw_mass_bound (e : raw) (different : kept e) : bitsAt e/q≤A.cap :=by
  let u:(coarse).graph.Edge:=(parent W G pick z hz fit pack p key flag k g).symm ⟨e,different⟩
  have weight:=DescentOrdinaryParentBlocks.weight_width W G edge pair pick z hz fit pack p key flag k g q
    old picked affected site A S ready grain u
  change wt u*q=bitsAt e at weight
  rw [←weight,Nat.mul_div_cancel _ qp]
  exact parent_mass_bound W G edge pair pick z hz fit pack p key flag k g q old picked affected site A S ready qp u

include ready grain in
/-- A local parent row exists exactly when its published post-trim endpoints
differ, its true width is positive, and one of its endpoints is at this window. -/
def localRows (h : Stage.Host J V stage) : Local C₀ h ≃
    {e : raw // kept e ∧ 0<bitsAt e ∧ ((portAt) (src₀ e)=h ∨ (portAt) (dst₀ e)=h)} where
  toFun e:=⟨e.val.val.val,e.val.property,(positiveParent e.val).1 e.property.1,e.property.2⟩
  invFun e:=
    let par:(coarse).graph.Edge:=(parent W G pick z hz fit pack p key flag k g).symm ⟨e.val,e.property.1⟩
    ⟨par,(positiveParent par).2 e.property.2.1,e.property.2.2⟩
  left_inv _:=rfl
  right_inv _:=rfl

include hz fit in
omit [Fintype I] in
/-- All positive raw rows originate on a paid old outgoing grain. Born rows
use the first chosen old demand cable, independently of the supply profile. -/
theorem anchor_positive {J₀ V₀ : Type} [Fintype J₀] [DecidableEq J₀] [Fintype V₀] [DecidableEq V₀]
    {k₀ a₀ : ℕ} {price₀ ε₀ : ℝ} (prior : GroupStage W G price₀ ε₀ J₀ V₀ k₀)
    (installed : prior.StateBounds S a₀) (e : raw) (pos : 0<bitsAt e) :
    0<prior.grainCount (anchor pick e) := by
  have rooted : ∀j:I,0<(N).width (pick (j,0)) :=fun j=> by rw [fit]; exact Nat.mul_pos (hz j) (by have:=G.paid; omega)
  have physical : 0<(N).width (anchor pick e) :=by
    rcases e with e|⟨j,s⟩|⟨j,s⟩
    · exact pos
    · exact rooted j
    · exact rooted j
  have eqn:=prior.grainCount_fit S installed (anchor pick e)
  by_contra! h
  have zero : prior.grainCount (anchor pick e)=0:=by omega
  simp [eqn,zero] at physical

variable {J₀ V₀ : Type} [Fintype J₀] [DecidableEq J₀] [Fintype V₀] [DecidableEq V₀]
    {k₀ a₀ : ℕ} {price₀ ε₀ : ℝ} (prior : GroupStage W G price₀ ε₀ J₀ V₀ k₀)
    (installed : prior.StateBounds S a₀)
local notation "rows" => localRows W G edge pair pick z hz fit pack p key flag k g q old picked affected site A S ready grain qp

include ready grain installed in
/-- Physical donor, old outgoing first grain, and old/arm/supply role are
computed on the actual raw parent. -/
def donorRows (h : Stage.Host J V stage) : Local C₀ h↪DescentRawCablePanel.Live prior pick where
  toFun t:=⟨(rows h t).val,anchor_positive W G pick z hz fit p S prior installed _ (rows h t).property.2.1⟩
  inj' _ _ eqn := (rows h).injective
    (Subtype.ext (congrArg (fun e : DescentRawCablePanel.Live prior pick => e.val) eqn))


end
end Hierarchy.DescentOrdinaryParentSupport

end OAI
