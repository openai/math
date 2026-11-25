import OAI.Hierarchy.DescentOrdinaryParentAddress
import OAI.Hierarchy.DescentOrdinaryShortSlotOrder

namespace OAI
/-! # The first grain of each surviving parent has its original physical donor order. -/
namespace Hierarchy.DescentOrdinaryParentSupport
open DescentPacking.PackedMatch.Local
open Computability.BorderVNP.Crossing DescentSixParty DescentSixParty.MarkedWorld DescentPhysicalOrder
open DescentHostDirectory DescentColonies DescentStageEdgeReceipt DescentPacking DescentCableDonorNames
open DescentSharedCableNames DescentSharedCableNames.Siblings DescentOrdinarySiblingSerial DescentParallelBase
open private DescentOrdinarySiblingSerial.physicalBase DescentOrdinarySiblingSerial.physicalKey
  from OAI.Hierarchy.DescentOrdinarySiblingSerial
open GadgetNetwork
open scoped Classical BigOperators
noncomputable section
set_option quotPrecheck false
variable {F P I C J₀ V₀ : Type} [Field F] [Fintype I] [DecidableEq I] [Fintype J₀] [DecidableEq J₀] [Fintype V₀] [DecidableEq V₀] {d : ℕ} {bits : P→ℕ}
variable (W : MarkedWorld F d P bits) (G : PoweredGadget F)
variable (edge : W.graph.Edge↪Fin (Fintype.card W.graph.Edge)) (pair : I≃Fin (Fintype.card I))
variable (pick : I×Fin 2↪W.graph.Edge) (z : I→ℕ) (hz : ∀i,0<z i)
variable (fit : ∀i s,W.graph.width (pick (i,s))=z i*G.b) (pack : W.graph.Site→C) (p : I→Profile G.C)
local notation "sel" => W.selected G pick z hz fit pack p
variable (key : (W.selected G pick z hz fit pack p).graph.Site↪Key (J₀×V₀)) (flag : (J₀×V₀)→Bool) (k g q : ℕ)
variable (old : ∀e∈W.core,q∣W.graph.width e) (picked : ∀j,pick j∈W.core) (affected : ∀i,q∣z i)
local notation "coarse" => coalesced sel key flag k g
local notation "world" => DescentOrdinarySiblingSerial.physicalBase W G pick z hz fit pack p key flag k g q old picked affected
local notation "tape" => ordinary W G edge pair pick z hz fit pack p key flag k g q old picked affected
variable (site : (coalesced (W.selected G pick z hz fit pack p) key flag k g).graph.Site ↪ ℕ)
local notation "sparse" => DescentOrdinarySiblingSerial.physicalKey W G edge pair pick z hz fit pack p key flag k g q old picked affected site
variable {J V : Type} [Fintype J] [DecidableEq J] [Fintype V] [DecidableEq V] {stage : ℕ} {price ε : ℝ}
variable (A : GroupStage
    (PhysicalRename.rankedWorld
      (DescentOrdinarySiblingSerial.physicalBase W G pick z hz fit pack p key flag k g q old picked affected) site
      (DescentOrdinarySiblingSerial.physicalKey W G edge pair pick z hz fit pack p key flag k g q old picked affected site))
    G price ε J V stage)



variable {i a₀ : ℕ} {k₀ : ℕ} {price₀ ε₀ : ℝ} (S : DescentCompiler.AtomSchedule)
  (ready : A.StateBounds S i) (grain : A.z*G.b=q) (qp : 0<q)
  (prior : GroupStage W G price₀ ε₀ J₀ V₀ k₀) (installed : prior.StateBounds S a₀)
local notation "donors" => donorRows W G edge pair pick z hz fit pack p key flag k g q old picked affected site A S ready grain qp prior installed
local notation "C₀" => DescentOrdinaryParentBlocks.blocks W G edge pair pick z hz fit pack p key flag k g q old picked affected site A qp
variable (rank : (J₀×V₀)↪ℕ) (digits : J₀≃J×Block stage)
variable (ports : DescentRawCablePanel.Live prior pick→Option (Walk×Walk))
    (actual : ∀e : DescentRawCablePanel.Live prior pick,
      let first := newSite W.graph pick (bestLayout (branchWidth G z p)) pack
      let left := first (GadgetNetwork.source (I:=I) W.graph e.val)
      let right := first (GadgetNetwork.target W.graph pick e.val)
      (ports e=none → left=right) ∧ ∀walks, ports e=some walks →
        ParentIncidence.Actual (DescentPacking.PackedMatch.Local.Stage.rotor prior rank)
          (prior.pos (W.graph.src (anchor pick e.val))) walks (key left) (key right))
    (placed : ∀s : GadgetNetwork.Site (I:=I) W.graph,
      let first := newSite W.graph pick (bestLayout (branchWidth G z p)) pack s
      let endpoint := MarkedWorld.address (W.selected G pick z hz fit pack p) key flag k g first
      let cellPos := DescentSharedCableNames.Stage.home A (rename site endpoint)
      (cellPos.1.1,cellPos.2) = digits (splitKey endpoint.val).1)

variable {hosts groups : ℕ} (name : V₀↪Fin hosts) (groupName : J₀≃Fin groups)
local notation "addr" => parentAddress W G edge pair pick z hz fit pack p key flag k g q old picked affected site A S ready grain qp prior installed rank digits ports actual placed name groupName
local notation "heads" => DescentOrdinaryParentBlocks.head W G edge pair pick z hz fit pack p key flag k g q old picked affected site A
local notation "units" => DescentOrdinaryParentBlocks.head_width W G edge pair pick z hz fit pack p key flag k g q old picked affected site A S ready
local notation "anc" => ancestryTicket W G edge pick z hz fit pack p key flag k g q old picked affected
local notation "home₀" t => W.graph.src (anchor pick t)
variable (named : prior.SiteNamed (groupRank (groupName.toEmbedding.trans Fin.valEmbedding) (name.trans Fin.valEmbedding)))

include named actual placed in
omit [DecidableEq I] in
theorem parentAddress_head_order (h : Stage.Host J V stage) (e f : Local C₀ h)
    (common : (world).graph.src (heads e.val e.property.1)=(world).graph.src (heads f.val f.property.1)) :
    sparse (heads e.val e.property.1)<sparse (heads f.val f.property.1) ↔
      (addr h e).1<(addr h f).1 ∨ (addr h e).1=(addr h f).1 ∧ (addr h e).2<(addr h f).2 :=by
  let first := fun t : Local C₀ h=>heads t.val t.property.1
  have rawEq (t : Local C₀ h) : ((tape).owner (first t)).val.val=(donors h t).val :=by
    change ((tape).owner (heads t.val t.property.1)).val.val=t.val.val.val
    exact congrArg (fun u : (coarse).graph.Edge => u.val.val)
      (DescentOrdinaryParentBlocks.head_owner W G edge pair pick z hz fit pack p key flag k g q
        old picked affected site A t.val t.property.1)
  have owner (t : Local C₀ h) :
      ((anc) (first t)).donor=Fintype.equivFin W.graph.Site (home₀ (donors h t).val) :=
    congrArg (fun r=>Fintype.equivFin W.graph.Site (home₀ r)) (rawEq t)
  have cable (t : Local C₀ h) :
      ((anc) (first t)).old=edge (anchor pick (donors h t).val) :=
    congrArg (fun r=>edge (anchor pick r)) (rawEq t)
  have label (t : Local C₀ h) : ((anc) (first t)).rawRole=role (donors h t).val :=
    congrArg role (rawEq t)
  have zero (t : Local C₀ h) : ((anc) (first t)).child.val=0 :=
    DescentOrdinaryParentBlocks.head_offset W G edge pair pick z hz fit pack p key flag k g q old picked affected site A _ _
  have group := parent_group W G edge pair pick z hz fit pack p key flag k g q old picked affected site A S ready
    grain qp prior installed rank digits ports actual placed h
  have agree:DescentRawCablePanel.birthGroup prior pick (donors h e)=DescentRawCablePanel.birthGroup prior pick (donors h f) :=
    (group e).trans (group f).symm
  have short:=DescentRawCablePanel.shortSlot_order prior S installed edge name (groupName.toEmbedding.trans Fin.valEmbedding)
    named pick (donors h e) (donors h f) agree
  change (tape).sourceKey (world).graph.src site (world).graph.width (first e)<(tape).sourceKey (world).graph.src site (world).graph.width (first f) ↔ _
  rw [(tape).sourceKey_lt (world).graph.src site (world).graph.width (first e) (first f)
    (units _ _) (units _ _) common]
  change code ((anc) (first e))<code ((anc) (first f)) ↔ _
  rw [ticket_lt,owner,owner,cable,cable,label,label]
  rw [parentAddress_val W G edge pair pick z hz fit pack p key flag k g q old picked affected site A S ready
    grain qp prior installed rank digits ports actual placed name groupName h e,
    parentAddress_val W G edge pair pick z hz fit pack p key flag k g q old picked affected site A S ready
    grain qp prior installed rank digits ports actual placed name groupName h f]
  have site_id (x : W.graph.Site) :
      originalId W.graph.Site x = (Fintype.equivFin W.graph.Site x).val := rfl
  simp only [Fin.lt_def, Fin.ext_iff, site_id, zero, lt_self_iff_false, and_false, or_false] at short ⊢
  exact short.symm

end
end Hierarchy.DescentOrdinaryParentSupport

end OAI
