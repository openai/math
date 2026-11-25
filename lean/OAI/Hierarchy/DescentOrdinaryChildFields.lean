import OAI.Hierarchy.DescentOrdinaryParentBlocks
import OAI.Hierarchy.DescentNextSignedWindow

namespace OAI
/-! # All six actual signed fields of a normalized ordinary parent’s child window -/
namespace Hierarchy.DescentOrdinaryChildFields
open Computability.BorderVNP.Crossing DescentSixParty DescentSixParty.MarkedWorld DescentPhysicalOrder
open DescentHostDirectory DescentColonies DescentStageEdgeReceipt DescentPacking DescentCableDonorNames
open DescentSharedCableNames DescentSharedCableNames.Siblings DescentOrdinarySiblingSerial DescentParallelBase
open private DescentOrdinarySiblingSerial.physicalBase DescentOrdinarySiblingSerial.physicalKey
  from OAI.Hierarchy.DescentOrdinarySiblingSerial
open scoped Classical BigOperators
noncomputable section
set_option quotPrecheck false
set_option Elab.async false
set_option maxHeartbeats 1200000
private theorem endpoint_wire {F P J V : Type} [Field F] [Fintype J] [DecidableEq J]
    [Fintype V] [DecidableEq V] {d k i : ℕ} {bits : P → ℕ} {W : MarkedWorld F d P bits}
    {G : PoweredGadget F} {price ε : ℝ} (A : GroupStage W G price ε J V k)
    (native : W.graph.Edge ↪ ℕ) (S : DescentCompiler.AtomSchedule) (ready : A.StateBounds S i)
    (names : Stage.Host J V k ↪ ℕ) (side : Bool) (x : Stage.Grain A) :
    (DescentPackedOperand.Public.endpoint A native S ready names side x).wire.val =
      (Stage.source A native).serial (Stage.home A (W.graph.src x.1))
        (Stage.home A (W.graph.dst x.1)) (Stage.stream A native x) := by
  cases side with
  | false => exact Siblings.live_serial A native S ready names x
  | true =>
    let b := Stage.source A native
    let t := Stage.stream A native x
    have l : b.src t = Stage.home A (W.graph.src x.1) := by simp [b,t,Stage.source]
    have r : b.dst t = Stage.home A (W.graph.dst x.1) := by simp [b,t,Stage.source]
    have peer : b.peer (b.dst t) t = b.src t := by
      by_cases eqn : b.src t = b.dst t
      · exact (ite_eq_left eqn).trans eqn.symm
      · exact ite_eq_right eqn
    change b.serial (Stage.home A (W.graph.dst x.1)) (b.peer (Stage.home A (W.graph.dst x.1)) t) t = _
    rw [← l, ← r, peer]
    exact (b.both_ends t).symm

variable {F P I C H : Type} [Field F] [Fintype I] [DecidableEq H] {d : ℕ} {bits : P→ℕ}
variable (W : MarkedWorld F d P bits) (G : PoweredGadget F)
variable (edge : W.graph.Edge↪Fin (Fintype.card W.graph.Edge)) (pair : I≃Fin (Fintype.card I))
variable (pick : I×Fin 2↪W.graph.Edge) (z : I→ℕ) (hz : ∀i,0<z i)
variable (fit : ∀i s,W.graph.width (pick (i,s))=z i*G.b) (pack : W.graph.Site→C) (p : I→Profile G.C)
local notation "sel" => W.selected G pick z hz fit pack p
variable (key : (W.selected G pick z hz fit pack p).graph.Site↪Key H) (flag : H→Bool) (k g q : ℕ)
variable (old : ∀e∈W.core,q∣W.graph.width e) (picked : ∀j,pick j∈W.core) (affected : ∀i,q∣z i)
local notation "coarse" => coalesced sel key flag k g
local notation "world" => DescentOrdinarySiblingSerial.physicalBase W G pick z hz fit pack p key flag k g q old picked affected
variable (site : (coalesced (W.selected G pick z hz fit pack p) key flag k g).graph.Site ↪ ℕ)
local notation "sparse" => DescentOrdinarySiblingSerial.physicalKey W G edge pair pick z hz fit pack p key flag k g q old picked affected site
local notation "next" => PhysicalRename.rankedWorld world site sparse
variable {J V : Type} [Fintype J] [DecidableEq J] [Fintype V] [DecidableEq V] {stage : ℕ} {price ε : ℝ}
variable (A : GroupStage
    (PhysicalRename.rankedWorld
      (DescentOrdinarySiblingSerial.physicalBase W G pick z hz fit pack p key flag k g q old picked affected) site
      (DescentOrdinarySiblingSerial.physicalKey W G edge pair pick z hz fit pack p key flag k g q old picked affected site))
    G price ε J V stage)
local notation "ord" => originalId (next).graph.Edge
local notation "stream'" => Stage.stream A ord
local notation "B" => Stage.source A ord

open DescentOrdinaryParentBlocks DescentNextSignedWindow
variable {i : ℕ} (S : DescentCompiler.AtomSchedule) (ready : A.StateBounds S i) (names : Stage.Host J V stage↪ℕ) (qp:0<q)
local notation "C₀" => blocks W G edge pair pick z hz fit pack p key flag k g q old picked affected site A qp
local notation "wt" => weight W G edge pair pick z hz fit pack p key flag k g q old picked affected site A
local notation "grain" => emit W G edge pair pick z hz fit pack p key flag k g q old picked affected site A
local notation "first" => firstGrain W G edge pair pick z hz fit pack p key flag k g q old picked affected site A
local notation "terms" => Stage.measured A ord S ready
local notation "live" => DescentPackedOperand.Public.endpoint A ord S ready names
local notation "atSource" => fun e=>Stage.home A ((next).graph.src e)

theorem src_at (u : (coarse).graph.Edge) (j : Fin (wt u)) : atSource (grain ⟨u,j⟩).1=(C₀).src u:=by
  have actual:=(C₀).atSource u j
  change (B).src (stream' (grain ⟨u,j⟩))=_ at actual
  simpa only [Stage.source,Equiv.symm_apply_apply] using actual

theorem dst_at (u : (coarse).graph.Edge) (j : Fin (wt u)) : Stage.home A ((next).graph.dst (grain ⟨u,j⟩).1)=(C₀).dst u:=by
  have actual:=(C₀).atTarget u j
  change (B).dst (stream' (grain ⟨u,j⟩))=_ at actual
  simpa only [Stage.source,Equiv.symm_apply_apply] using actual

theorem serial (u : (coarse).graph.Edge) (j : Fin (wt u)) (side:Bool) :
    (live side (grain ⟨u,j⟩)).wire.val=(B).serial ((C₀).src u) ((C₀).dst u) ((C₀).order ⟨u,⟨0,Nat.zero_lt_of_lt j.isLt⟩⟩)+j.val:=by
  exact (endpoint_wire A ord S ready names side (grain ⟨u,j⟩)).trans <|
    (congrArg₂ (fun x y => (B).serial x y (stream' (grain ⟨u,j⟩)))
      (src_at W G edge pair pick z hz fit pack p key flag k g q old picked affected site A qp u j)
      (dst_at W G edge pair pick z hz fit pack p key flag k g q old picked affected site A qp u j)).trans (Incidence.parallel_child C₀ u j)

theorem metadata (u : (coarse).graph.Edge) (j : Fin (wt u)) (side:Bool) :
    (live side (grain ⟨u,j⟩)).within.val=(if u∈(coarse).core then 0 else j.val) ∧
    (live side (grain ⟨u,j⟩)).target=side ∧ (live side (grain ⟨u,j⟩)).markedOut=(decide (u∈(coarse).core) && !side) :=by
  have offset:=within_at W G edge pair pick z hz fit pack p key flag k g q old picked affected site A u j
  have core:=core_at W G edge pair pick z hz fit pack p key flag k g q old picked affected site A u j
  cases side <;> by_cases active:u∈(coarse).core <;>
    simp [DescentPackedOperand.Public.endpoint,Stage.live,Stage.recover,Stage.isMarkedOut,Stage.signedBit,Exchange.sourcePort,Exchange.targetPort,offset,core,active]
  all_goals
    simp only [active, ite_true, ite_false] at offset
    exact offset

/-- True first-grain source handle, including the remote view of a tether
spanning several finer grains. -/
theorem sourceWire (u : (coarse).graph.Edge) (j : Fin (wt u)) (side:Bool) :
    let x:=grain ⟨u,j⟩
    let home:=atSource x.1
    let member:Local C₀ home:=⟨u,Nat.zero_lt_of_lt j.isLt,Or.inl (src_at W G edge pair pick z hz fit pack p key flag k g q old picked affected site A qp u j).symm⟩
    (live side x).sourceWire.val=((B).position terms home (Incidence.candidate C₀ home member ⟨0,Nat.zero_lt_of_lt j.isLt⟩)).val+
      (if u∈(coarse).core then j.val else 0) :=by
  intro x home mem
  let pos:Stage.Positive A:=⟨x.1,Nat.zero_lt_of_lt x.2.isLt⟩
  have raw : (live side x).sourceWire=Stage.outgoing A ord S ready pos:=by cases side <;> rfl
  rw [raw]
  have where_ : Stage.firstAt A ord home pos rfl=Incidence.candidate C₀ home mem (first u j):=by
    apply Subtype.ext;change stream' ⟨x.1,⟨0,pos.property⟩⟩=stream' (grain ⟨u,first u j⟩)
    exact congrArg stream' (first_of_edge W G edge pair pick z hz fit pack p key flag k g q old picked affected site A u j).symm
  change ((B).position terms home (Stage.firstAt A ord home pos rfl)).val=_
  rw [where_]
  apply (Incidence.child C₀ home terms mem (first u j)).trans
  apply congrArg (_ + ·)
  by_cases marked:u∈(coarse).core <;> simp [DescentOrdinaryParentBlocks.firstGrain,marked]

end
end Hierarchy.DescentOrdinaryChildFields

end OAI
