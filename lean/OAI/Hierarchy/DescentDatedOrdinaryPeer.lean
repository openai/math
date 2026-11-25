import OAI.Hierarchy.DescentDatedNamedBlock
import OAI.Hierarchy.DescentOrdinarySignedMeta

namespace OAI
/-! # Peer slots of ordinary public fragments and their signed resident parents -/
namespace Hierarchy.DescentPackedOperand.Public
open DescentSixParty DescentColonies DescentSharedCableNames
open scoped Classical
noncomputable section
variable {F P J V : Type} [Field F] [Fintype J] [DecidableEq J] [Fintype V] [DecidableEq V]
  {d k i : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits} {G : PoweredGadget F} {price ε : ℝ}
  (A : GroupStage W G price ε J V k) (native : W.graph.Edge↪ℕ)
  (S : DescentCompiler.AtomSchedule) (ready : A.StateBounds S i) (names : Stage.Host J V k↪ℕ)
local notation "B" => Stage.source A native

private theorem peer_slot {l r : Stage.Host J V k} (x : ↥((B).incident l)) (y : ↥((B).incident r))
    (same : l=r) (src : (B).src x.val=(B).src y.val) (dst : (B).dst x.val=(B).dst y.val) :
    (Stage.neighbors A native names).slot l x=(Stage.neighbors A native names).slot r y := by
  subst r
  apply ((Stage.neighbors A native names).same l _ _).2
  simp only [Ends.peer,src,dst]

/-- Both signed views give equal peer ordinals for two grains with the same
ordered endpoint hosts, including when those hosts coincide. -/
theorem endpoint_neighbor (side : Bool) (x y : Stage.Grain A)
    (src : Stage.home A (W.graph.src x.1)=Stage.home A (W.graph.src y.1))
    (dst : Stage.home A (W.graph.dst x.1)=Stage.home A (W.graph.dst y.1)) :
    (endpoint A native S ready names side x).neighbor=(endpoint A native S ready names side y).neighbor := by
  let stream:=Stage.stream A native
  have src' : (B).src (stream x)=(B).src (stream y):=by
    simpa only [Stage.source,stream,Equiv.symm_apply_apply] using src
  have dst' : (B).dst (stream x)=(B).dst (stream y):=by
    simpa only [Stage.source,stream,Equiv.symm_apply_apply] using dst
  cases side with
  | false =>
    exact peer_slot A native names
      (Stage.ofPort A native _ (Exchange.sourcePort A x))
      (Stage.ofPort A native _ (Exchange.sourcePort A y)) src src' dst'
  | true =>
    exact peer_slot A native names
      (Stage.ofPort A native _ (Exchange.targetPort A x))
      (Stage.ofPort A native _ (Exchange.targetPort A y)) dst src' dst'
end
end Hierarchy.DescentPackedOperand.Public

namespace Hierarchy.DescentResetWindowFields
open DescentSixParty DescentColonies DescentSharedCableNames DescentParallelBase DescentNextSignedWindow
open scoped Classical
noncomputable section
variable {F P V J E : Type} [Field F] [Fintype J] [DecidableEq J] [Fintype V] [DecidableEq V]
  [Fintype E] {d k i : ℕ} {bits : P → ℕ} {W : MarkedWorld F d P bits}
  {G : PoweredGadget F} {price ε : ℝ}
  (A : GroupStage W G price ε J V k) (native : W.graph.Edge ↪ ℕ)
  (S : DescentCompiler.AtomSchedule) (ready : A.StateBounds S i) (names : Stage.Host J V k ↪ ℕ)
  (C : Blocks (Stage.source A native) E) (marked : E → Prop) (emit : Emission A native C marked)

omit [Fintype E] in
/-- Read a resident from either incident face at its own host. The physical
peer is precisely the public peer at the supplied child of the emitted block. -/
theorem resident_endpoint_neighbor (h : Stage.Host J V k) (f : Roster.Face A native C h)
    (t : GrainPorts.Unit A native C h) (parent : f.val.1=t.val.1.1) :
    neighbor A native S ready names C h f=
      (DescentPackedOperand.Public.endpoint A native S ready names t.val.2 (emit.units t.val.1)).neighbor := by
  rw [DescentOrdinarySignedMeta.neighbor_same_parent A native S ready names C h f
    (Roster.face A native C h t) parent,←near A native S ready names C h t,GrainPorts.at_end]
  change (DescentPackedOperand.Public.endpoint A native S ready names t.val.2
    ((Stage.stream A native).symm (C.order t.val.1))).neighbor=_
  rw [emit.order_eq t.val.1.1 t.val.1.2,Equiv.symm_apply_apply]

omit [Fintype E] in
/-- Peer value at the actual committed resident face and child ordinal. -/
theorem resident_child_neighbor (h : Stage.Host J V k) (edge : Local C h) (j : Fin (C.count edge.val))
    (side : Bool) (here : (if side then C.dst edge.val else C.src edge.val)=h) :
    neighbor A native S ready names C h (DescentOrdinarySignedMeta.residentFace A native C h edge)=
      (DescentPackedOperand.Public.endpoint A native S ready names side (emit.units ⟨edge.val,j⟩)).neighbor :=
  resident_endpoint_neighbor A native S ready names C marked emit h _ ⟨(⟨edge.val,j⟩,side),here⟩
    (DescentOrdinarySignedMeta.residentFace_edge A native C h edge)
end
end Hierarchy.DescentResetWindowFields

namespace Hierarchy.DescentOrdinarySiblingSerial
open DescentPackedOperand DescentSIMDLookup
open Computability.BorderVNP.Crossing DescentSixParty DescentSixParty.MarkedWorld DescentPhysicalOrder
open DescentHostDirectory DescentColonies DescentStageEdgeReceipt DescentPacking DescentCableDonorNames
open DescentSharedCableNames DescentSharedCableNames.Siblings
open scoped Classical BigOperators
noncomputable section
set_option quotPrecheck false
open private physicalBase physicalKey from OAI.Hierarchy.DescentOrdinarySiblingSerial
variable {F P I C H : Type} [Field F] [Fintype I] [DecidableEq H] {d : ℕ} {bits : P→ℕ}
variable (W : MarkedWorld F d P bits) (G : PoweredGadget F)
variable (edge : W.graph.Edge↪Fin (Fintype.card W.graph.Edge)) (pair : I≃Fin (Fintype.card I))
variable (pick : I×Fin 2↪W.graph.Edge) (z : I→ℕ) (hz : ∀i,0<z i)
variable (fit : ∀i s,W.graph.width (pick (i,s))=z i*G.b) (pack : W.graph.Site→C) (p : I→Profile G.C)
variable (key : (W.selected G pick z hz fit pack p).graph.Site↪DescentHostDirectory.Key H) (flag : H→Bool) (k g q : ℕ)
variable (old : ∀e∈W.core,q∣W.graph.width e) (picked : ∀j,pick j∈W.core) (affected : ∀i,q∣z i)
variable (site : (coalesced (W.selected G pick z hz fit pack p) key flag k g).graph.Site ↪ ℕ)
variable {J V : Type} [Fintype J] [DecidableEq J] [Fintype V] [DecidableEq V] {age i : ℕ} {price ε : ℝ}
variable (A : GroupStage (PhysicalRename.rankedWorld
  (physicalBase W G pick z hz fit pack p key flag k g q old picked affected) site
  (physicalKey W G edge pair pick z hz fit pack p key flag k g q old picked affected site)) G price ε J V age)
local notation "baseWorld" => physicalBase W G pick z hz fit pack p key flag k g q old picked affected
local notation "edgeKey" => physicalKey W G edge pair pick z hz fit pack p key flag k g q old picked affected site
local notation "rep" => repetitions W G pick z hz fit pack p key flag k g q
local notation "atPiece" => piece W G pick z hz fit pack p key flag k g q old picked affected
local notation "paid" => core_piece W G edge pair pick z hz fit pack p key flag k g q old picked affected site

local notation "coarse" => coalesced (W.selected G pick z hz fit pack p) key flag k g
local notation "ls" => rename site
local notation "le'" => rename edgeKey
local notation "nextWorld" => PhysicalRename.rankedWorld baseWorld site edgeKey
open DescentKernelHistory DescentBundleHistory DescentOperandStateBanks
local notation "ord" => @originalId (baseWorld).graph.Edge (baseWorld).graph.finiteEdge
local notation "active" => fun (u : {a : (coarse).graph.Edge // a∈(coarse).core}) (j : Fin (rep u.val)) => le' (atPiece u j)

/-- All normalized split pieces of a named positive edge retain its source and
target through the physical renaming, so the live peer digit is constant. -/
theorem sibling_neighbor (S : DescentCompiler.AtomSchedule) (ready : A.StateBounds S i)
    (names : Stage.Host J V age↪ℕ) (side : Bool) (u : {e : (coarse).graph.Edge // e∈(coarse).core})
    (a b : Fin (rep u.val)) :
    (Public.endpoint A ord S ready names side ⟨active u a,⟨0,A.quantum_positive _ (paid u a)⟩⟩).neighbor=
      (Public.endpoint A ord S ready names side ⟨active u b,⟨0,A.quantum_positive _ (paid u b)⟩⟩).neighbor := by
  let x:=atPiece u a
  let y:=atPiece u b
  have src : (baseWorld).graph.src x=(baseWorld).graph.src y:=rfl
  have dst : (baseWorld).graph.dst x=(baseWorld).graph.dst y:=rfl
  apply Public.endpoint_neighbor
  · apply congrArg (Stage.home A)
    change (PhysicalRename.graph (baseWorld).graph ls le').src (le' x)=(PhysicalRename.graph (baseWorld).graph ls le').src (le' y)
    exact (PhysicalRename.src _ _ _ x).trans ((congrArg ls src).trans (PhysicalRename.src _ _ _ y).symm)
  · apply congrArg (Stage.home A)
    change (PhysicalRename.graph (baseWorld).graph ls le').dst (le' x)=(PhysicalRename.graph (baseWorld).graph ls le').dst (le' y)
    exact (PhysicalRename.dst _ _ _ x).trans ((congrArg ls dst).trans (PhysicalRename.dst _ _ _ y).symm)

end
end Hierarchy.DescentOrdinarySiblingSerial

end OAI
