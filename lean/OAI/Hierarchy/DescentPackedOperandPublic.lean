import OAI.Hierarchy.DescentTicketFragment
import OAI.Hierarchy.DescentPackedOperand
import OAI.Hierarchy.DescentOrdinarySiblingSerial
import OAI.Hierarchy.DescentSharedCableExchange

namespace OAI
/-! # Surviving operands at the measured parallel serial of each actual endpoint -/
namespace Hierarchy.DescentPackedOperand.Public
open DescentColonies DescentSixParty DescentSharedCableNames DescentSIMDLookup
open scoped Classical Fin.CommRing
noncomputable section
variable {F P J V : Type} [Field F] [Fintype P] [Fintype J] [DecidableEq J] [Fintype V] [DecidableEq V]
  {d k i : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits} {G : PoweredGadget F} {price ε : ℝ}
  (A : GroupStage W G price ε J V k) (native : W.graph.Edge↪ℕ)
  (S : DescentCompiler.AtomSchedule) (ready : A.StateBounds S i) (names : Stage.Host J V k↪ℕ)

def endpoint (target : Bool) (x : Stage.Grain A) : Stage.Live A.degree A.cap :=
  if target then Stage.live A native S ready names (Stage.home A (W.graph.dst x.1)) (Exchange.targetPort A x)
  else Stage.live A native S ready names (Stage.home A (W.graph.src x.1)) (Exchange.sourcePort A x)

omit [Fintype P] in
theorem boundary (target : Bool) (x : Stage.Grain A) :
    (endpoint A native S ready names target x).wire.val=Siblings.shared A native x := by
  cases target with
  | false=>exact Siblings.live_serial A native S ready names x
  | true =>
    exact (congrArg Fin.val (Exchange.serial_same A native S ready names x)).symm.trans
      (Siblings.live_serial A native S ready names x)

def short {n b : ℕ} (x : Fin n) (fit : n≤2^b) : Cell b:=⟨x.val,x.isLt.trans_le fit⟩

omit [Fintype P] in
/-- Unsplit positive cables keep the first measured serial and original
within-cable chunk. Each containing finer grain is consecutive from that start. -/
theorem unsplit {b : ℕ} (e : W.graph.Edge) (j : Fin (A.grainCount e)) (target : Bool)
    (slotRoom : A.degree≤2^(b+2)) (wireRoom : A.cap≤2^(b+2)) (chunk grain : Cell (b+2)) :
    let first:=endpoint A native S ready names target ⟨e,⟨0,Nat.zero_lt_of_lt j.isLt⟩⟩
    let observed:=endpoint A native S ready names target ⟨e,j⟩
    resolve (fragment false (short first.neighbor slotRoom) (short first.wire wireRoom) chunk grain)=
      .cable first.neighbor.val first.wire.val chunk.val ∧
        first.wire.val+j.val=observed.wire.val := by
  dsimp only
  refine ⟨rfl,?_⟩
  rw [boundary,boundary,Siblings.within A native e j]

omit [Fintype P] in
/-- Replace the start of a public operand by the literal numeric digit of
the returned memory, preserving the full resolved key. -/
theorem measured_fragment {b : ℕ} (x : Stage.Grain A) (target : Bool)
    (peer chunk grain : Cell (b+2)) (marked : Bool) (v : ℕ)
    (measured : v=(endpoint A native S ready names target x).wire.val)
    (fits : A.cap≤2^(b+2)) :
    let start : Cell (b+2) := ⟨v,by rw [measured]; exact (endpoint A native S ready names target x).wire.isLt.trans_le fits⟩
    resolve (fragment marked peer start chunk grain)=
      resolve (fragment marked peer (short (endpoint A native S ready names target x).wire fits) chunk grain) := by
  cases measured
  rfl

end
end Hierarchy.DescentPackedOperand.Public

namespace Hierarchy.DescentOrdinarySiblingSerial
open DescentPackedOperand DescentSIMDLookup
open Computability.BorderVNP.Crossing DescentSixParty DescentSixParty.MarkedWorld DescentPhysicalOrder
open DescentHostDirectory DescentColonies DescentStageEdgeReceipt DescentPacking DescentCableDonorNames
open DescentSharedCableNames DescentSharedCableNames.Siblings
open scoped Classical BigOperators
noncomputable section
set_option maxHeartbeats 4000000
set_option quotPrecheck false
open private physicalBase physicalKey namedCoreAt namedSerial from OAI.Hierarchy.DescentOrdinarySiblingSerial

private def firstGrain {F P J V : Type} [Field F] [Fintype J] [DecidableEq J]
    [Fintype V] [DecidableEq V] {d age : ℕ} {bits : P → ℕ} {price ε : ℝ}
    (B : MarkedWorld F d P bits) (site : B.graph.Site ↪ ℕ) (rank : B.graph.Edge ↪ ℕ)
    {G : PoweredGadget F} (A : GroupStage (PhysicalRename.rankedWorld B site rank) G price ε J V age)
    (e : B.graph.Edge) (paid : namedCoreAt B site rank e) : Stage.Grain A :=
  ⟨@rename B.graph.Edge B.graph.finiteEdge rank e, ⟨0, A.quantum_positive _ paid⟩⟩

private theorem firstGrain_serial {F P J V : Type} [Field F] [Fintype J] [DecidableEq J]
    [Fintype V] [DecidableEq V] {d age : ℕ} {bits : P → ℕ} {price ε : ℝ}
    (B : MarkedWorld F d P bits) (site : B.graph.Site ↪ ℕ) (rank : B.graph.Edge ↪ ℕ)
    {G : PoweredGadget F} (A : GroupStage (PhysicalRename.rankedWorld B site rank) G price ε J V age)
    (e : B.graph.Edge) (paid : namedCoreAt B site rank e) :
    Siblings.shared A (@originalId B.graph.Edge B.graph.finiteEdge)
      (firstGrain B site rank A e paid) = namedSerial B site rank A e paid := rfl

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
local notation "startAt" => serial W G edge pair pick z hz fit pack p key flag k g q old picked affected site A
local notation "ord" => @originalId (baseWorld).graph.Edge (baseWorld).graph.finiteEdge

theorem operand_piece [Fintype P] {b : ℕ} (qpos : 0<q) (S : DescentCompiler.AtomSchedule) (ready : A.StateBounds S i)
    (names : Stage.Host J V age↪ℕ) (target : Bool) (u : {a : (coalesced (W.selected G pick z hz fit pack p) key flag k g).graph.Edge // a ∈ (coalesced (W.selected G pick z hz fit pack p) key flag k g).core})
    (chunk grain : Cell (b+2)) (positive : 0<grain.val) (within : chunk.val<rep u.val*grain.val)
    (slotRoom : A.degree≤2^(b+2)) (wireRoom : A.cap≤2^(b+2)) :
    let j : Fin (rep u.val):=⟨chunk.val/grain.val,(Nat.div_lt_iff_lt_mul positive).2 within⟩
    let zero : Fin (rep u.val):=⟨0,Nat.zero_lt_of_lt j.isLt⟩
    let fine (t : Fin (rep u.val)) : Stage.Grain A:=firstGrain baseWorld site edgeKey A (atPiece u t) (paid u t)
    let first:=Public.endpoint A ord S ready names target (fine zero)
    let actual:=Public.endpoint A ord S ready names target (fine j)
    resolve (Public.fragment true (Public.short actual.neighbor slotRoom) (Public.short first.wire wireRoom) chunk grain)=
      .cable actual.neighbor.val actual.wire.val (chunk.val%grain.val) := by
  let j : Fin (rep u.val):=⟨chunk.val/grain.val,(Nat.div_lt_iff_lt_mul positive).2 within⟩
  let fine (t : Fin (rep u.val)) : Stage.Grain A:=firstGrain baseWorld site edgeKey A (atPiece u t) (paid u t)
  let zero : Fin (rep u.val):=⟨0,Nat.zero_lt_of_lt j.isLt⟩
  let first:=Public.endpoint A ord S ready names target (fine zero)
  let actual:=Public.endpoint A ord S ready names target (fine j)
  change DescentPackedOperand.Key.cable _ (first.wire.val+j.val) _=DescentPackedOperand.Key.cable _ actual.wire.val _
  have measured (t : Fin (rep u.val)) :
      (Public.endpoint A ord S ready names target (fine t)).wire.val = startAt u t :=
    (Public.boundary A ord S ready names target (fine t)).trans
      (firstGrain_serial baseWorld site edgeKey A (atPiece u t) (paid u t))
  apply congrArg (fun ticket => DescentPackedOperand.Key.cable actual.neighbor.val ticket (chunk.val%grain.val))
  exact (congrArg (fun ticket => ticket + j.val) (measured zero)).trans
    ((add W G edge pair pick z hz fit pack p key flag k g q old picked affected site A qpos u j).symm.trans
      (measured j).symm)

end
end Hierarchy.DescentOrdinarySiblingSerial

end OAI
