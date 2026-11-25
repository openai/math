import OAI.Hierarchy.DescentNamedPublicBlock
import OAI.Hierarchy.DescentDatedPublicGrain

namespace OAI
/-! The exact split p-word at the native tape edge and the pointer calculated by
the chronological public solver use the same sibling and within-edge ordinal. -/
namespace Hierarchy.DescentOrdinarySiblingSerial
open DescentPackedOperand DescentSIMDLookup
open Computability.BorderVNP.Crossing DescentSixParty DescentSixParty.MarkedWorld DescentPhysicalOrder
open DescentHostDirectory DescentColonies DescentStageEdgeReceipt DescentPacking DescentCableDonorNames
open DescentSharedCableNames DescentSharedCableNames.Siblings
open scoped Classical BigOperators
noncomputable section
open private physicalBase physicalKey from OAI.Hierarchy.DescentOrdinarySiblingSerial
open private firstGrain from OAI.Hierarchy.DescentPackedOperandPublic

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
local notation "cut₀" => repetition_width W G pick z hz fit pack p key flag k g q old picked affected
variable {R unit : ℕ} {recipe : BitDescription (coalesced (W.selected G pick z hz fit pack p) key flag k g)}
variable (hp : 0<unit) (sh : WorldShape unit R recipe) (hq : 0<q) (dvd : unit∣q)
local notation "pre" => sh.pieces rep q cut₀ hp hq dvd
local notation "mapped" => SiteBooks.trans hp (SiteBooks.rename hp pre ls le')
  (SiteBooks.split hp sh rep q cut₀ hq dvd)

set_option maxHeartbeats 4000000 in
theorem named_operand_dated [Fintype P] {b : ℕ} (S : DescentCompiler.AtomSchedule) (ready : A.StateBounds S i)
    (names : Stage.Host J V age↪ℕ) (target : Bool) (v : (coalesced (W.selected G pick z hz fit pack p) key flag k g).graph.Site)
    (e : Incident (coarse).graph ((ls).symm v)) (mark : e.val∈(coarse).core) (chunk : Cell (b+2))
    (bounded : (chunk.val+1)*unit≤(coarse).graph.width e.val)
    (field : DescentDatedPublicGrain.amount S G.b i<2^(b+2))
    (cut : q=DescentDatedPublicGrain.amount S G.b i*unit)
    (slotRoom : A.degree≤2^(b+2)) (wireRoom : A.cap≤2^(b+2)) :
    let grain : Cell (b+2):=⟨DescentDatedPublicGrain.amount S G.b i,field⟩
    let block:=((mapped).atSite v).publicWord ⟨.inl e,chunk.val,bounded⟩
    let u : {a : (coarse).graph.Edge // a∈(coarse).core}:=⟨e.val,mark⟩
    ∃j : Fin (rep e.val), j.val=chunk.val/grain.val ∧
      block.cableNumber (nextWorld).graph v=some ((le') (atPiece u j),chunk.val%grain.val) ∧
      let fine (t : Fin (rep u.val)) : Stage.Grain A :=
        firstGrain baseWorld site edgeKey A (atPiece u t) (paid u t)
      let first:=Public.endpoint A (@originalId (baseWorld).graph.Edge (baseWorld).graph.finiteEdge) S ready names target (fine ⟨0,Nat.zero_lt_of_lt j.isLt⟩)
      let child:=Public.endpoint A (@originalId (baseWorld).graph.Edge (baseWorld).graph.finiteEdge) S ready names target (fine j)
      resolve (Public.fragment true (Public.short child.neighbor slotRoom) (Public.short first.wire wireRoom) chunk grain)=
        .cable child.neighbor.val child.wire.val (chunk.val%grain.val) := by
  intro grain block u
  have same : q/unit=grain.val := by
    exact (congrArg (fun n => n/unit) cut).trans (Nat.mul_div_cancel _ hp)
  obtain ⟨j,rawIndex,rawAddress⟩ :=
    named_split_block (W:=coarse) hp sh rep q cut₀ hq dvd ls le' v e chunk.val bounded mark
  have idx : j.val=chunk.val/grain.val :=
    rawIndex.trans (congrArg (fun n => chunk.val/n) same)
  have addr : block.cableNumber (nextWorld).graph v=some ((le') (atPiece u j),chunk.val%grain.val) :=
    rawAddress.trans (congrArg (fun n => some ((le') (atPiece u j),chunk.val%n)) same)
  have width:=cut₀ e.val mark
  have within : chunk.val<(rep u.val*q)/unit :=
    Nat.lt_of_succ_le ((Nat.le_div_iff_mul_le hp).2 (Nat.le_trans bounded (Nat.le_of_eq width)))
  refine ⟨j,idx,addr,?_⟩
  have hgrain : 0<grain.val := DescentDatedPublicGrain.amount_pos S G.base_pos i
  have lt : chunk.val<rep u.val*grain.val :=
    Nat.lt_of_lt_of_eq within (DescentDatedPublicGrain.cut_chunks q grain.val unit (rep u.val) hp cut)
  let physical : Fin (rep u.val) := ⟨chunk.val/grain.val,(Nat.div_lt_iff_lt_mul hgrain).2 lt⟩
  have equal : physical=j := Fin.ext idx.symm
  subst j
  exact operand_piece_dated W G edge pair pick z hz fit pack p key flag k g q old picked affected
    site A hq S ready names target u chunk unit hp field cut within slotRoom wireRoom

end
end Hierarchy.DescentOrdinarySiblingSerial

end OAI
