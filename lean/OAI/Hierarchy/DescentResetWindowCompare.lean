import OAI.Hierarchy.DescentOrderedGrainPrecedence
import OAI.Hierarchy.DescentResetParentWindows

namespace OAI
/-! # Original reset ordinals and source-aware predecessor comparisons -/
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


def rawHead (e : (coarse).graph.Edge) (live : 0<wt e) : (world).graph.Edge :=
  if core:e∈(coarse).core then piece' ⟨e,core⟩ ⟨0,by simpa [weight,core] using live⟩
  else .inl ⟨e,core⟩
local notation "head'" => rawHead B

private theorem head_core (e : (coarse).graph.Edge) (live : 0<wt e) (yes : e∈(coarse).core) :
    head' e live = piece' ⟨e,yes⟩ ⟨0,by simpa only [weight,dite_eq_left yes] using live⟩ := dite_eq_left yes

private theorem head_free (e : (coarse).graph.Edge) (live : 0<wt e) (no : e∉(coarse).core) :
    head' e live = .inl ⟨e,no⟩ := dite_eq_right no

theorem head_emit (e : (coarse).graph.Edge) (live : 0<wt e) :
    (grains ⟨e,⟨0,live⟩⟩).1=renameEdge (head' e live) ∧ (grains ⟨e,⟨0,live⟩⟩).2.val=0 := by
  by_cases yes : e∈(coarse).core
  · let j : Fin ((cnt) e) := ⟨0,by simpa only [weight,dite_eq_left yes] using live⟩
    let edge := renameEdge (piece' ⟨e,yes⟩ j)
    have positive := (A).quantum_positive edge (core_piece B ⟨e,yes⟩ j)
    have sent : grains ⟨e,⟨0,live⟩⟩ = ⟨edge,⟨0,positive⟩⟩ := by
      unfold emit
      exact dite_eq_left yes
    rw [sent,head_core B e live yes]
    exact ⟨rfl,rfl⟩
  · let edge := renameEdge (Sum.inl ⟨e,yes⟩)
    have positive : 0<(A).grainCount edge := by simpa only [weight,dite_eq_right yes] using live
    have sent : grains ⟨e,⟨0,live⟩⟩ = ⟨edge,⟨0,positive⟩⟩ := by
      unfold emit
      exact dite_eq_right yes
    rw [sent,head_free B e live yes]
    exact ⟨rfl,rfl⟩

theorem head_fields (e : (coarse).graph.Edge) (live : 0<wt e) :
    (tape).owner (head' e live)=e ∧ (tape).offset (head' e live)=0 ∧
    (world).graph.src (head' e live)=(coarse).graph.src e ∧
    (world).graph.dst (head' e live)=(coarse).graph.dst e := by
  by_cases core:e∈(coarse).core
  · rw [head_core B e live core]
    exact ⟨rfl,rfl,rfl,rfl⟩
  · rw [head_free B e live core]
    exact ⟨rfl,rfl,rfl,rfl⟩

theorem head_index (e : (coarse).graph.Edge) (live : 0<wt e) :
    index (head' e live)=ProtocolRAMPortRanks.«prefix» (tape).span (tape).rank e := by
  have headFields:=head_fields B e live
  have read:=(tape).read (head' e live)
  simpa only [headFields.1,headFields.2.1,Nat.add_zero] using! read

theorem span_pos (e : (coarse).graph.Edge) (live : 0<wt e) : 0<(tape).span e := by
  have facts:=head_fields B e live
  have fits:=(tape).offsetFits (head' e live)
  simpa only [facts.1,facts.2.1] using fits

theorem prefix_lt (e f : (coarse).graph.Edge) (he : 0<wt e) (hf : 0<wt f) :
    index (head' e he) < index (head' f hf) ↔ (tape).rank e<(tape).rank f := by
  rw [head_index,head_index]
  exact DescentOrderedGrainPrecedence.first (tape).span (tape).rank e f
    (span_pos B e he) (span_pos B f hf)

/-- Compare two raw parent heads by the same short source geometry and actual
physical installed slot, regardless of which receiver makes the comparison. -/
theorem first_before (e f : (coarse).graph.Edge) (he : 0<wt e) (hf : 0<wt f) :
    (blocks B).first e<(blocks B).first f ↔
      rawSite ((coarse).graph.src e)<rawSite ((coarse).graph.src f) ∨
      rawSite ((coarse).graph.src e)=rawSite ((coarse).graph.src f) ∧
        ((Z).installedResetOrdinal T vertexCode birth e).val<((Z).installedResetOrdinal T vertexCode birth f).val := by
  let x:=grains ⟨e,⟨0,he⟩⟩
  let y:=grains ⟨f,⟨0,hf⟩⟩
  have hx:=head_emit B e he
  have hy:=head_emit B f hf
  have headPos (z : Stage.Grain A) (zero : z.2.val=0) :
      (stream' z).val = ProtocolRAMPortRanks.«prefix» (A).grainCount ord z.1 := by
    change ProtocolRAMPortRanks.«prefix» (A).grainCount ord z.1 + z.2.val = _
    rw [zero,Nat.add_zero]
  have stream_lt : (stream' x).val<(stream' y).val ↔ ord x.1<ord y.1 := by
    rw [headPos x hx.2,headPos y hy.2]
    exact DescentOrderedGrainPrecedence.first (A).grainCount ord x.1 y.1
      (Nat.zero_lt_of_lt x.2.isLt) (Nat.zero_lt_of_lt y.2.isLt)
  change (if _ : 0<wt e then _ else 0)<(if _ : 0<wt f then _ else 0) ↔ _
  rw [dite_eq_left he,dite_eq_left hf]
  change (stream' x).val<(stream' y).val ↔ _
  rw [stream_lt,show x.1=renameEdge (head' e he) from hx.1,show y.1=renameEdge (head' f hf) from hy.1,
    names_lt,DescentResetLocalOrder.code_val,DescentResetLocalOrder.code_val]
  have fits (a : (world).graph.Edge) : index a<(Finset.univ.sup index)+1 :=
    Nat.lt_succ_of_le (Finset.le_sup (Finset.mem_univ a))
  rw [DescentCableDonorNames.digit_lt (fits _) (fits _),(head_fields B e he).2.2.1,
    (head_fields B f hf).2.2.1,prefix_lt]; rfl

end
end Hierarchy.DescentSixParty.ClosedReset.Window

end OAI
