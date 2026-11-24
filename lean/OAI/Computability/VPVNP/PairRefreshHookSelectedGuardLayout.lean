import OAI.Computability.VPVNP.PairRefreshHookFrozenSite
import OAI.Computability.VPVNP.PairRefreshGuardLayout

/-!
# Guard addresses of a selected refresh job

At each linked site, the old and new level pointers still locate the two
packed graphs. The parent row and its tagged copy lie in the reserved
traversal arena below the controller's terminal header.
-/

namespace OAI
namespace Computability
namespace VPVNP

noncomputable section

namespace PairSimulation.RefreshHook.SelectedPublished

open BurstRAM Compression Compression.Refresh CompressorRecords PortRefresh NewSlots
open LocalHistory TraversalRoles TraversalRows DescriptorSpace TerminalProgram
open LiveProgram.PairStages LiveProgram.PairStages.Group.Auxiliary
open TraversalControllerInputs
open scoped Fin.CommRing

variable {k : Type} [_root_.Field k] {S : BlockSchedule k} (B : S.Templates)
  {A : Type*} [CommRing A] (f : B.Entry → A) (hf : B.IsSolution f)
  {n l g hist : ℕ} (G : LiveProgram.PairStages.Group) (workspace : BurstRAM.Word G.w)
  (positions blocks : ℕ)
  (budget : blocks * S.laneBits ≤ l) (initial : State (S.degreeExponent 0) l)
  (branch : (B.execute f hf blocks budget initial).Choices)
  (X : State S.portExponent (S.portExponent + g))
  (choice : DyadicRefreshChoice X S.graph (Nat.two_pow_pos _)
    (And.left (S.port_bound.connected_and_pos S.port_order)) B.refresh)
  (record : List Bool) (port : (X.Base × BitWord g) × Fin (2 ^ S.portExponent))
  (stage : Fin (executeLevels B f hf blocks budget initial branch).length)
  (occurrence : (executeLevels B f hf blocks budget initial branch)[stage] =
    RefreshPlacement.traversalLevel f hf X choice record)

local notation "layout" => BlockProgram.layout B workspace.val positions blocks
local notation "levels" => executeLevels B f hf blocks budget initial branch
local notation "tags" => TraversalRoles.selected B f hf blocks budget initial branch
local notation "cap" => BlockSchedule.Templates.recordLimit B
local notation "first" => endAddress layout
local notation "rowEnd" => first + tagWords cap tags
local notation "ord" => Fin.val (sites X.baseIndex (bitWordFinEquiv g) port)
local notation "child" => address cap (layerBase cap first tags stage.val) ord
local notation "parent" => address cap (layerBase cap first tags (stage.val + 1)) ord
local notation "width" =>
  State.totalWidth (StateExecution.finalState (B.execute f hf blocks budget initial) branch)

local notation "pub" => terminalOperands G
local notation "H" => Fin.val (TerminalLink.header pub)
local notation "size" => tagWords cap tags

include occurrence in
/-- The real selected calendar and the physical linked memory provide all source
address ranges required by the refresh dispatcher. -/
theorem guard_at_site {tab : Fin (layout).shape.tables} {baseBits laneBits ordinal : ℕ}
    {calendar vertex current : Memory G.w} {wireBits : Fin width → Bool}
    (entry : VertexEntry B f hf blocks budget initial branch layout tab baseBits laneBits
      pub calendar vertex wireBits)
    (history : SelectedPayloadHistory.Past B f hf layout
      (CompiledResident.payload B f hf workspace positions blocks n) levels calendar)
    (packed : VertexPacked G layout cap tags width)
    (frame : LinkedVertexMemory G vertex ordinal current)
    (fits : TraversalPlan.Room B X choice port (slotDegree S) n rowEnd child parent hist G.w)
    (prev next : Fin (layout).levels) (prevIndex : prev.val = stage.val)
    (nextIndex : next.val = stage.val + 1) :
    let R := ofSelected B n hist G.w workspace.val positions blocks X choice port stage.val
      tags width fits
    Site.GuardLayout B R pub current workspace.val positions blocks prev next := by
  let R := ofSelected B n hist G.w workspace.val positions blocks X choice port stage.val
    tags width fits
  change Site.GuardLayout B R pub current workspace.val positions blocks prev next
  have live : (levels).length < (layout).levels :=
    (executeLevels_length B f hf blocks budget initial branch).trans_lt (by
      rw [BlockProgram.actual_level_count]
      omega)
  obtain ⟨kept, high⟩ := packed.traversal_frames frame
  have heads (i : ℕ) (hi : i ≤ (levels).length) :=
    entry.site_level_head live (by change 28 ≤ 54; decide) kept high i hi
  have data := RefreshHookRetained.ofPast B f hf workspace positions blocks n X choice history
    stage record occurrence
  have arena : first + 2 * size + width ≤ H := packed.arena
  have below : first ≤ H := by omega
  have top : first ≤ parent := (Nat.le_add_right ..).trans (Nat.le_add_right ..)
  have inside : parent < first + size := fits.parentBound
  have minSize : 2 ≤ size := by
    have pos : 0 < size := by omega
    change 0 < (cap + 2) * (((tags).map TaggedLayer.layer).map Layer.count).sum at pos
    have nonempty := (mul_pos_iff_of_pos_left (by omega : 0 < cap + 2)).mp pos
    exact (by omega : 2 ≤ cap + 2).trans (Nat.le_mul_of_pos_right _ nonempty)
  have tagsLength : (tags).length = (levels).length + 1 := by simp [TraversalRoles.selected]
  refine ⟨data.size, below, packed.room, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [prevIndex]
    exact (heads stage.val stage.isLt.le).2
  · rw [nextIndex]
    exact (heads (stage.val + 1) stage.isLt).2
  · rw [prevIndex]; rfl
  · rw [prevIndex]; rfl
  · rw [nextIndex]; rfl
  · intro i _ hi
    change i ≤ stage.val + 1 + ((tags).length - 1 - (stage.val + 1)) at hi
    have inLevels : i ≤ (levels).length := by rw [tagsLength] at hi; omega
    have nextFits := levelStart_mono layout (inLevels.trans_lt live)
    have stride : 14 < levelWords layout := by
      change 14 < 66 + _ + _
      omega
    have fieldBefore : levelStart layout i + 14 < endAddress layout := by
      change levelStart layout (i + 1) ≤ endAddress layout at nextFits
      have shift : levelStart layout (i + 1) = levelStart layout i + levelWords layout := by
        simp only [levelStart, Nat.succ_mul, Nat.add_assoc]
      rw [shift] at nextFits
      omega
    rw [Fin.val_add, (heads i inLevels).2]
    have small : (14 : BurstRAM.Word G.w).val ≤ 14 := Nat.mod_le ..
    exact (Nat.mod_le ..).trans_lt
      ((Nat.add_le_add_left small _).trans_lt (fieldBefore.trans_le below))
  · change parent + 1 < H
    omega
  · change parent + 2 < H
    omega
  · change (Fin.ofNat (2 ^ G.w) (size + width) + Fin.ofNat (2 ^ G.w) parent).val < H
    rw [Fin.val_add, Fin.val_ofNat, Fin.val_ofNat]
    exact (Nat.mod_le ..).trans_lt ((Nat.add_le_add (Nat.mod_le ..) (Nat.mod_le ..)).trans_lt
      (by omega))

end PairSimulation.RefreshHook.SelectedPublished

end

end VPVNP
end Computability
end OAI
