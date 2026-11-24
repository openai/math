import OAI.Computability.VPVNP.PairVertexRootEntry

/-! # The selected argument region and role bank in the current site memory -/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.TerminalProgram

open BurstRAM PrivateRAM LiveProgram LiveProgram.PairStages.Group.Auxiliary
open Compression CompressorRecords LocalHistory NodeArguments TraversalRows TraversalRoles
open scoped Fin.CommRing

variable {k K : Type} [_root_.Field k] [CommRing K] {S : BlockSchedule k}
    (B : S.Templates) (f : B.Entry → K) (hf : B.IsSolution f)
    {lanes : ℕ} (T : ℕ) (hT : T * S.laneBits ≤ lanes)
    (X : State (S.degreeExponent 0) lanes) (z : (B.execute f hf T hT X).Choices)
    (G : PairStages.Group) (n labels : ℕ) (baseBits laneBits : ℕ) (ord : ℕ)

local notation "pub" => terminalOperands G
local notation "hdr" => vertexHeader G
local notation "tags" => selected B f hf T hT X z
variable {layout : DescriptorSpace.Layout}
local notation "base" => DescriptorSpace.endAddress layout
local notation "Y" => StateExecution.finalState (B.execute f hf T hT X) z
local notation "width" => State.totalWidth (Y)
local notation "size" => tagWords B.recordLimit (tags)
local notation "offset" => (((size) + (width) : ℕ) : Word G.w)
local notation "area" => TerminalLayout.privateRegions (slotDegree S) n ((base) + (size)) labels
variable {calendar reference : Memory G.w} (m : Memory G.w)
    {bits : Fin ((B.execute f hf T hT X).finalState z).totalWidth → Bool}
    {tab : Fin layout.shape.tables}
    (pack : VertexPacked G layout B.recordLimit (selected B f hf T hT X z)
      ((B.execute f hf T hT X).finalState z).totalWidth)
    (entry : VertexEntry B f hf T hT X z layout tab baseBits laneBits (terminalOperands G)
      calendar reference bits)
    (later : LinkedVertexMemory G reference ord m)

include pack entry later in
/-- Both role offsets and the complete private geometry remain those of
the selected physical table after earlier vertices have flushed. -/
theorem VertexEntry.role_layout (length : (pub 6).val = n) (count : (pub 9).val = labels) :
    NativeFrame.fromHeader (slotDegree S) pub hdr m = (area) ∧
    m (hdr + 14).val = (offset) ∧
    Reads G.w (m) ((offset).val) B.recordLimit (base) (tags) := by
  have rowEq : (size) = words B.recordLimit (selectedLayers B f hf T hT X z) :=
    congrArg (words B.recordLimit) (selected_layers B f hf T hT X z)
  have room := pack.room
  have bound := pack.arena
  have addr : (hdr + 14).val = (hdr).val + 14 := by
    change ((hdr).val + 14 % (2 ^ G.w)) % (2 ^ G.w) = (hdr).val + 14
    rw [Nat.mod_eq_of_lt (by omega : 14 < 2 ^ G.w), Nat.mod_eq_of_lt (by omega)]
  have role := pack.header later 14 (by decide) (by decide)
  change m (hdr + 14).val = reference (hdr + 14).val at role
  refine ⟨?_, role.trans ?_, ?_⟩
  · rw [rowEq]
    exact entry.selected_regions pack later n labels length count
  · rw [addr, rowEq]
    exact entry.offset
  · rw [Fin.val_natCast, Nat.mod_eq_of_lt (by omega : (size) + (width) < 2 ^ G.w)]
    apply pack.roleWords later
    rw [rowEq]
    exact entry.roles

end PairSimulation.TerminalProgram

end VPVNP
end Computability
end OAI
