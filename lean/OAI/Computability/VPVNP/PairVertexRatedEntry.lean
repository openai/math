import OAI.Computability.VPVNP.PairTerminalPackedPrefix

/-! # The final ordinal stored by the actual selected terminal prefix -/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.TerminalProgram

open BurstRAM PrivateRAM Compression CompressorRecords DescriptorSpace LocalHistory TerminalLink
  TraversalRows
open scoped Fin.CommRing

variable {w : ℕ} {k K : Type*} [_root_.Field k] [CommRing K] {S : BlockSchedule k}
    {B : S.Templates} {κ : B.Entry → K} {hκ : B.IsSolution κ} {lanes T : ℕ}
    {hT : T * S.laneBits ≤ lanes} {X : State (S.degreeExponent 0) lanes} {z : (B.execute κ hκ T hT
      X).Choices}
    {L : Layout} {tab : Fin L.shape.tables} {baseBits laneBits : ℕ} {pub : Fin 11 → Word w}
    {calendar vertex : Memory w}
local notation "Y" => StateExecution.finalState (B.execute κ hκ T hT X) z
local notation "layers" => selectedLayers B κ hκ T hT X z

/-- The active site's closing ordinal is read from header word seven of
the post-scan memory. -/
theorem VertexEntry.storedOrdinal {bits : Fin (Y).totalWidth → Bool}
    (entry : VertexEntry B κ hκ T hT X z L tab baseBits laneBits pub calendar vertex bits)
    (room : (header pub).val + 32 ≤ 2 ^ w) :
    vertex (header pub + 7).val = ((siteOrder (Y)).length : Word w) := by
  let source := TerminalBootstrap.fromState L (List.dropLast (layers)) B.recordLimit baseBits
    laneBits (Y) tab
  have raw := entry.headers (7 : Fin 21) (by decide) (by decide) (by decide)
  change vertex ((header pub).val + 7) = (source.sites : Word w) at raw
  have h7 : (7 : Word w).val = 7 := Nat.mod_eq_of_lt (show (7 : ℕ) < 2 ^ w by omega)
  have atSeven : (header pub + 7).val = (header pub).val + 7 := by
    rw [Fin.val_add,h7,Nat.mod_eq_of_lt (by omega)]
  have sites : source.sites = (Y).positions := TerminalBootstrap.fromState_sites ..
  have order : (siteOrder (Y)).length = (Y).positions := by
    change (siteOrder (Y)).length = Fintype.card (Y).network.Site
    simpa only [Fintype.card_fin] using Fintype.card_congr (siteOrder (Y)).entries
  rw [atSeven,raw,sites,order]

end PairSimulation.TerminalProgram

end VPVNP
end Computability
end OAI
