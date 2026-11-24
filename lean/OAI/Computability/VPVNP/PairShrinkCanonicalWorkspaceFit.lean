import OAI.Computability.VPVNP.PairShrinkCallABI
import OAI.Computability.VPVNP.PairShrinkSelectedCapacity

/-!
# Workspace capacity at a scheduled shrinking motif

The terminal row end determines the private argument arena and histogram.
The hidden fields begin after the scalar stacks and use the square stride
computed by the handoff. These are the addresses used by the canonical job
for every party of the motif.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.ShrinkRole

open Compression Compression.ShrinkMotif CompressorRecords CursorBounds MotifConversion
open ShrinkCallCapacity ShrinkCallFields

variable {K : Type} [_root_.Field K] {S : BlockSchedule K} (B : S.Templates) (i : Fin S.steps)
variable {g : ℕ} (X : State (S.degreeExponent i.castSucc)
  (packingLaneBits (S.degreeExponent i.castSucc) g)) (sel : X.ShrinkSelection B.shrink)

open Classical in
/-- Workspace capacity for the motif at the old level's published row base. -/
noncomputable abbrev canonicalFits {w : ℕ} (t n rowEnd older limit : ℕ)
    (m : X.packingData.Motif) : Prop :=
  let R := TerminalLayout.privateRegions (slotDegree S) n rowEnd (Fintype.card B.Entry)
  let demand := X.packingData.shrinkDemandWidths X.shrinkNumber X.packingWidth m
  Fits (w := w) (n := n) (limit := limit) (u := repetitions B.shrink demand) (t := t)
    B.shrink demand (sel m).val
    (ShrinkCallHeader.scratch X (ShrinkCallABI.hiddenBase R n) (n ^ 2) R.histBase)
    (ShrinkMotifOrder.stateNumber X m).val
    (ShrinkCallHeader.cdBase X m R.arguments older (B.recordLimit + 2))

/-- The selected level's capacity applies at the canonical row end. In
particular this specializes the capacity supplied by
`ShrinkCallCapacity.eventually_packed_occurrence` for the physical level. -/
theorem canonicalFits_of_selected {b n firstRow rowWords older limit : ℕ}
    (m : X.packingData.Motif)
    (fit : SelectedFits X B sel m
      (NativeFrame.regions (slotDegree S) n firstRow rowWords (Fintype.card B.Entry))
      b n limit older (B.recordLimit + 2)) :
    canonicalFits B i X sel (w := wordBits b n) (Fintype.card B.Entry) n
      (firstRow + rowWords) older limit m := by
  simpa only [canonicalFits, SelectedFits, pow_two, ShrinkCallABI.hiddenBase, mapBase,
    TerminalLayout.privateRegions, NativeFrame.regions, NodeArguments.frameStride] using fit

end PairSimulation.ShrinkRole

end VPVNP
end Computability
end OAI
