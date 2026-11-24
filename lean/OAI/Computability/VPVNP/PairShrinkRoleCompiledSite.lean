import OAI.Computability.VPVNP.PairShrinkCanonicalSite
import OAI.Computability.VPVNP.PairShrinkRolePackedHidden
import OAI.Computability.VPVNP.PairShrinkRoleChildDescriptor
import OAI.Computability.VPVNP.PairShrinkRolePackedRow
import OAI.Computability.VPVNP.PairSimulationShrinkMapCompiledSource

/-!
# The physical data of a shrinking site in the selected compressor image

The site reads its own term rows and owner tables from the compiled payload.
The child descriptor uses the selected pass's ordered fiber. Its private
hidden and matrix operands share the same post-stack reservation.
-/

namespace OAI
namespace Computability
namespace VPVNP

noncomputable section

namespace PairSimulation.ShrinkRole

open BurstRAM Compression Compression.ShrinkMotif CompressorRecords DescriptorSpace
open ShrinkBlockInputs LocalHistory ShrinkMapImage.Registers MapResidentRows
open scoped Fin.CommRing

variable {K A : Type} [_root_.Field K] [CommRing A] {S : BlockSchedule K} (B : S.Templates)
  (f : B.Entry → A) (hf : B.IsSolution f) (i : Fin S.steps) {g w : ℕ}
  (X : State (a i) (packingLaneBits (a i) g)) (sel : SelectedScore.Selection B X)
  (v : Site X) (pub : Fin 11 → Word w) (workspace : Word w)
  (positions blocks cur n rowEnd older later limit levels : ℕ) (phy : Memory w)
  (payload : CompiledResident.ShrinkPayload B workspace positions blocks n cur i X sel phy)

local notation "D" => BlockProgram.layout B workspace.val positions blocks
local notation "t" => Fintype.card B.Entry
local notation "R" => TerminalLayout.privateRegions (slotDegree S) n rowEnd t
local notation "side" => SelectedFinish.chosen B X sel
local notation "levelAt" => (levelStart D cur : Word w)
local notation "tab" => (fun j : Fin 6 => tableBase D cur j)
local notation "termAt" => ShrinkInput.termHead (w := w) X (tab 0)

private noncomputable abbrev selectedSource :=
  (mapRowSource_compiled B workspace positions blocks n cur i X sel payload).choose

local notation "sourceAt" => selectedSource B i X sel workspace positions blocks cur n phy payload

variable (width : MapConstants.widthThreshold B.shrink ≤ w)
  (fits : ∀ m, canonicalFits B i X sel (w := w) (Fintype.card B.Entry) n rowEnd older limit m)

/-- The concrete parser site on the packed level. Its operand banks are the
ones read by the compressor, locator, and selected party map code. -/
def compiledSite : CanonicalSite B i X sel v w n t where
  workspace := workspace
  positions := positions
  blocks := blocks
  cur := cur
  bounds := payload.bounds
  rowEnd := rowEnd
  older := older
  later := later
  limit := limit
  fits := fits
  mem := phy
  level := levelAt
  term := termAt
  source := sourceAt
  width := width
  publicData := pub
  levels := levels
  passIndex := cur
  incidence := packedIncidence D w cur (X.positions * 2 ^ a i)
  descriptor := PackedChildren.descriptor levelAt (oldSites B f hf i X sel v)
  hiddenArgs := PackedHidden.arguments B i X sel workspace positions blocks cur n R v
  seed := fun _ _ => ⟨0, Nat.two_pow_pos _⟩

local notation "site" => compiledSite B f hf i X sel v pub workspace positions blocks cur n
  rowEnd older later limit levels phy payload width fits

/-- The matrix owner directory starts at table five of this chronological level. -/
theorem compiledSite_first : (site).source.first = tab 5 :=
  (mapRowSource_compiled B workspace positions blocks n cur i X sel payload).choose_spec.1

/-- All map reads of this source lie in the retained producing level. -/
theorem compiledSite_inLevel : (site).source.InLevel D cur :=
  (mapRowSource_compiled B workspace positions blocks n cur i X sel payload).choose_spec.2.1

/-- The four header values read by the map loop are present at their
actual offsets in the terminal vertex's memory. -/
theorem compiledSite_published :
    let p := (ShrinkResidentLayout.layout X (site).source.first).params (a i) true w
    MapResidentInputs.Published phy levelAt (p 3) (p 5) termAt 10 := by
  rw [compiledSite_first B f hf i X sel v pub workspace positions blocks cur n
    rowEnd older later limit levels phy payload width fits]
  exact (mapRowSource_compiled B workspace positions blocks n cur i X sel payload).choose_spec.2.2

/-- The exclusive stop pointer of the selected map row fits the word. -/
theorem compiledSite_mapRoom :
    ShrinkVertexImage.firstMap B i (site).source v + (order X side v).length < 2 ^ w := by
  have bound := (directory_fit X (site).source.first v (site).source.fit).2
  rw [MapResidentRows.length_eq]
  exact bound

end PairSimulation.ShrinkRole

end

end VPVNP
end Computability
end OAI
