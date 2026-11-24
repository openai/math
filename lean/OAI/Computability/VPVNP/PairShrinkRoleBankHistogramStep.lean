import OAI.Computability.VPVNP.PairShrinkRoleCanonicalReader
import OAI.Computability.VPVNP.PairShrinkMapRowJobCount

/-!
# Histogram increment at one physical resident of a shrinking site

An old assignment, a parent half-wire and the hidden fields determine the row
independently of its later use in a local kernel witness.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.ShrinkRole

open BurstRAM DFS Compression Compression.PackingData Compression.ShrinkMotif NetworkKernel
open CompressorRecords CompressorRecords.ShrinkBlockInputs CompressorRecords.ShrinkSlots
open ShrinkMapImage.Registers ResidentMapLoop.Exact MapResidentRows NodeArguments
open scoped Fin.CommRing

variable {K : Type} [_root_.Field K] {S : BlockSchedule K} {B : S.Templates}
  {i : Fin S.steps} {g n w t packetEnd : ℕ}
  {X : State (a i) (packingLaneBits (a i) g)}
  {sel : X.ShrinkSelection B.shrink} {v : Site X}

open private acceptanceBase from OAI.Computability.VPVNP.PairShrinkRoleMapActions
private noncomputable local instance rowBase : DecidableEq X.Base := acceptanceBase i X
set_option allowUnsafeReducibility true in
attribute [local reducible] rowBase
set_option allowUnsafeReducibility true in
attribute [local reducible] Compression.PackingData.shrinkTermLayout ShrinkVertexImage.gatherFamily
set_option allowUnsafeReducibility true in
attribute [local irreducible] Compression.ShrinkEnergy.chosenLayout

local notation "side" => selectedLayout X B.shrink sel
variable (site : CanonicalSite B i X sel v w n t) (ord : B.Entry ≃ Fin t)
  (old : Placed (X.packingData.shrinkPlace (selectedLayout X B.shrink sel) ∘
    X.packingInputIso.site.symm) X.network.Half v)
  (parent : (X.shrinkNext B.shrink (S.shrink i) sel).network.Half v)
  (hidden : Placed (X.packingData.shrinkInternalOwner (selectedLayout X B.shrink sel))
    (internalLabel (ShrinkPreparedCall.width B.shrink X sel) (selectedLayout X B.shrink sel)) v)

local notation "bank" => canonicalBank site ord parent old hidden
local notation "residents" => order (a := a i) (g := g) X side v

/-- The selected resident's action in the actual physical row order. -/
noncomputable def canonicalRow (j : Fin (residents).length) : Action w n :=
  (bank)[j.val]'(by simpa only [canonicalBank, MapWitness.actions, List.length_ofFn] using j.isLt)

/-- Collecting all indexed actions recovers the whole resident bank. -/
theorem canonicalRows_eq : List.ofFn (canonicalRow site ord old parent hidden) = bank := by
  apply List.ext_getElem
  · simp only [List.length_ofFn, canonicalBank, MapWitness.actions]
  · intro k h₁ h₂
    rw [List.getElem_ofFn]
    rfl


local notation "regions" => TerminalLayout.privateRegions (slotDegree S) n site.rowEnd
  (Fintype.card B.Entry)
local notation "jobs" => ShrinkSiteBank.jobs (g := g) (w := w) B i X sel site.workspace
  site.positions site.blocks site.cur site.bounds n site.rowEnd site.older site.later v old parent
local notation "row" => MapWitness.rowEquiv (a := a i) (g := g) X side v
open private jobPublic from OAI.Computability.VPVNP.PairShrinkRoleCanonicalReader
local notation:max "pubAt" q:max => jobPublic site old parent q
set_option quotPrecheck false in
local notation:max "bin" l:max => (((regions).histBase + (ord l).val : ℕ) : Word w)

set_option allowUnsafeReducibility true in
attribute [local irreducible] rowAction ShrinkPartyNative.Job.entryInput
  ShrinkPartyNative.Job.mapWorkspace MapWitness.input

private theorem ordinal_names (I : LocalHistory.EntryInput B.shrink) :
    MapHandlerOperand.names (ShrinkVertexImage.matrixFamily B ord i) demandMass_pos I =
      (MapWitness.names B I).map (List.map (ord ∘ Sum.inl)) := rfl

set_option maxHeartbeats 2200000 in
-- Identify the actual row's dependent job, resident input and fitted workspace.
/-- One successful resident action adds the multiplicity of its scheduled local names. -/
theorem canonicalRow_count (j : Fin (residents).length) (baseline : Word w → Word w)
    (packets : (jobs (row j)).Packets packetEnd baseline)
    {T : IncidenceDirectory w} {origin : ℕ}
    (header : (jobs (row j)).OldPublished (ShrinkCallABI.operands (slotDegree S))
      (jobPublic site old parent (row j)) (rowOrdinalWord (w := w) (a := a i) (g := g) X side v j)
      site.mem site.level T origin)
    (node : Word w) {saved out : Scratch w n} {es : List (Event w)}
    (got : canonicalRow site ord old parent hidden j node saved = some (es, out)) (l : B.Entry) :
    rawScratch out (bin l) = rawScratch saved (bin l) +
      ((((MapWitness.names B (MapWitness.input (g := g) B i X sel v old parent hidden
        (row j))).map (List.map (ord ∘ Sum.inl))).getD []).count (ord l) : Word w) := by
  let q := row j
  have labels : t ≤ (regions).histWords := by
    change t ≤ Fintype.card B.Entry
    simpa only [Fintype.card_fin] using (Fintype.card_congr ord).ge
  have floor : n ≤ (regions).histBase := Nat.le_add_right ..
  have histEnd := ShrinkResidentMemory.histogram_before_hidden regions n t labels
  unfold canonicalRow canonicalBank MapWitness.actions at got
  erw [List.getElem_ofFn] at got
  dsimp only [MapWitness.jobInput, id] at got
  have count := ShrinkPartyNative.Job.routed_histogram (g := g) (w := w) (n := n)
    (endAddr := n) (limit := site.limit) (t := t) (packetEnd := packetEnd)
    («side» := side) (T := T) (origin := origin) (baseline := baseline) (events := es) (out := out)
    B (⇑ord) i X sel q.1.1 q.1.2 (jobs q) (q.2.symm ▸ hidden) (site.fits q.1.1)
    site.width (pubAt q) site.mem v site.level site.term site.source j saved packets
    floor histEnd header got (ord l)
  erw [ordinal_names, ShrinkSiteBank.input_eq] at count
  exact count

end PairSimulation.ShrinkRole

end VPVNP
end Computability
end OAI
