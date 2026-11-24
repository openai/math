import OAI.Computability.VPVNP.PairShrinkRoleBankHistogramStep
import OAI.Computability.VPVNP.PairSimulationMapScanAcceptance

/-!
# Histogram of the physical shrinking bank

The successful scan of a site's resident jobs adds the sum of their label
multiplicities to each counter in the private histogram.
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

open private rowBase from OAI.Computability.VPVNP.PairShrinkRoleBankHistogramStep
attribute [local instance] rowBase
set_option allowUnsafeReducibility true in
attribute [local reducible] rowBase
set_option allowUnsafeReducibility true in
attribute [local reducible] Compression.PackingData.shrinkTermLayout
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

local notation "regions" => TerminalLayout.privateRegions (slotDegree S) n site.rowEnd
  (Fintype.card B.Entry)
local notation "jobs" => ShrinkSiteBank.jobs (g := g) (w := w) B i X sel site.workspace
  site.positions site.blocks site.cur site.bounds n site.rowEnd site.older site.later v old parent
local notation "row" => MapWitness.rowEquiv (a := a i) (g := g) X side v
open private jobPublic from OAI.Computability.VPVNP.PairShrinkRoleCanonicalReader
local notation:max "pubAt" q:max => jobPublic site old parent q
set_option quotPrecheck false in
local notation:max "bin" l:max => (((regions).histBase + (ord l).val : ℕ) : Word w)


attribute [local irreducible] canonicalRow canonicalBank ResidentMapLoop.Exact.scan
  MapWitness.input MapWitness.names

set_option quotPrecheck false in
local notation:max "countAt" j:max l:max =>
  ((((MapWitness.names B (MapWitness.input (g := g) B i X sel v old parent hidden
    (row j))).map (List.map (ord ∘ Sum.inl))).getD []).count (ord l))

set_option maxHeartbeats 2200000 in
-- The scan and row count use the same selected old, parent and hidden assignments.
/-- The complete bank adds the sum of its physical row counts for each parameter ordinal. -/
theorem canonicalBank_counts (baseline : Word w → Word w)
    (packets : ∀ q, (jobs q).Packets packetEnd baseline)
    {T : IncidenceDirectory w} {origin : ℕ}
    (headers : ∀ j : Fin (residents).length, let q := row j
      (jobs q).OldPublished (ShrinkCallABI.operands (slotDegree S)) (pubAt q)
        (rowOrdinalWord (w := w) (a := a i) (g := g) X side v j) site.mem site.level T origin)
    (node : Word w) {saved out : Scratch w n} {es : List (Event w)}
    (got : scan node bank saved = some (es, out)) (l : B.Entry) :
    rawScratch out (bin l) = rawScratch saved (bin l) +
      ((∑ j : Fin (residents).length, countAt j l : ℕ) : Word w) := by
  let rows := canonicalRow site ord old parent hidden
  let delta (j : Fin (residents).length) : ℕ := countAt j l
  have run : scan node (List.ofFn rows) saved = some (es, out) := by
    rw [show List.ofFn rows = bank from canonicalRows_eq site ord old parent hidden]
    exact got
  have step (j : Fin (residents).length) (s : Scratch w n) (log : List (Event w))
      (next : Scratch w n) (hit : rows j node s = some (log, next)) :
      rawScratch next (bin l) = rawScratch s (bin l) + (delta j : Word w) :=
    canonicalRow_count (g := g) (packetEnd := packetEnd) (T := T) (origin := origin)
      site ord old parent hidden j baseline (packets (row j)) (headers j) node hit l
  have total := scan_ofFn_add node rows (fun s => rawScratch s (bin l))
    (fun j => (delta j : Word w)) step run
  simpa only [← Nat.cast_sum] using total

end PairSimulation.ShrinkRole

end VPVNP
end Computability
end OAI
