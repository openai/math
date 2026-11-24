import OAI.Computability.VPVNP.CompressorRecordRefreshArgumentAddress
import OAI.Computability.VPVNP.CompressorRefreshTraversalChild
import OAI.Computability.VPVNP.CompressorShrinkHistoryDirectory
import OAI.Computability.VPVNP.PairNodeChildPackets
import OAI.Computability.VPVNP.PairSimulationMapResidentRows

/-! # The ordered child addresses stored at a selected shrinking site -/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.ShrinkRole

open BurstRAM Compression CompressorRecords LocalHistory TraversalRows TraversalRoles
open NodeArguments.ChildScan
open scoped Fin.CommRing
open private successor_rows from OAI.Computability.VPVNP.CompressorRefreshTraversalChild
open private next_number from OAI.Computability.VPVNP.CompressorRecordsShrinkPreimages

variable {K R : Type*} [_root_.Field K] [CommRing R] {S : BlockSchedule K}
  (B : S.Templates) (f : B.Entry → R) (hf : B.IsSolution f)
  {lanes : ℕ} (T : ℕ) (hT : T * S.laneBits ≤ lanes)
  (initial : State (S.degreeExponent 0) lanes) (z : (B.execute f hf T hT initial).Choices)
  (i : Fin S.steps) {g : ℕ}
  (Z : State (S.degreeExponent i.castSucc) (packingLaneBits (S.degreeExponent i.castSucc) g))
  (sel : Z.ShrinkSelection B.shrink) (bits : List Bool)

/-- The old sites at a packed site, in the order consumed by the kernel's child reader. -/
noncomputable abbrev oldSites (site : MapResidentRows.Site Z) : List Z.network.Site :=
  List.ofFn fun j => ((((shrinkPassReaders B f hf i rfl Z).order sel).children site).entries j).val

/-- The successor's argument ordinal is the packed-site index used by the resident map rows. -/
@[simp] theorem shrinkSiteOrdinal_eq (site : MapResidentRows.Site Z) :
    PortRefresh.ArgumentAddress.siteOrdinal (Z.shrinkNext B.shrink (S.shrink i) sel) site =
      (MapResidentRows.siteIndex Z site).val := by
  let Y := Z.shrinkNext B.shrink (S.shrink i) sel
  apply Eq.trans _ (next_number Z B.shrink (S.shrink i) sel (packedSiteEquiv.symm site))
  change (Y.baseIndex site.1).val * 2 ^ g + (bitWordFinEquiv g site.2).val =
    (bitWordFinEquiv g site.2).val + 2 ^ g * (Y.baseIndex site.1).val
  ac_rfl

local notation "level" => shrinkLevel B f hf i Z sel bits
local notation "passes" => executeLevels B f hf T hT initial z
local notation "tags" => TraversalRoles.selected B f hf T hT initial z

set_option maxHeartbeats 2000000 in
-- Identifying the child list reduces the scheduled pass's dependent site and order transports.
private theorem packedRow {w cap older later : ℕ} {mem : Memory w}
    (rows : (levelLayer B f hf level).Rows w mem cap older later) (site : MapResidentRows.Site Z) :
    let addr := address cap later (MapResidentRows.siteIndex Z site).val
    DFS.Row mem addr (addr + 2) ((oldSites B f hf i Z sel site).map fun u =>
      (childNode Z older cap u : Word w)) := by
  let out := siteOrder (Z.shrinkNext B.shrink (S.shrink i) sel)
  let idx := out.entries.symm site
  have ord : idx.val = (MapResidentRows.siteIndex Z site).val :=
    next_number Z B.shrink (S.shrink i) sel (packedSiteEquiv.symm site)
  have row := (rows idx).2
  change DFS.Row mem (address cap later idx.val) (address cap later idx.val + 2)
    ((List.ofFn fun j => ((siteOrder Z).entries.symm
      ((((shrinkPassReaders B f hf i rfl Z).order sel).children
        (out.entries idx)).entries j).val).val).map
      fun id => (address cap older id : Word w)) at row
  rw [show out.entries idx = site from Equiv.apply_symm_apply .., ord] at row
  simpa only [oldSites, List.map_ofFn, Function.comp_def, childNode, sitePointers] using row

/-- The physical DFS row contains precisely the ordered old-site fiber of this occurrence.
Each child word points into the preceding selected layer at that site's ordinal. -/
theorem selectedChildRow (stage : Fin (passes).length)
    (occurrence : (passes)[stage] = level) {w base : ℕ} {mem : Memory w}
    (rows : AllRows w mem B.recordLimit base base (selectedLayers B f hf T hT initial z))
    (site : MapResidentRows.Site Z) :
    let older := layerBase B.recordLimit base tags stage.val
    let later := layerBase B.recordLimit base tags (stage.val + 1)
    let addr := address B.recordLimit later (MapResidentRows.siteIndex Z site).val
    DFS.Row mem addr (addr + 2) ((oldSites B f hf i Z sel site).map fun u =>
      (childNode Z older B.recordLimit u : Word w)) := by
  have all : AllRows w mem B.recordLimit base base ((tags).map TaggedLayer.layer) := by
    rwa [selected_layers]
  have bound : stage.val + 1 < (tags).length := by simp [TraversalRoles.selected]
  have atLevel : (tags)[stage.val + 1].layer = levelLayer B f hf level := by
    simp only [TraversalRoles.selected, List.getElem_cons_succ, List.getElem_map]
    exact congrArg (levelLayer B f hf) occurrence
  have atRow := successor_rows all stage.val bound
  rw [atLevel] at atRow
  exact packedRow B f hf i Z sel bits atRow site

end PairSimulation.ShrinkRole

end VPVNP
end Computability
end OAI
