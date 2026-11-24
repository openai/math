import OAI.Computability.VPVNP.CompressorRecordsShrinkHistory
import OAI.Computability.VPVNP.CompressorShrinkSelectedPlan

/-!
# Workspace for the shrinking history's two resident directories

The absorbed-field records start after the chosen placement's child rows.
The map records follow them. Each stores one owner word and one ordered
row word per occurrence, and one counter per packed site.
-/

namespace OAI
namespace Computability
namespace VPVNP

noncomputable section

namespace CompressorRecords.ShrinkResidentLayout

open BurstRAM Compression Compression.PackingData PrimedStackRAM
open PairSimulation.LocalHistory ShrinkHistoryRows
open scoped Fin.CommRing Classical

/-- Occurrences per motif in a resident scan, four for absorbed fields and six for party maps. -/
def radix (maps : Bool) := if maps then 6 else 4

/-- Number of occurrence slots reserved per packed site in the selected field or map directory,
accounting for degree, pieces and occurrences per motif. -/
def rowCapacity (a : ℕ) (maps : Bool) := radix maps*(2^a*pieceCount (2^a) (Shrink.colors a))

/-- Dimensions and starting address for two consecutive resident directories, each with an
owner column, per-site counts and ordered preimage rows. -/
structure Layout where
  /-- Number of packed output sites, each with its own count and preimage row in both
  directories. -/
  sites : ℕ
  /-- Number of shrinking motifs whose field and party-map occurrences must be assigned to
  owners. -/
  motifs : ℕ
  /-- Base of the hidden-field owner column, the first address of the combined resident
  workspace. -/
  first : ℕ

namespace Layout

/-- Number of occurrences in the selected directory, the motif count times four hidden fields
or six party maps. -/
def size (L : Layout) (maps : Bool) := L.motifs*radix maps

/-- Start of the selected owner column. The hidden-field column comes first and the map column
follows the complete hidden-field directory. -/
def owner (L : Layout) (maps : Bool) :=
  if maps then L.first + L.size false + L.sites + L.size false else L.first

/-- Start of the per-site counts immediately following the selected occurrence-owner column. -/
def counts (L : Layout) (maps : Bool) := L.owner maps + L.size maps

/-- Start of the selected preimage rows, following one count word per packed site. -/
def rows (L : Layout) (maps : Bool) := L.counts maps + L.sites

/-- First free address following the party-map preimage rows and hence both resident
directories. -/
def endAddr (L : Layout) := L.rows true + L.size true

/-- Six public collector operands in order, occurrence count, owner base, site count, count
base, row capacity and row base. -/
def params (L : Layout) (a : ℕ) (maps : Bool) (w : ℕ) : Fin 6 → Word w :=
  ![(L.size maps : Word w),(L.owner maps : Word w),(L.sites : Word w),
    (L.counts maps : Word w),(rowCapacity a maps : Word w),(L.rows maps : Word w)]

theorem ranges (L : Layout) (maps : Bool) : L.first ≤ L.owner maps ∧
    L.owner maps + L.size maps = L.counts maps ∧ L.counts maps+L.sites = L.rows maps ∧
    L.rows maps+L.size maps ≤ L.endAddr := by
  cases maps <;> dsimp [endAddr,rows,counts,owner] <;> omega

end Layout

variable {a g w : ℕ} (X : State a (packingLaneBits a g))

/-- Instantiate the resident workspace at `first` using the actual number of packed sites and
the motif order of the shrinking state. -/
def layout (first : ℕ) : Layout := ⟨ShrinkPreimages.newCount X,(shrinkMotifOrder X).length,first⟩

theorem size_eq_rows (first : ℕ) (maps : Bool) :
    (layout X first).size maps = (layout X first).sites * rowCapacity a maps := by
  have h := Fintype.card_congr (ShrinkMotifOrder.stateNumber X)
  rw [Fintype.card_fin] at h
  change Fintype.card X.packingData.Motif * radix maps = ShrinkPreimages.newCount X * _
  rw [h]
  unfold rowCapacity
  ring

/-- No index is truncated when the next free address fits the word. -/
theorem frame (first : ℕ) (maps : Bool) (fit : (layout X first).endAddr < 2^w) :
    let L := layout X first
    let p := L.params a maps w
    RowRegions p ∧ (p 0).val = L.size maps ∧ (p 1).val = L.owner maps ∧
      (p 2).val = L.sites ∧ (p 3).val = L.counts maps ∧ (p 4).val = rowCapacity a maps ∧
      (p 5).val = L.rows maps := by
  intro L p
  change L.endAddr < 2^w at fit
  obtain ⟨_,hc,hr,hend⟩ := L.ranges maps
  have dim := size_eq_rows X first maps
  change L.size maps = L.sites*rowCapacity a maps at dim
  have hpos : 0 < L.sites := Nat.mul_pos Fintype.card_pos (Nat.mul_pos (Nat.two_pow_pos _) (Nat.two_pow_pos _))
  have hcap := Nat.le_mul_of_pos_left (rowCapacity a maps) hpos
  have ok0 : (p 0).val = L.size maps := Nat.mod_eq_of_lt (by omega)
  have ok1 : (p 1).val = L.owner maps := Nat.mod_eq_of_lt (by omega)
  have ok2 : (p 2).val = L.sites := Nat.mod_eq_of_lt (by omega)
  have ok3 : (p 3).val = L.counts maps := Nat.mod_eq_of_lt (by omega)
  have ok4 : (p 4).val = rowCapacity a maps := Nat.mod_eq_of_lt (by omega)
  have ok5 : (p 5).val = L.rows maps := Nat.mod_eq_of_lt (by omega)
  exact ⟨⟨by rw [ok1,ok0,ok3,hc],by rw [ok3,ok2,ok5,hr],
    by rw [ok5,ok2,ok4,←dim]; exact hend.trans fit.le⟩,ok0,ok1,ok2,ok3,ok4,ok5⟩

theorem hidden_id (m : X.packingData.Motif) (t : Fin 4) :
    ((hiddenOrder X).entries.symm (m,t)).val = (ShrinkMotifOrder.stateNumber X m).val * 4 + t.val := by
  change t.val + 4*(ShrinkMotifOrder.stateNumber X m).val = _
  omega

theorem map_id (m : X.packingData.Motif) (t : Fin 6) :
    ((mapOrder X).entries.symm (m,t)).val = (ShrinkMotifOrder.stateNumber X m).val * 6 + t.val := by
  change t.val + 6*(ShrinkMotifOrder.stateNumber X m).val = _
  omega

theorem hidden_build (first : ℕ) (fit : (layout X first).endAddr < 2^w) (side : Bool)
    (mem : Memory w) :
    let L := layout X first
    let p := L.params a false w
    let old := hiddenOrder X
    let next := packedOrder X
    let place := X.packingData.shrinkInternalOwner side
    (∀ i : Word w, i<p 0 → ownerAt p mem i = encodedPlacement old.entries.symm next.entries.symm place i) →
    ∃ cs rs, let mid := after mem (eventLog cs)
      let out := after mid (eventLog rs)
      runSegment ((template SliceRAM.clearOps 0).instantiate w (fun _ => p 3)).program 8 (some 0) mem
        (List.replicate L.sites []) = some cs ∧
      runSegment ((template collectPreimage 3).instantiate w p).program 23 (some 0) mid
        (List.replicate (L.size false) []) = some rs ∧
      Directory old next place p out ∧ cs.length=L.sites ∧ rs.length=L.size false ∧
      (∀ r ∈ cs, r.probes=1 ∧ r.events.length+1=8) ∧ (∀ r ∈ rs, r.probes=4 ∧ r.events.length+1=23) ∧
      (∀ j, OutsidePreimageWrites p j → out j = mem j) := by
  intro L p old next place owners
  obtain ⟨regions,ho,_,hn,_,hc,_⟩ := frame X first false fit
  exact build old next place p regions ho hn (fun v => (hidden_count X side v).le.trans hc.symm.le) mem owners

theorem map_build (first : ℕ) (fit : (layout X first).endAddr < 2^w) (side : Bool)
    (mem : Memory w) :
    let L := layout X first
    let p := L.params a true w
    let old := mapOrder X
    let next := packedOrder X
    let place := fun (e : X.packingData.Motif × Fin 6) => X.packingData.shrinkPartySite side e.1 e.2
    (∀ i : Word w, i<p 0 → ownerAt p mem i = encodedPlacement old.entries.symm next.entries.symm place i) →
    ∃ cs rs, let mid := after mem (eventLog cs)
      let out := after mid (eventLog rs)
      runSegment ((template SliceRAM.clearOps 0).instantiate w (fun _ => p 3)).program 8 (some 0) mem
        (List.replicate L.sites []) = some cs ∧
      runSegment ((template collectPreimage 3).instantiate w p).program 23 (some 0) mid
        (List.replicate (L.size true) []) = some rs ∧
      Directory old next place p out ∧ cs.length=L.sites ∧ rs.length=L.size true ∧
      (∀ r ∈ cs, r.probes=1 ∧ r.events.length+1=8) ∧ (∀ r ∈ rs, r.probes=4 ∧ r.events.length+1=23) ∧
      (∀ j, OutsidePreimageWrites p j → out j = mem j) := by
  intro L p old next place owners
  obtain ⟨regions,ho,_,hn,_,hc,_⟩ := frame X first true fit
  exact build old next place p regions ho hn (fun v => (map_count X side v).le.trans hc.symm.le) mem owners

end CompressorRecords.ShrinkResidentLayout

end

end VPVNP
end Computability
end OAI
