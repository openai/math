import OAI.Computability.BorderVNP.DiagonalPassingSeedCopy
import OAI.Computability.BorderVNP.PackedBottomBoxLocality

/-! # The reported suffix after an original birth bank

An original site's private work and incidence words occupy its full intrinsic
extent. The operand scan reads the separately emitted report suffix after that
extent. Appending those report reads preserves the original site's observations.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.DeckGrid.WiredWitness

/-- Read the original private and incidence words up to the site's intrinsic
extent, then read the physical report tape starting at its actual address. -/
def birthReportBank (extent report : ℕ) (original physical : ℕ → Bool) (k : ℕ) : Bool :=
  if k < extent then original k else physical (report+(k-extent))

/-- Every real original work and incidence position is kept verbatim. -/
theorem birthReportBank_before {extent k : ℕ} (report : ℕ) (original physical : ℕ → Bool) (hk : k<extent) :
    birthReportBank extent report original physical k = original k := ite_eq_left hk

/-- Every true supplemental position reads its offset in the final physical report. -/
theorem birthReportBank_after (extent report : ℕ) (original physical : ℕ → Bool) (k : ℕ) :
    birthReportBank extent report original physical (extent+k) = physical (report+k) := by
  simp only [birthReportBank,not_lt_of_ge (Nat.le_add_right extent k),ite_false,Nat.add_sub_cancel_left]

end Packing.DeckGrid.WiredWitness

namespace Packing.DeckGrid.WiredWitness

open Crossing CellSparse CellAddresses BottomGridBank BottomReports Inherited GridBoxes
open GridPlacement Cover TeamContraction ParseBatch ParseBatchVerifier Prewire
open VPVNP VPVNP.ParseGrammar Diagonal.CellEntries Diagonal.ExternalSew
open DiagonalTallyCellReports
open scoped Classical
set_option maxHeartbeats 1600000

variable {R r t pins link inner n g : ℕ} {Edge : Type} [Fintype Edge]
    {G : Wiring R r t pins link inner n Edge} {d : Fin n} {D q depth : ℕ}
    {order : Fin (Fintype.card (Fin q → Deck (depth+2))) ≃ (Fin q → Deck (depth+2))} {state : Fin g}
    (W : WiredWitness G d D q depth order state)
    (position : (Fin q → Deck (depth+2)) → {v : EuclideanSpace ℝ (Fin D) // ‖v‖ ≤ 1})
    (code : GrammarLabel (Fin n × Bool) (Fin g) n ↪ ℕ)

/-- The native bottom grid uses decidable equality of its physical deck vertices. -/
noncomputable local instance overlaySeedDeckEq : DecidableEq (Fin q → Deck (depth+2)) := Classical.decEq _
local notation "Tile₀" => (Fin q → Deck (depth+2))
local notation "tiles" => GridHosts.tileCount q depth
local notation "lane₀" => GridHosts.wiredLane G tiles Fintype.card_pos
local notation "width₀" => (fun _ : Fin tiles => GridHosts.inputBlockWidth r n q depth)
local notation "net₀" => W.routedFine position
local notation "owner₀" => cell position W.route
local notation "packing₀" => routedPacking position W.route (fun _ => le_rfl)
local notation "grouped₀" => W.seedGrouped position
local notation "wired₀" => wiredGrid G q depth order position
local notation "h₀" => seedChannelWidth n r q depth
variable {ns ne np qe qa : ℕ} (sites : (W.routedFine position).Site ↪ Fin ns) (edges : (W.routedFine position).Edge ↪ Fin ne)
    (ports : (Fin r × Fin (publicWidth G)) ↪ Fin np) (channels : ((Fin q → Deck (depth+2)) × Direction q) ↪ Fin qe)
    (groups : Fin (GridHosts.tileCount q depth) ↪ Fin qa) (c : Fin q → Deck (depth+2)) {copies : ℕ}
    (physicalBank : ℕ → Bool) (slot base : ℕ) (z : Fin copies → W.Hidden position)
local notation "slab" => W.seedSlab position code sites edges ports c
local notation "wide₀" => BottomRepeat.wide grouped₀ copies
local notation "fs" => W.nativeFactors position code sites edges ports c
local notation "pr" => W.seedBorn position code sites edges ports channels groups c
local notation "cap₀" => seedSiteCapacity n r q depth


variable {l : ReportLayout} (out : ReportCell l) (before after : List ReportBundle)
    (boxes : List (List Factor)) (original : ℕ → Bool)

private abbrev realCursor {l : ReportLayout} (out : ReportCell l) (before : List ReportBundle) :=
  out.privateWires+out.supplied+l.gadgets*l.countWidth+(before.map ReportBundle.useCount).sum

/-- Construct the complete reported seed source from its actual original local
bank and the physical cell tape. The native birth test runs before the report
region and the report offsets are supplied by the cell's preceding bundles. -/
noncomputable def PassingSeedSource.ofBirth
    (sequence : out.bundles = before ++ W.seedUseBundle position code sites edges ports channels groups c slot base copies physicalBank :: after)
    (tape : ∀ k < out.bits.length, physicalBank (out.privateWires+out.supplied+k) = (out.bits[k]?).getD false)
    (window : ∀ (i : Fin copies) (j : Fin (slab).stride), physicalBank (base+i.val*(slab).stride+j.val) = original (i.val*(slab).stride+j.val))
    (guesses : ∀ (i : Fin copies) (j : Fin (slab).guessed), original (i.val*(slab).stride+j.val) =
      ((guessedWords net₀ owner₀ c edges).symm (z i c)) j)
    (seen : ((pr copies).observe original).isSome = true)
    (valid : ∀ row ∈ reportRows base (slab).orig cap₀ copies (realCursor out before) fs, row.Valid boxes physicalBank) :
    W.PassingSeedSource position code sites edges ports channels groups c physicalBank slot base z l := by
  let site := pr copies
  let report := realCursor out before
  let bank := birthReportBank site.size report original physicalBank
  have localSite : site.Local := BottomGridBank.born_local net₀ owner₀ position packing₀ width₀ order lane₀
    (W.seedLane_aligned position) sites edges ports channels groups c
    (fun v => W.routedRules position (sidecarReport code) v.val) (3*cap₀) cap₀ copies
    (W.seed_stride_le position c) ((slab).reportFits)
  have hw : site.work = copies*(slab).stride := rfl
  have workBound (i : Fin copies) (j : Fin (slab).stride) : i.val*(slab).stride+j.val < site.size := by
    have h := Nat.add_lt_add_left j.isLt (i.val*(slab).stride)
    have next := Nat.mul_le_mul_right (slab).stride i.isLt
    rw [Nat.succ_mul] at next
    exact (h.trans_le (next.trans hw.symm.le)).trans_le (Nat.le_add_right site.work site.incoming)
  refine ⟨bank,site.size,boxes,out,before,after,sequence,tape,?_,?_,?_,?_,valid⟩
  · intro i j
    exact (window i j).trans (birthReportBank_before report original physicalBank (workBound i j)).symm
  · intro i j
    change birthReportBank site.size report original physicalBank (site.size+j.val*copies+i.val) =
      physicalBank (report+j.val*copies+i.val)
    simpa only [Nat.add_assoc] using birthReportBank_after site.size report original physicalBank (j.val*copies+i.val)
  · intro i j
    have within : j.val < (slab).stride := by
      have fit := (slab).fineFits
      have bound := j.isLt
      simp only [Slab.stride,Slab.orig,bottomStride]
      omega
    exact (birthReportBank_before report original physicalBank (workBound i ⟨j.val,within⟩)).trans (guesses i j)
  · have same : site.observe bank = site.observe original :=
      localSite _ _ fun j hj => birthReportBank_before report original physicalBank hj
    exact (congrArg Option.isSome same).trans seen

/-- Each original incidence suffix position in the spliced bank still gives the
true original read, even when the adjacent report has arbitrary Boolean values. -/
theorem birthReportBank_input (report : ℕ) (original physical : ℕ → Bool)
    (j : Fin (incoming wide₀ c)) :
    birthReportBank (pr copies).size report original physical (copies*(slab).stride+j.val) =
      original (copies*(slab).stride+j.val) :=
  birthReportBank_before report original physical (Nat.add_lt_add_left j.isLt _)

/-- Passing observations and row checks on the original local bank, before the
physical cell's report suffix is attached. -/
structure SeedBirthReceipt (copies base : ℕ) (layout : Slab) (birth : Site) (factors : List Factor)
    (bundle : ReportBundle) (physicalBank : ℕ → Bool) (guess : Fin copies → Fin layout.guessed → Bool)
    (l : ReportLayout) (original : ℕ → Bool) where
  /-- Actual local box rows on which the supplemental validity check runs. -/
  boxes : List (List Factor)
  /-- Physical cell report containing this original bundle. -/
  out : ReportCell l
  /-- Other bundles preceding this original bundle in the actual cell. -/
  before : List ReportBundle
  /-- Other bundles following this original bundle in the actual cell. -/
  after : List ReportBundle
  /-- The reported cell carries the exact source and both chronological neighbors. -/
  sequence : out.bundles = before ++ bundle :: after
  /-- All physically emitted suffix bits occupy their reported address. -/
  tape : ∀ k < out.bits.length, physicalBank (out.privateWires+out.supplied+k) = (out.bits[k]?).getD false
  /-- The source's actual work window is the offset-zero birth region for each copy. -/
  window : ∀ (i : Fin copies) (j : Fin layout.stride), physicalBank (base+i.val*layout.stride+j.val) = original (i.val*layout.stride+j.val)
  /-- The original guessed words encode the chosen hidden assignment. -/
  guesses : ∀ (i : Fin copies) (j : Fin layout.guessed), original (i.val*layout.stride+j.val) =
    guess i j
  /-- The actual original birth observations pass. -/
  seen : (birth.observe original).isSome = true
  /-- All rebased marked operand rows agree with their checked physical box entries. -/
  rows : ∀ row ∈ reportRows base layout.orig layout.capReport copies
    (out.privateWires+out.supplied+l.gadgets*l.countWidth+(before.map ReportBundle.useCount).sum) factors,
    row.Valid boxes physicalBank

/-- The concrete physical checks for this named wired site, indexed by its
actual original work and incidence bank. -/
noncomputable abbrev CheckedBirthData (l : ReportLayout) (original : ℕ → Bool) :=
  SeedBirthReceipt copies base (slab) (pr copies) fs
    (W.seedUseBundle position code sites edges ports channels groups c slot base copies physicalBank)
    physicalBank (fun i => (guessedWords net₀ owner₀ c edges).symm (z i c)) l original

namespace CheckedBirthData

variable {W position code sites edges ports channels groups c physicalBank slot base z original}
variable (data : W.CheckedBirthData position code sites edges ports channels groups c physicalBank slot base z l original)

/-- Append the actual physical report words to these already checked original
birth inputs and retain the observed physical row sequence. -/
noncomputable def passingSource : W.PassingSeedSource position code sites edges ports channels groups c physicalBank slot base z l :=
  PassingSeedSource.ofBirth W position code sites edges ports channels groups c physicalBank slot base z
    data.out data.before data.after data.boxes original data.sequence data.tape data.window data.guesses data.seen data.rows

/-- The source produced from the physical receipt preserves every original
typed incidence coordinate. -/
theorem passingSource_input (j : Fin (incoming wide₀ c)) :
    data.passingSource.birthBank (copies*(slab).stride+j.val) = original (copies*(slab).stride+j.val) :=
  birthReportBank_input W position code sites edges ports channels groups c (realCursor data.out data.before) original physicalBank j

end CheckedBirthData

end Packing.DeckGrid.WiredWitness

end BorderVNP
end Computability
end OAI
