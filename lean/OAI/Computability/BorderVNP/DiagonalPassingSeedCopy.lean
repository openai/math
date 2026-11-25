import OAI.Computability.BorderVNP.DiagonalBottomSeedPhysicalBits
import OAI.Computability.BorderVNP.DiagonalBottomSeedCheckedWords
import OAI.Computability.BorderVNP.PackedBottomWiredSite

/-! # Recovering the fine seed bits from a passing original site's report

The birth checker and the physical row suffix together supply the original
copy's forced operands and its surviving fine tag. The original incidence
suffix is stated separately so that it can be obtained along the attained
history and exterior path.
-/

namespace OAI
namespace Computability
namespace BorderVNP

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
noncomputable local instance passingSeedDeckEq : DecidableEq (Fin q → Deck (depth+2)) := Classical.decEq _
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
    (groups : Fin (GridHosts.tileCount q depth) ↪ Fin qa) (c : Fin q → Deck (depth+2)) {copies : ℕ} (a : PowerInput ((wiredGrid G q depth order position).groupedRepeat
      (fun _ : Fin (Fintype.card (Fin q → Deck (depth+2))) => GridHosts.inputBlockWidth r n q depth) order copies))
    (physicalBank : ℕ → Bool) (slot base : ℕ) (z : Fin copies → W.Hidden position)
local notation "slab" => W.seedSlab position code sites edges ports c
local notation "wide₀" => BottomRepeat.wide grouped₀ copies
local notation "slice₀" => copyInput (H := h₀) (src := fun a : Tile₀ × Direction q => Prod.fst a)
  (dst := fun a => Prod.fst a*step q (depth+2) (Prod.snd a)) net₀ owner₀ position width₀ order channels groups c
local notation "idx₀" => publicIndex net₀ owner₀ position packing₀ width₀ order lane₀ (W.seedLane_aligned position) edges ports channels groups c
local notation "input₀" => inputWords wide₀ channels groups c (fun e => PowerInput.edges a (Subtype.val e)) (fun p => PowerInput.ports a (Subtype.val p))


local notation "fs" => W.nativeFactors position code sites edges ports c
local notation "pr" => W.seedBorn position code sites edges ports channels groups c
local notation "cap₀" => seedSiteCapacity n r q depth

/-- Concrete checked birth and cell-report data for one original routed site. -/
structure SeedSourceReceipt (copies base : ℕ) (layout : Slab) (birth : Site) (factors : List Factor)
    (bundle : ReportBundle) (physicalBank : ℕ → Bool) (guess : Fin copies → Fin layout.guessed → Bool)
    (l : ReportLayout) where
  /-- Birth work followed by the site's reconstructed incidence suffix and reports. -/
  birthBank : ℕ → Bool
  /-- Original report-start address in the birth view. -/
  cursor : ℕ
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
  window : ∀ (i : Fin copies) (j : Fin layout.stride), physicalBank (base+i.val*layout.stride+j.val) = birthBank (i.val*layout.stride+j.val)
  /-- Each marked report read uses its own rank and copy in the final cell suffix. -/
  use : ∀ (i : Fin copies) (rank : Fin (count factors)), birthBank (cursor+rank.val*copies+i.val) =
    physicalBank (out.privateWires+out.supplied+l.gadgets*l.countWidth+(before.map ReportBundle.useCount).sum+rank.val*copies+i.val)
  /-- The original guessed words encode the chosen hidden assignment. -/
  guesses : ∀ (i : Fin copies) (j : Fin layout.guessed), birthBank (i.val*layout.stride+j.val) =
    guess i j
  /-- The actual original birth observations pass. -/
  seen : (birth.observe birthBank).isSome = true
  /-- All rebased marked operand rows agree with their checked physical box entries. -/
  rows : ∀ row ∈ reportRows base layout.orig layout.capReport copies
    (out.privateWires+out.supplied+l.gadgets*l.countWidth+(before.map ReportBundle.useCount).sum) factors,
    row.Valid boxes physicalBank

/-- The report receipt at the actual wired seed program, grammar marks and
original hidden fine assignment of this physical source. -/
noncomputable abbrev PassingSeedSource (l : ReportLayout) :=
  SeedSourceReceipt copies base (slab) (pr copies) fs
    (W.seedUseBundle position code sites edges ports channels groups c slot base copies physicalBank)
    physicalBank (fun i => (guessedWords net₀ owner₀ c edges).symm (z i c)) l

/-- Actual reported work lanes and the passing fine verifier are recovered
simultaneously on every copy of this original host. -/
theorem seedPassingCopy {Gadget : Type} {l : ReportLayout}
    (source : W.PassingSeedSource position code sites edges ports channels groups c physicalBank slot base z l)
    (suffix : ∀ j : Fin (incoming wide₀ c), source.birthBank (copies*(slab).stride+j.val) = input₀ j)
    (i : Fin copies) :
    (∀ j : Fin (stride net₀ owner₀ c), physicalBank (base+i.val*(slab).stride+j.val) =
      physicalBits owner₀ position (z i) packing₀ edges ports c
        (fun e => (W.seedCopyInput position a i).edges e.val) (fun p => (W.seedCopyInput position a i).ports p.val) j) ∧
    (W.seedGrid position).read (W.seedTags (Gadget := Gadget) position (z i)) (W.seedCopyInput position a i).edges
      (W.seedCopyInput position a i).ports c ≠ 0 := by
  obtain ⟨forced,pass⟩ := (W.seed_physical_iff (Gadget := Gadget) position code sites edges ports channels groups c
    slot base copies source.cursor source.birthBank physicalBank source.boxes source.out source.before source.after z
    source.sequence source.tape source.window source.use source.guesses).mp ⟨source.seen,source.rows⟩
  refine ⟨W.seedCopyInput_physicalBits position code sites edges ports channels groups c a source.birthBank physicalBank base
    i (z i) suffix (source.window i) (source.guesses i) (fun k => source.birthBank (source.cursor+k.val*copies+i.val)) (forced i),?_⟩
  obtain ⟨he,hp⟩ := W.seedCopyInput_checkerWords position code sites edges ports channels groups c a source.birthBank i suffix
  intro zero
  exact pass i ((congrArg₂ (W.seedTags (Gadget := Gadget) position (z i) c) he hp).trans zero)

end Packing.DeckGrid.WiredWitness

end BorderVNP
end Computability
end OAI
