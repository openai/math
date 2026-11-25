import OAI.Computability.BorderVNP.PackedRetainedNativeOperand

/-! # Physical use values in the chronological owned report ledger

Invert the real cell/bundle order, recover the selected original source and
copy, and read the corresponding power bit from the prewired witness.
The layout of every source bundle is the actual padded seed layout.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.DeckGrid.WiredWitness

open Crossing CellSparse GridBoxes BottomReports Cover TeamContraction GridPlacement
open Diagonal.CellEntries Diagonal.ExternalSew DiagonalTallyCellReports Inherited
open ParseBatch ParseBatchVerifier Prewire VPVNP VPVNP.ParseGrammar
open scoped Classical

variable {R r t pins link inner n g : ℕ} {Edge : Type} [Fintype Edge]
    {G : Wiring R r t pins link inner n Edge} {d : Fin n} {D q depth : ℕ}
    {order : Fin (Fintype.card (Fin q → Deck (depth+2))) ≃ (Fin q → Deck (depth+2))} {state : Fin g}
    (W : WiredWitness G d D q depth order state)
    (position : (Fin q → Deck (depth+2)) → {v : EuclideanSpace ℝ (Fin D) // ‖v‖ ≤ 1})
    {N leaves : ℕ} (origin : Fin N ≃ Fin leaves × (Fin q → Deck (depth+2)))
    (code : GrammarLabel (Fin n × Bool) (Fin g) n ↪ ℕ)
    {s m p qe qa : ℕ} (sites : (W.routedFine position).Site ↪ Fin s) (edges : (W.routedFine position).Edge ↪ Fin m)
    (ports : (Fin r × Fin (publicWidth G)) ↪ Fin p) (channels : ((Fin q → Deck (depth+2)) × Direction q) ↪ Fin qe)
    (groups : Fin (GridHosts.tileCount q depth) ↪ Fin qa)
    {copies : ℕ} (slot base : Fin N → ℕ) (bank : Fin N → ℕ → Bool)

/-- Equality used by the original routed deck's incidence and hidden wire read. -/
noncomputable local instance reportDeckEq : DecidableEq (Fin q → Deck (depth+2)) := Classical.decEq _

local notation "cap₀" => seedSiteCapacity n r q depth
local notation "pack₀" => routedPacking position W.route (fun _ => le_rfl)

/-- The report source at its original bundle ordinal, with its true opaque
body, host base, multiplicity and selected fine assignment. -/
noncomputable abbrev retainedBundle (j : Fin N) : ReportBundle :=
  W.seedUseBundle position code sites edges ports channels groups (origin j).2 (slot j) (base j) copies (bank j)

/-- Relative report suffix at a named original bundle ordinal. -/
noncomputable abbrev retainedReportStart (j : Fin N) := 3*cap₀+incoming (W.seedGrouped position) (origin j).2

local notation "bs₀" => W.retainedBundle (copies := copies) position origin code sites edges ports channels groups slot base bank
local notation "start₀" => W.retainedReportStart position origin
local notation "marks₀" => W.reportMark position origin code sites edges ports start₀ bs₀ (fun _ => rfl)
variable {Gadget : Type} (hidden : Fin leaves → Fin copies → W.Hidden position)
    (cables : Fin leaves → Fin copies → (W.seedGrid position).Assignment)
    (exterior : Fin leaves → Fin copies → Ports (fun _ : Fin r × Fin (publicWidth G) => 1))

/-- The exact formal power bit at the original site's own cell and copy,
on a complete hidden, cable and exterior assignment of that leaf. -/
noncomputable def retainedPower (i : Fin copies) (v : Fin leaves × WeightSites n g r d) : Bool :=
  let words := W.seedWords (Gadget := Gadget) position (hidden v.1 i)
  words.selected (words.site ((),v.2)) (fun e => cables v.1 i e.val) (fun p => exterior v.1 i p.val) ((),v.2)

local notation "power₀" => W.retainedPower (Gadget := Gadget) position hidden cables exterior
variable (readFine : ∀ (j : Fin N) (i : Fin copies) k, bank j (base j+i.val*(W.seedUseHeader position (origin j).2 (slot j) (base j) copies).stride+k.val) =
    physicalBits (cell position W.route) position (hidden (origin j).1 i) (routedPacking position W.route (fun _ => le_rfl)) edges ports (origin j).2
      (fun e => cables (origin j).1 i e.val) (fun p => exterior (origin j).1 i p.val) k)
variable (alive : ∀ (j : Fin N) (i : Fin copies),W.seedTags (Gadget := Gadget) position (hidden (origin j).1 i)
    (origin j).2 (fun e => cables (origin j).1 i e.val) (fun p => exterior (origin j).1 i p.val) ≠ 0)
include readFine alive

set_option maxHeartbeats 1600000 in
/-- The actual retained site's bank bit equals the formal bit at the recovered
power slot, with the source's true physical owner and copy. -/
theorem retained_source_bit (j : Fin N) (k : Fin (bs₀ j).positions.length) (i : Fin copies) :
    (bs₀ j).uses (finProdFinEquiv (k,i)) = power₀ i (marks₀ j k).val := by
  let u := W.sidecarEquiv position code sites edges ports (origin j).2 (start₀ j) k
  let z := hidden (origin j).1 i
  let words := W.seedWords (Gadget := Gadget) position z
  let get (v : (W.seedGrid position).Site) := words.selected v (fun e => cables (origin j).1 i e.val)
    (fun p => exterior (origin j).1 i p.val) ((),u.val)
  have source := W.seedUseBundle_selected position code sites edges ports channels groups (origin j).2
    (slot j) (base j) copies z (fun e => cables (origin j).1 i e.val) (fun p => exterior (origin j).1 i p.val)
    (bank j) i k (readFine j i) (alive j i)
  apply source.trans
  exact congrArg get u.property.symm

variable {C : ℕ} (owner : Fin N → Fin C) (team : Fin C → ℕ) (current : ℕ)
    {l : ReportLayout} (cs : List (ReportCell l)) (cells : Fin cs.length ≃ {c : Fin C // team c = current})
    (grouped : ∀ i : Fin cs.length, cs[i].bundles = (BundleDirectory.sourceRows owner (cells i).val.val).map
      (W.retainedBundle (copies := copies) position origin code sites edges ports channels groups slot base bank))
local notation "source₀" => W.reportUseEquiv position origin code sites edges ports start₀ bs₀ (fun _ => rfl)
  owner team current cs cells grouped (fun _ => rfl)

/-- The chronological native occurrence reads the exact selected formal
prewired power bit after recovering the true original leaf and copy. -/
theorem reportUse_selected (u : UseOccurrence cs) :
    let a := source₀ u
    cs[u.1].bundles[u.2.1].uses u.2.2 = power₀ a.1 a.2.val :=
  ownedUse_bit cs owner team current cells bs₀ grouped (W.weightRow position origin) (fun _ => rfl) marks₀
    power₀ (fun j k i => W.retained_source_bit position origin code sites edges ports channels groups slot base bank
      hidden cables exterior readFine alive j k i) u

/-- The actual chronological operand is ready for the native ledger's
permutation theorem: its coordinate and binary increment are both recovered
from the same retained source/copy and true prewired selected bit. -/
theorem reportUse_pair (u : UseOccurrence cs) :
    let a := source₀ u
    occurrencePair cs u = (code a.2.val.2.1,if power₀ a.1 a.2.val then 2^a.2.val.2.2.val else 0) := by
  intro a
  have fields := W.reportUse_fields position origin code sites edges ports start₀ bs₀ (fun _ => rfl)
    owner team current cs cells grouped (fun _ => rfl) u
  have selected := W.reportUse_selected position origin code sites edges ports channels groups slot base bank
    hidden cables exterior readFine alive owner team current cs cells grouped u
  unfold occurrencePair ReportBundle.usePair
  rw [fields.1,fields.2,selected]

end Packing.DeckGrid.WiredWitness

end BorderVNP
end Computability
end OAI
