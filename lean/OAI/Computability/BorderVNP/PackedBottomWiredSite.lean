import OAI.Computability.BorderVNP.PackedBottomPhysicalReads
import OAI.Computability.BorderVNP.PackedGridSeedNativeNames
import OAI.Computability.BorderVNP.PackedBottomReportWindows

/-! # The real weighted query seed's pass condition on the padded work slab

This joins the sparse original box interpreter to the prewired verifier's
tagged seed tables. The chosen internal fine wires are the free variables.
Every padding, cable and use slot satisfies the complete reconstruction
equations. The named uses in the physical bit stream are the ones decoded
by the original source sidecar.
-/

namespace OAI
namespace Computability
namespace BorderVNP

set_option maxHeartbeats 2000000

namespace Packing.DeckGrid.WiredWitness

open Crossing CellSparse CellAddresses BottomGridBank BottomReports Inherited GridBoxes
open GridPlacement Cover TeamContraction ParseBatch ParseBatchVerifier Prewire
open VPVNP VPVNP.ParseGrammar Diagonal.CellEntries Diagonal.ExternalSew
open scoped Classical

variable {R r t pins link inner n g : ℕ} {Edge : Type} [Fintype Edge]
    {G : Wiring R r t pins link inner n Edge} {d : Fin n} {D q depth : ℕ}
    {order : Fin (Fintype.card (Fin q → Deck (depth+2))) ≃ (Fin q → Deck (depth+2))} {state : Fin g}
    (W : WiredWitness G d D q depth order state)
    (position : (Fin q → Deck (depth+2)) → {v : EuclideanSpace ℝ (Fin D) // ‖v‖ ≤ 1})
    (code : GrammarLabel (Fin n × Bool) (Fin g) n ↪ ℕ)

local notation "Tile₀" => (Fin q → Deck (depth+2))
local notation "cardV" => GridHosts.tileCount q depth
local notation "net₀" => W.routedFine position
local notation "owner₀" => GridPlacement.cell position W.route
local notation "packing₀" => routedPacking position W.route (fun _ => le_rfl)
local notation "liveLane" => GridHosts.wiredLane G cardV Fintype.card_pos
local notation "width₀" => (fun _ : Fin cardV => GridHosts.inputBlockWidth r n q depth)
local notation "cap₀" => seedSiteCapacity n r q depth
local notation "h₀" => seedChannelWidth n r q depth
local notation "rule₀" => W.routedRules position (sidecarReport code)
local notation "pack₀" => W.seedGrouped position
local notation "at₀" => W.seedLane_aligned position

/-- Equality used in the true conditioned prewire tables at each public tile. -/
noncomputable local instance checkedSeedDeckEq : DecidableEq (Fin q → Deck (depth+2)) := Classical.decEq _

variable {ns ne np qe qa : ℕ} (siteID : (W.routedFine position).Site ↪ Fin ns) (edgeID : (W.routedFine position).Edge ↪ Fin ne)
    (portID : (Fin r × Fin (publicWidth G)) ↪ Fin np) (channels : ((Fin q → Deck (depth+2)) × Direction q) ↪ Fin qe)
    (groups : Fin (GridHosts.tileCount q depth) ↪ Fin qa) (c : Fin q → Deck (depth+2))

/-- The actual fine guesses, grouped incidence bits and weighted slots of the
prewired verifier at this cell, with the certified common public capacities. -/
noncomputable def seedSlab : Slab :=
  BottomGridBank.slab (H := h₀) (src := fun a : Tile₀ × Direction q => Prod.fst a) (dst := fun a => Prod.fst a*step q (depth+2) (Prod.snd a))
    net₀ owner₀ position width₀ order siteID edgeID portID c (fun u => W.routedRules position (sidecarReport code) u.val)
    (3*cap₀) cap₀ (W.seed_stride_le position c) (W.seed_sites_le position c)

local notation "s₀" => W.seedSlab position code siteID edgeID portID c
local notation "fs" => W.nativeFactors position code siteID edgeID portID c
local notation "pr" => W.seedBorn position code siteID edgeID portID channels groups c
local notation "index₀" => publicIndex net₀ owner₀ position packing₀ width₀ order liveLane at₀ edgeID portID channels groups c
local notation "slice₀" => copyInput (H := h₀) (src := fun a : Tile₀ × Direction q => Prod.fst a)
  (dst := fun a => Prod.fst a*step q (depth+2) (Prod.snd a)) net₀ owner₀ position width₀ order channels groups c
local notation "wire₀" => channelRead (H := h₀) (src := fun a : Tile₀ × Direction q => Prod.fst a)
  (dst := fun a => Prod.fst a*step q (depth+2) (Prod.snd a)) net₀ owner₀ position width₀ order channels groups c
local notation "port₀" => argumentRead (H := h₀) (src := fun a : Tile₀ × Direction q => Prod.fst a)
  (dst := fun a => Prod.fst a*step q (depth+2) (Prod.snd a)) net₀ owner₀ position width₀ order liveLane at₀ channels groups c

/-- In the native supplemented box every non-free lane is forced and every copy
has a nonzero tagged seed entry at its true fine assignment. Conversely these
conditions make all original private and public checks pass. -/
theorem seed_checked_iff {Gadget : Type} (copies cursor : ℕ) (bank : ℕ → Bool) (boxes : List (List Factor))
    (z : Fin copies → W.Hidden position) :
    let input := slice₀ copies (s₀).stride bank
    let wires := fun i => wire₀ (input i)
    let args := fun i => port₀ (input i)
    let uses := fun i => trueReports rule₀ owner₀ position (z i) packing₀ c (wires i) (args i)
    let forced := ∀ i : Fin copies, (s₀).Checks (fun k => bank (i.val*(s₀).stride+k))
      (fun k => input i (index₀ k)) (input i) (fun k => bank (cursor+k.val*copies+i.val))
    (∀ (i : Fin copies) (k : Fin (s₀).guessed), bank (i.val*(s₀).stride+k.val) =
      ((guessedWords net₀ owner₀ c edgeID).symm (z i c)) k) →
    (∀ i : Fin copies, NamedAt bank (uses i) copies i.val cursor (sidecar (s₀).orig fs)) →
    (((pr copies).observe bank).isSome = true ∧
      (∀ row ∈ reportRows 0 (s₀).orig cap₀ copies cursor fs, row.Valid boxes bank) ↔
      forced ∧ ∀ i : Fin copies, W.seedTags (Gadget := Gadget) position (z i) c (wires i) (args i) ≠ 0) := by
  intro input wires args uses forced guess names
  have ok := complete_acceptance net₀ owner₀ position packing₀ width₀ order liveLane at₀ siteID edgeID portID
    channels groups c (fun v => W.routedRules position (sidecarReport code) v.val) copies (3*cap₀) cap₀ cursor
    (W.seed_stride_le position c) (W.seed_sites_le position c) bank boxes uses names
  apply ok.trans
  apply and_congr_right
  intro hforced
  have physical (i : Fin copies) : ∀ k : Fin (GridBoxes.stride net₀ owner₀ c),
      bank (i.val*(s₀).stride+k.val) = physicalBits owner₀ position (z i) packing₀ edgeID portID c (wires i) (args i) k :=
    prefix_physical net₀ owner₀ position packing₀ width₀ order liveLane at₀ edgeID portID channels groups c
      (input i) (z i) bank (i.val*(s₀).stride) (guess i) (hforced i).1
  have guardRead (i : Fin copies) (v : {w : (W.routedFine position).Site // owner₀ w = c}) :
      (rule₀ v.val).passes (fun l => bank (i.val*(s₀).stride+(GridBoxes.lane net₀ owner₀ c edgeID portID v l).val)) (uses i) =
        cellRead owner₀ position (z i) packing₀ (guard rule₀ (uses i)) c v (wires i) (args i) :=
    named_guard_read net₀ owner₀ position packing₀ width₀ order liveLane at₀ edgeID portID channels groups c
      rule₀ (uses i) v (input i) (z i) bank (i.val*(s₀).stride) (physical i)
  have alive (i : Fin copies) := W.seed_alive_trueReports (Gadget := Gadget) position (sidecarReport code)
    (sidecarReport_injective code) (z i) c (wires i) (args i)
  constructor
  · rintro ⟨pad,guards⟩ i
    exact (alive i).mpr ⟨pad i,fun v => (guardRead i v).symm.trans (guards i v)⟩
  · intro h
    exact ⟨fun i => ((alive i).mp (h i)).1,fun i v => (guardRead i v).trans (((alive i).mp (h i)).2 v)⟩

open DiagonalTallyCellReports

/-- The true native report tape closes the named-report premise. The birth
view reads its own incidence suffix, while the retained private prefix and
the final count-following report suffix are read at their physical addresses. -/
theorem seed_physical_iff {Gadget : Type} (slot base copies cursor : ℕ)
    (birthBank physicalBank : ℕ → Bool) (boxes : List (List Factor))
    {l : ReportLayout} (out : ReportCell l) (before after : List ReportBundle)
    (z : Fin copies → W.Hidden position) :
    let realCursor := out.privateWires+out.supplied+l.gadgets*l.countWidth+(before.map ReportBundle.useCount).sum
    let bundle := W.seedUseBundle position code siteID edgeID portID channels groups c slot base copies physicalBank
    let input := slice₀ copies (s₀).stride birthBank
    let wires := fun i => wire₀ (input i)
    let args := fun i => port₀ (input i)
    let forced := ∀ i : Fin copies, (s₀).Checks (fun k => birthBank (i.val*(s₀).stride+k))
      (fun k => input i (index₀ k)) (input i) (fun k => birthBank (cursor+k.val*copies+i.val))
    out.bundles = before++bundle::after →
    (∀ k < out.bits.length, physicalBank (out.privateWires+out.supplied+k) = (out.bits[k]?).getD false) →
    (∀ (i : Fin copies) (k : Fin (s₀).stride), physicalBank (base+i.val*(s₀).stride+k.val) =
      birthBank (i.val*(s₀).stride+k.val)) →
    (∀ (i : Fin copies) (rank : Fin (count fs)), birthBank (cursor+rank.val*copies+i.val) =
      physicalBank (realCursor+rank.val*copies+i.val)) →
    (∀ (i : Fin copies) (k : Fin (s₀).guessed), birthBank (i.val*(s₀).stride+k.val) =
      ((guessedWords net₀ owner₀ c edgeID).symm (z i c)) k) →
    (((pr copies).observe birthBank).isSome = true ∧
      (∀ row ∈ reportRows base (s₀).orig cap₀ copies realCursor fs, row.Valid boxes physicalBank) ↔
      forced ∧ ∀ i : Fin copies, W.seedTags (Gadget := Gadget) position (z i) c (wires i) (args i) ≠ 0) := by
  intro realCursor bundle input wires args forced sequence tape workAt use guess
  have rows := reportRows_rebase_iff birthBank physicalBank boxes base (s₀).orig cap₀ copies cursor
    realCursor fs (s₀).reportFits workAt use
  rw [← rows]
  have iffOf (checked : forced) : (((pr copies).observe birthBank).isSome = true ∧
        (∀ row ∈ reportRows 0 (s₀).orig cap₀ copies cursor fs, row.Valid boxes birthBank)) ↔
      forced ∧ ∀ i : Fin copies, W.seedTags (Gadget := Gadget) position (z i) c (wires i) (args i) ≠ 0 := by
    apply W.seed_checked_iff (Gadget := Gadget) position code siteID edgeID portID channels groups c copies cursor
      birthBank boxes z guess
    intro i
    have small : GridBoxes.stride net₀ owner₀ c ≤ (s₀).stride :=
      (W.seed_stride_le position c).trans ((Nat.le_add_right _ _).trans (Nat.le_add_right _ _))
    have physical := prefix_physical net₀ owner₀ position packing₀ width₀ order liveLane at₀ edgeID portID channels groups c
      (input i) (z i) birthBank (i.val*(s₀).stride) (guess i) (checked i).1
    have aligned (k : Fin (GridBoxes.stride net₀ owner₀ c)) :
        physicalBank (base+i.val*(s₀).stride+k.val) =
          physicalBits owner₀ position (z i) packing₀ edgeID portID c (wires i) (args i) k :=
      (workAt i ⟨k.val,k.isLt.trans_le small⟩).trans (physical k)
    have names := W.seedUseBundle_namedAt position code siteID edgeID portID channels groups c slot base copies
      (z i) (wires i) (args i) physicalBank i aligned out before after sequence tape
    apply (namedAt_iff ..).mpr
    intro j
    exact (use i ⟨j.val,by simpa using j.isLt⟩).trans ((namedAt_iff ..).mp names j)
  constructor
  · intro hp
    have checked (i : Fin copies) := accepted_checks net₀ owner₀ position packing₀ width₀ order liveLane at₀
      siteID edgeID portID channels groups c (fun v => W.routedRules position (sidecarReport code) v.val)
      copies (3*cap₀) cap₀ cursor (W.seed_stride_le position c) (W.seed_sites_le position c) birthBank boxes i hp.1 hp.2
    exact (iffOf checked).mp hp
  · intro hp
    exact (iffOf hp.1).mpr hp

end Packing.DeckGrid.WiredWitness

end BorderVNP
end Computability
end OAI
