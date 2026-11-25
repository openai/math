import OAI.Computability.BorderVNP.PackedGridSeedTape
import OAI.Computability.BorderVNP.PackedGridSourceInventory
import OAI.Computability.BorderVNP.PackedBottomTapeNames
import OAI.Computability.BorderVNP.PackedGridSelectedNames

/-! # The real prewired seed's named bits in the native report bank

The immutable body and positions come from the routed witness. Each emitted
row reads its own selected wire on the chosen hidden assignment. The report
function that makes the seed tensor survive is therefore the same function
read by the private checker at the real cell's use cursor.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.DeckGrid.WiredWitness

open Crossing CellSparse GridBoxes GridPlacement BottomGridBank BottomReports Inherited Cover TeamContraction
open Diagonal.CellEntries Diagonal.ExternalSew DiagonalTallyCellReports ParseBatch ParseBatchVerifier Prewire VPVNP VPVNP.ParseGrammar
open scoped Classical
variable {R r t pins link inner n g : ℕ} {Edge : Type} [Fintype Edge]
    {G : Wiring R r t pins link inner n Edge} {d : Fin n} {D q depth : ℕ}
    {order : Fin (Fintype.card (Fin q → Deck (depth+2))) ≃ (Fin q → Deck (depth+2))} {state : Fin g}
    (W : WiredWitness G d D q depth order state)
    (position : (Fin q → Deck (depth+2)) → {v : EuclideanSpace ℝ (Fin D) // ‖v‖ ≤ 1})
    (code : GrammarLabel (Fin n × Bool) (Fin g) n ↪ ℕ)
    {s m p qe qa : ℕ} (siteID : (W.routedFine position).Site ↪ Fin s) (edgeID : (W.routedFine position).Edge ↪ Fin m)
    (portID : (Fin r × Fin (publicWidth G)) ↪ Fin p) (channelID : ((Fin q → Deck (depth+2)) × Direction q) ↪ Fin qe)
    (groupID : Fin (GridHosts.tileCount q depth) ↪ Fin qa) (c : Fin q → Deck (depth+2))
/-- Equality on the real deck cells used in the hidden grid assignment. -/
noncomputable local instance nativeNamesDeckEq : DecidableEq (Fin q → Deck (depth+2)) := Classical.decEq _
local notation "S₀" => seedSiteCapacity n r q depth
local notation "orig₀" => 3*S₀+incoming (W.seedGrouped position) c
local notation "rows₀" => W.nativeFactors position code siteID edgeID portID c
local notation "body₀" => W.seedStored position code siteID edgeID portID channelID groupID c
local notation "rules₀" => W.routedRules position (sidecarReport code)
local notation "pack₀" => routedPacking position W.route (fun _ => le_rfl)

/-- The scanner's six public fields for this real initial grid box. -/
noncomputable def seedUseHeader (slot base copies : ℕ) : BundleHeader :=
  ⟨slot,copies,base,bottomStride orig₀ S₀,S₀,orig₀⟩

variable (slot base copies : ℕ)
local notation "h₀" => W.seedUseHeader position c slot base copies

/-- The typed bundle whose body and source positions are precisely the
complete one-copy packet transmitted for the original routed witness. -/
noncomputable abbrev seedUseBundle (bank : ℕ → Bool) : ReportBundle :=
  physicalBundle h₀ body₀ rows₀ bank

local notation "b₀" => W.seedUseBundle position code siteID edgeID portID channelID groupID c slot base copies

/-- Typed native use count of this witness equals the actual sidecar count
times the true local bundle multiplicity. -/
theorem seedUseBundle_count (bank : ℕ → Bool) :
    (b₀ bank).useCount = count rows₀*copies := by
  change (positions orig₀ rows₀).length*copies = _
  rw [positions_length]

private theorem unique_report :
    ∀ u v p, ruleTag ((rules₀) u) = some p → ruleTag ((rules₀) v) = some p → u = v := by
  intro u v p hu hv
  obtain ⟨j,hj,hpj⟩ := (W.routed_ruleTag_iff position (sidecarReport code) u p).mp hu
  obtain ⟨k,hk,hpk⟩ := (W.routed_ruleTag_iff position (sidecarReport code) v p).mp hv
  have hjk := sidecarReport_injective code (hpj.trans hpk.symm)
  exact hj.symm.trans ((congrArg (W.routedPowerSite position) hjk).trans hk)

set_option maxHeartbeats 1000000 in
/-- A true typed operand reads the actual selected fine wire of the uniquely
decoded parameter and exponent, even if that bit is false. -/
theorem seedUseBundle_at (z : W.Hidden position) (a x) (bank : ℕ → Bool) (i : Fin copies)
    (r : Fin (W.seedPositions position code siteID edgeID portID c).length)
    (aligned : ∀ k, bank (base+i.val*(h₀).stride+k.val) = physicalBits (cell position W.route) position z
      pack₀ edgeID portID c a x k) :
    (b₀ bank).uses (finProdFinEquiv (r,i)) = trueReports rules₀ (cell position W.route) position z
      pack₀ c a x (sidecarReport code (W.sidecarEquiv position code siteID edgeID portID c orig₀ r).val) := by
  let rank : Fin (sidecar orig₀ rows₀).length := ⟨r.val,by simpa [seedPositions,sidecarPositions,positions] using r.isLt⟩
  have read := physicalBundle_trueReport rules₀ (cell position W.route) position z pack₀ siteID edgeID portID
    c (unique_report W position code) h₀ body₀ bank i rank a x aligned
  apply read.trans
  exact congrArg _ (W.sidecar_tag_at position code siteID edgeID portID c orig₀ rank)

set_option maxHeartbeats 1000000 in
/-- The emitted native tally operand increments precisely its decoded parameter
by the correct exponent-place value on selection, and by zero otherwise. -/
theorem seedUseBundle_operand_pair (z : W.Hidden position) (a x) (bank : ℕ → Bool) (i : Fin copies)
    (r : Fin (W.seedPositions position code siteID edgeID portID c).length) (cursor : ReportCursor) (external : ℕ)
    (aligned : ∀ k, bank (base+i.val*(h₀).stride+k.val) = physicalBits (cell position W.route) position z
      pack₀ edgeID portID c a x k) :
    let j := (W.sidecarEquiv position code siteID edgeID portID c orig₀ r).val
    ((b₀ bank).operand cursor external (finProdFinEquiv (r,i))).pair =
      (code j.1, if trueReports rules₀ (cell position W.route) position z pack₀ c a x (sidecarReport code j)
        then 2^j.2.val else 0) := by
  intro j
  have fields := W.sidecarEquiv_fields position code siteID edgeID portID c orig₀ r
  have source := physicalBundle_source h₀ body₀ rows₀ bank r i
  have hp : ((b₀ bank).source (finProdFinEquiv (r,i))).parameter = code j.1 :=
    (congrArg TallySidecar.Position.parameter source).trans fields.1
  have he : ((b₀ bank).source (finProdFinEquiv (r,i))).place = j.2.val :=
    (congrArg TallySidecar.Position.place source).trans fields.2.1
  have pair (b : ReportBundle) (k : Fin b.useCount) : (b.operand cursor external k).pair =
      ((b.source k).parameter, if b.uses k then 2^(b.source k).place else 0) :=
    DiagonalTallyMaterialize.unaryOperand_pair _ _ _ _ _ _ _
  apply (pair (b₀ bank) (finProdFinEquiv (r,i))).trans
  rw [hp,he,W.seedUseBundle_at position code siteID edgeID portID channelID groupID c slot base copies z a x bank i r aligned]

set_option maxHeartbeats 1000000 in
/-- The W-specific true report function satisfies the private checker's
recursive name condition on the actual cell tape, following the count words
and all earlier bundles. -/
theorem seedUseBundle_namedAt (z : W.Hidden position) (a x) (bank : ℕ → Bool) (i : Fin copies)
    (aligned : ∀ k, bank (base+i.val*(h₀).stride+k.val) = physicalBits (cell position W.route) position z
      pack₀ edgeID portID c a x k) {l : ReportLayout} (out : ReportCell l) (before after : List ReportBundle)
    (bundleOrder : out.bundles = before++(b₀ bank)::after)
    (tailAt : ∀ k < out.bits.length, bank (out.privateWires+out.supplied+k) = (out.bits[k]?).getD false) :
    NamedAt bank (trueReports rules₀ (cell position W.route) position z pack₀ c a x)
      copies i.val (out.privateWires+out.supplied+l.gadgets*l.countWidth+(before.map ReportBundle.useCount).sum)
      (sidecar orig₀ rows₀) := by
  have unique := W.sidecar_tags_nodup position code siteID edgeID portID c orig₀
  have bound := namedAt_report_tape out before after h₀ body₀ rows₀ bank bundleOrder unique i tailAt
  apply (namedAt_iff ..).mpr
  intro j
  have hb := (namedAt_iff ..).mp bound j
  apply hb.trans
  apply (bundleUse_row h₀ body₀ rows₀ bank i unique j).trans
  exact physicalBundle_trueReport rules₀ (cell position W.route) position z pack₀ siteID edgeID portID
    c (unique_report W position code) h₀ body₀ bank i j a x aligned

set_option maxHeartbeats 1000000 in
/-- The tag of a real prewired seed term survives exactly when its physical
padding and every fine check pass with the actual native selected-wire uses. -/
theorem seed_alive_native {Gadget : Type} (z : W.Hidden position) (a x) (bank : ℕ → Bool) (i : Fin copies)
    (aligned : ∀ k, bank (base+i.val*(h₀).stride+k.val) = physicalBits (cell position W.route) position z
      pack₀ edgeID portID c a x k) :
    W.seedTags (Gadget := Gadget) position z c a x ≠ 0 ↔ padOK pack₀ c a x ∧
      ∀ u,cellRead (cell position W.route) position z pack₀ (guard rules₀ (bundleUse h₀ body₀ rows₀ bank i)) c u a x = true := by
  have uses := bundleUse_trueReports rules₀ (cell position W.route) position z pack₀ siteID edgeID portID
    c (unique_report W position code) h₀ body₀ bank i
    (W.sidecar_tags_nodup position code siteID edgeID portID c orig₀) a x aligned
  rw [uses]
  exact W.seed_alive_trueReports position (sidecarReport code) (sidecarReport_injective code) z c a x

end Packing.DeckGrid.WiredWitness

end BorderVNP
end Computability
end OAI
