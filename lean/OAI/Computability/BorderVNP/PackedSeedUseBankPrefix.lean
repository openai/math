import OAI.Computability.BorderVNP.PackedGridSeedNativeNames
import OAI.Computability.BorderVNP.PackedBottomWiredSite
import OAI.Computability.BorderVNP.PackedBottomInstalledFine

/-! # An original unary operand only addresses the retained private prefix -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.DeckGrid.WiredWitness

open Crossing CellSparse GridBoxes GridPlacement BottomGridBank BottomReports Inherited Cover TeamContraction
open Diagonal.CellEntries Diagonal.ExternalSew DiagonalTallyCellReports ParseBatch ParseBatchVerifier Prewire VPVNP VPVNP.ParseGrammar
open scoped Classical
set_option maxHeartbeats 1100000
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
noncomputable local instance appendSourceDeckEq : DecidableEq (Fin q → Deck (depth+2)) := Classical.decEq _
local notation "S₀" => seedSiteCapacity n r q depth
local notation "orig₀" => 3*S₀+incoming (W.seedGrouped position) c
local notation "rows₀" => W.nativeFactors position code siteID edgeID portID c
local notation "body₀" => W.seedStored position code siteID edgeID portID channelID groupID c
local notation "rules₀" => W.routedRules position (sidecarReport code)
local notation "pack₀" => routedPacking position W.route (fun _ => le_rfl)


/-- The selected wire of every original unary descriptor belongs to the
actual one-copy private grid slice. -/
theorem seedSelectedWire_lt (next : ℕ) (r₀ : Fin (sidecar next rows₀).length) :
    (selectedWires rows₀)[r₀.val]'(by simpa using r₀.isLt) <
      GridBoxes.stride (W.routedFine position) (cell position W.route) c := by
  let fs := rows₀
  let a := (selectedWires fs)[r₀.val]'(by simpa [fs] using r₀.isLt)
  obtain ⟨u,_,hu⟩ := List.mem_map.mp (selected_entry next fs r₀)
  change ruleFactor (W.routedFine position) (cell position W.route) c edgeID portID u (Fintype.equivFin _)
    (rules₀ u.val) = .unary a _ at hu
  cases hr : rules₀ u.val with
  | truth f => simp only [hr,ruleFactor,reduceCtorEq] at hu
  | unary lane tag =>
    simp only [hr,ruleFactor,Factor.unary.injEq] at hu
    change a < _
    rw [←hu.1]
    exact Fin.isLt _

/-- Appending all count and use bits of this same cell preserves the values
of every marked source. In particular the report read from a pre-call bank
is equal as a full report bundle to the report read from the passing bank. -/
theorem seedUseBundle_append (slot base copies : ℕ) (pre tail : List Bool)
    (extent : base+copies*(W.seedSlab position code siteID edgeID portID c).stride ≤ pre.length) :
    W.seedUseBundle position code siteID edgeID portID channelID groupID c slot base copies (lookup (pre++tail)) =
      W.seedUseBundle position code siteID edgeID portID channelID groupID c slot base copies (lookup pre) := by
  let H := W.seedUseHeader position c slot base copies
  let f := W.seedUseBundle position code siteID edgeID portID channelID groupID c slot base copies
  have same : (f (lookup (pre++tail))).uses=(f (lookup pre)).uses := by
    funext j
    obtain ⟨⟨r₀,i⟩,rfl⟩ := finProdFinEquiv.surjective j
    change (physicalBundle H body₀ rows₀ (lookup (pre++tail))).uses (finProdFinEquiv (r₀,i)) =
      (physicalBundle H body₀ rows₀ (lookup pre)).uses _
    refine (physicalBundle_use H body₀ rows₀ (lookup (pre++tail)) r₀ i).trans (Eq.trans ?_
      (physicalBundle_use H body₀ rows₀ (lookup pre) r₀ i).symm)
    have hr : r₀.val < (positions H.orig rows₀).length := r₀.isLt
    rw [positions_length] at hr
    let k := (selectedWires rows₀)[r₀.val]'(by simpa only [selectedWires_length] using hr)
    have fit := W.seedSelectedWire_lt position code siteID edgeID portID c H.orig ⟨r₀.val,by simpa using hr⟩
    have room := (W.seedSlab position code siteID edgeID portID c).fine_room ⟨k,fit⟩
    have first : H.boxBase+i.val*H.stride+k<pre.length := by
      change k < H.stride at room
      calc
        H.boxBase+i.val*H.stride+k = H.boxBase+(i.val*H.stride+k) := Nat.add_assoc ..
        _ < H.boxBase+(i.val*H.stride+H.stride) := Nat.add_lt_add_left (Nat.add_lt_add_left room _) _
        _ = H.boxBase+(i.val+1)*H.stride := by rw [Nat.succ_mul]
        _ ≤ H.boxBase+H.copies*H.stride := Nat.add_le_add_left (Nat.mul_le_mul_right H.stride i.isLt) _
        _ ≤ pre.length := extent
    change lookup (pre++tail) (H.boxBase+i.val*H.stride+k) = lookup pre (H.boxBase+i.val*H.stride+k)
    simp only [lookup,List.head?_drop,List.getElem?_append_left first]
  exact congrArg (ReportBundle.mk H body₀ (positions H.orig rows₀)) same

end Packing.DeckGrid.WiredWitness

end BorderVNP
end Computability
end OAI
