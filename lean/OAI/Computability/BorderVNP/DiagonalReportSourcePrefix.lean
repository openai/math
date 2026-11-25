import OAI.Computability.BorderVNP.PackedBottomReportBundle
import OAI.Computability.BorderVNP.PackedBottomReportCursors
import OAI.Computability.BorderVNP.PackedSeedCoreChoices
import OAI.Computability.BorderVNP.PackedBundleGroups
import OAI.Computability.BorderVNP.DiagonalTallyReportChoices

/-! # The use cursor of every bundle in its actual sorted reporting cell -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace DiagonalTallyCellReports.ReportDirectory

open Packing.BottomReports Packing.BundleDirectory

private theorem tape_append (tape : ℕ → Bool) (p : ℕ) (left right : List ReportBundle) :
    tapeBundles tape p (left++right) =
      tapeBundles tape p left ++ tapeBundles tape (p+(left.map ReportBundle.useCount).sum) right := by
  induction left generalizing p with
  | nil => simp [tapeBundles]
  | cons h t ih => simp only [List.cons_append,tapeBundles,ih,List.map_cons,List.sum_cons,Nat.add_assoc]

/-- The actual use bits of an original bundle in its physical cell start
after the expanded use counts of exactly the earlier source ordinals in
that cell. This split works for all assignments to the report tape. -/
theorem source_use_prefix {J C : ℕ} (home : Fin J → Fin C) (bundle : Fin J → Bundle)
    (body : Fin J → List CellSparse.Factor) (native : Fin J → ℕ → Bool)
    (j : Fin J) (c : ℕ) (placed : (home j).val=c) (rs : List ReportBundle)
    (stored : rs=(sourceRows home c).map (fun i =>
      physicalBundle (bundle i).header (body i) (bundle i).factors (native i)))
    (tape : ℕ → Bool) (p : ℕ) :
    let source := fun i => physicalBundle (bundle i).header (body i) (bundle i).factors (native i)
    ∃ pre post : List (Fin J), sourceRows home c = pre++j::post ∧
      let offset := p+(pre.map (fun i => (bundle i).useBits)).sum
      tapeBundles tape p rs =
        tapeBundles tape p (pre.map source) ++ (source j).withTape tape offset ::
          tapeBundles tape (offset+(bundle j).useBits) (post.map source) := by
  intro source
  obtain ⟨pre,post,split⟩ := List.append_of_mem (mem_sourceRows.mpr placed)
  refine ⟨pre,post,split,?_⟩
  rw [stored,split,List.map_append,tape_append]
  simp only [List.map_cons,tapeBundles,List.map_map,Function.comp_def,source,physicalBundle,
    ReportBundle.useCount,positions_length,Bundle.useBits]

end DiagonalTallyCellReports.ReportDirectory

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

/-- The reported positions in a received one-copy seed are the original
weighted factors, with one use bit for each of its exact copies. The values
guessed in the native bank affect only the bit values. -/
@[simp] theorem seedUseBundle_useBits (slot base copies : ℕ) (bank : ℕ → Bool) :
    (W.seedUseBundle position code siteID edgeID portID channelID groupID c slot base copies bank).useCount =
      (W.seedCoreBundle position code siteID edgeID portID c slot base copies).useBits := by
  simp only [seedUseBundle,physicalBundle,ReportBundle.useCount,Bundle.useBits,positions_length]

end Packing.DeckGrid.WiredWitness

end BorderVNP
end Computability
end OAI
