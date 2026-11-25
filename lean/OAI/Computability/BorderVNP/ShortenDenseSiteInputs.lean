import OAI.Computability.BorderVNP.ShortenDensePath
import OAI.Computability.BorderVNP.ShortenDenseSiteHistory
import OAI.Computability.BorderVNP.ShortenSiteProgram

/-!
# Initial site routes and terminal catalogs for publicly sorted epochs

The zero-stage state subdivides the given site route with its original
valued pack. Terminal catalog membership comes from the actually stored
successor, including the dense ordering of its saved cable directory.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace PackedHistoryCircuit.Normalized.StagePath

open Crossing Cover Epoch Round Shortening Catalog Packing
open scoped Classical

variable {I : Type} [Fintype I] {D m b : ℕ} [NeZero D] {K : Type*} [Field K]
    {e : PaidIdentity K D m} {h H ν L : ℝ} (path : StagePath b e I h H ν)

/-- Each flat leaf of the sorted program starts at the given input pack and
site routes, with their exact original potential. -/
theorem initial_leaves (hh : 0 < h) :
    ∃ floor : ℕ, ∀ {k : ℕ} {P : Type} {bits : P → ℕ} (w : ℝ) last high,
    path.depth last high 0 = high → floor ≤ high+1 →
    path.catalog 0 = SiteRoutes.startingSites I L h →
    ∀ (input : Fin (k^b) → Pack D P bits K) (routes : ∀ i, SiteRoutes (input i) I high L),
      ∃ flat : Fin (k^b) → path.State P bits k last high 0,
      ∃ initial : ∀ i, InitialSites (flat i).val L hh,
        (∀ i, (initial i).pack = input i) ∧ (∀ i, (initial i).routes.potential w = (routes i).potential w) ∧
        ∀ i, HEq (initial i).routes (routes i) := by
  obtain ⟨floor,init⟩ := SiteRoutes.initial_placedAt (L := L) I hh
  refine ⟨floor,?_⟩
  intro k P bits w last high hstart hfloor hc input routes
  let before := path.depth last high 0
  let r (i) : SiteRoutes (input i) I before L := Adaptive.reindexRoutes hstart.symm (routes i)
  let f (i) : path.State P bits k last high 0 := ⟨(r i).initialPlacedPack hh,by
    rw [hc]
    exact init before (hfloor.trans_eq (congrArg (·+1) hstart.symm)) (r i)⟩
  exact ⟨f,fun i => ⟨input i,r i,rfl⟩,fun _ => rfl,fun i => Adaptive.reindexRoutes_potential _ _ w,
    fun i => Adaptive.reindexRoutes_heq _ _⟩

/-- The same finite segment catalog covers every attained stored terminal
state, uniformly before fan-in, absolute levels, input packs and histograms. -/
theorem terminal_catalog (hh : 2*h ≤ 1/4) :
    ∃ V : Set (SegmentType I), V.Finite ∧
      ∀ {k : ℕ} {P : Type} {bits : P → ℕ} (last high : ℕ)
        (F : path.ProgramAt P bits k last high)
        (flat : Fin (k^b) → path.State P bits k last high 0) (i : F.Hist flat),
        FitsCatalog (F.terminal flat i) V (1/4) := by
  obtain ⟨V,hV,h⟩ := finite_segments (path.catalog b).finite_toSet (2*h)
  refine ⟨V,hV,?_⟩
  intro k P bits last high F flat i
  let z := (F.system.histories b le_rfl (Adaptive.leavesEquiv k (path.State P bits k last high 0) b flat)).term i
  let state := (F.system.layer b).state z
  change FitsCatalog state.val V (1/4)
  intro c
  obtain ⟨act,distinct⟩ := (state.val.active_iff c.val).mp c.property
  have short := state.property.short _ act
  exact ⟨short.trans hh,h _ _ _ (state.property.sites _) (state.property.sites _) distinct short⟩

end PackedHistoryCircuit.Normalized.StagePath

end BorderVNP
end Computability
end OAI
