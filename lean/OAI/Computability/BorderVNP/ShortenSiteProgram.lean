import OAI.Computability.BorderVNP.ShortenEpochRoundClosure
import OAI.Computability.BorderVNP.ShortenEpochRoundInputGeometry
import OAI.Computability.BorderVNP.ShortenCatalogEpoch

/-!
# Initial states and the terminal catalog of a prepared site epoch

Site inputs enter the actual K-ary program by geodesic equality subdivision.
The output at each attained history is the same placed pack stored in the
prepared program. Its relative sites and short charged lengths consequently
supply the final finite segment catalog needed for the rounding motion.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Shortening.Adaptive

open Crossing Cover Epoch Round Catalog Packing
open scoped Classical

variable {I P : Type} [Fintype I] {D m b k : ℕ} [NeZero D] {K : Type*} [Field K]
    {bits : P → ℕ} {e : PaidIdentity K D m} {h H ν L : ℝ}
    (path : StagePath b e I h H ν)

/-- Transporting the depth index retains the same site and move record. -/
def reindexRoutes {a z : ℕ} (he : a = z) {p : Pack D P bits K} (routes : SiteRoutes p I a L) : SiteRoutes p I z L :=
  he ▸ routes

omit [NeZero D] [Field K] in
/-- Reindexing does not alter the underlying actual routes or sites. -/
theorem reindexRoutes_heq {a z : ℕ} (he : a = z) {p : Pack D P bits K} (routes : SiteRoutes p I a L) :
    HEq (reindexRoutes he routes) routes := by cases he; rfl

omit [NeZero D] [Field K] in
/-- The initial site potential is invariant under this relabeling of the integer depth. -/
theorem reindexRoutes_potential {a z : ℕ} (he : a = z) {p : Pack D P bits K} (routes : SiteRoutes p I a L) (w : ℝ) :
    (reindexRoutes he routes).potential w = routes.potential w := by cases he; rfl

/-- Realize the zero stage by subdividing each input's actual valued pack.
The sites and their original costs are retained on this same leaf tuple. -/
theorem StagePath.initial_leaves (hh : 0 < h) :
    ∃ floor : ℕ, ∀ {k : ℕ} {P : Type} {bits : P → ℕ} (w : ℝ) last high, path.depths last high 0 = high → floor ≤ high+1 →
    path.catalog 0 = SiteRoutes.startingSites I L h →
    ∀ (input : Fin (k^b) → Pack D P bits K) (routes : ∀ i, SiteRoutes (input i) I high L),
      ∃ flat : Fin (k^b) → path.State P bits k last high 0,
      ∃ initial : ∀ i, InitialSites (flat i).val L hh,
        (∀ i, (initial i).pack = input i) ∧ (∀ i, (initial i).routes.potential w = (routes i).potential w) ∧
        (∀ i, HEq (initial i).routes (routes i)) := by
  obtain ⟨floor,init⟩ := SiteRoutes.initial_placedAt (L := L) I hh
  refine ⟨floor,?_⟩
  intro k P bits w last high hstart hfloor hc input routes
  let before := path.depths last high 0
  let r (i) : SiteRoutes (input i) I before L := reindexRoutes hstart.symm (routes i)
  let f (i) : path.State P bits k last high 0 := ⟨(r i).initialPlacedPack hh, by
    rw [hc]
    exact init before (hfloor.trans_eq (congrArg (·+1) hstart.symm)) (r i)⟩
  exact ⟨f,fun i => ⟨input i,r i,rfl⟩,fun _ => rfl,fun i => reindexRoutes_potential _ _ w,fun i => reindexRoutes_heq _ _⟩

/-- On a directly stored program the executed network is exactly the stored
network, including its site positions and charged midpoints. -/
theorem Program.executed_eq_state {A : ℕ → Type*} {B : Fin b → Type} [∀ i, Fintype (B i)]
    {depth : ℕ → ℕ} {view : ∀ n, A n → PlacedPack D (Port k P n) (width bits k n) K I (depth n)}
    (F : Program (B := B) e view)
    (stored : ∀ i c q, view (i.val+1) (F.advance i c q) = (F.step i c).result e q)
    (n : ℕ) (z : (F.system.layer n).Name) : F.executed n z = view n ((F.system.layer n).state z) := by
  cases n with
  | zero => rfl
  | succ j => exact (stored ⟨j,z.2.1.down⟩ (fun i => (F.system.layer j).state (z.1 i)) z.2.2).symm

/-- The terminal relative catalog is selected before the fan-in, the absolute
levels, all leaf packs, and all their public histograms. -/
theorem StagePath.terminal_catalog (hh : 2*h ≤ 1/4) :
    ∃ V : Set (SegmentType I), V.Finite ∧
    ∀ {k : ℕ} {P : Type} {bits : P → ℕ} (last high : ℕ)
      (F : Program (B := fun i => (path.pattern i).Bin) e
        (fun n (p : path.State P bits k last high n) => p.val)),
      (∀ i c q, (F.advance i c q).val = (F.step i c).result e q) →
      ∀ (flat : Fin (k^b) → path.State P bits k last high 0) (i : F.Hist flat), FitsCatalog (F.terminal flat i) V (1/4) := by
  obtain ⟨V,hV,h⟩ := finite_segments (path.catalog b).finite_toSet (2*h)
  refine ⟨V,hV,?_⟩
  intro k P bits last high F stored flat i
  let z := (F.system.histories b le_rfl (leavesEquiv k (path.State P bits k last high 0) b flat)).term i
  let state := (F.system.layer b).state z
  have he : F.terminal flat i = state.val := F.executed_eq_state stored b z
  rw [he]
  have hs := state.property
  intro c
  obtain ⟨act,distinct⟩ := (state.val.active_iff c.val).mp c.property
  have short := hs.short _ act
  exact ⟨short.trans hh,h _ _ _ (hs.sites _) (hs.sites _) distinct short⟩

end Shortening.Adaptive

end BorderVNP
end Computability
end OAI
