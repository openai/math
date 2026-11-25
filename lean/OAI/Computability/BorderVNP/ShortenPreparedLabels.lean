import OAI.Computability.BorderVNP.ShortenPreparedBins
import OAI.Computability.BorderVNP.ShortenFramedPacks
import OAI.Computability.BorderVNP.ShortenEpochNeighbors

/-!
# Actual catalog labels, moved cable placement and mean coverage

Every positive short charged cable with endpoints in the current finite
relative site catalog has a common lift of its two endpoints. A single
sample moves all sites of each original pack. On sufficiently deep levels
the canonical charts then fit the physical sorted slots, and their sampled
bin means cover at least half the actual combined charged length.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Shortening.PreparedBins

open Crossing Epoch Cover Cover.Frame Hecke Framed Packing PackMotions CombiningStep Set Filter
open scoped Classical Topology

variable {D : ℕ} {S : Finset (HyperbolicHost (Cube D))} {h η : ℝ}
variable (B : PreparedBins D S h η) {copies d n : ℕ} {P : Type} {bits : P → ℕ} {K : Type*}
variable (input : Fin copies → Pack D P bits K) (active : ∀ i, (input i).layout.Edge → Bool)
variable (sites : ∀ i, (input i).layout.Site → SurfaceHost (Cube D) d)

/-- The ordered relative segment and the integral tile lift of every actual active cable. -/
structure Labels where
  /-- The public index of the relative segment. -/
  kind : Active input active → B.types
  /-- One jointly chosen tile lift for both endpoints. -/
  lift : Active input active → Cube D → gamma 1
  src : ∀ w : Active input active, productProjection _ (translatePoint (lift w) (kind w).val.ends.1) =
    sites w.1 ((input w.1).layout.src w.2.val)
  dst : ∀ w : Active input active, productProjection _ (translatePoint (lift w) (kind w).val.ends.2) =
    sites w.1 ((input w.1).layout.dst w.2.val)
  length : ∀ w : Active input active,
    dist (sites w.1 ((input w.1).layout.src w.2.val)) (sites w.1 ((input w.1).layout.dst w.2.val)) =
      2*(kind w).val.radius

/-- The geometric catalog applies to every actual input pack in a combining step. -/
theorem exists_labels (sites : ∀ i, (input i).layout.Site → SurfaceHost (Cube D) (d+1))
    (hc : ∀ i v, Catalog.relative d (sites i v) ∈ S)
    (hn : ∀ w : Active input active, sites w.1 ((input w.1).layout.src w.2.val) ≠
      sites w.1 ((input w.1).layout.dst w.2.val))
    (hs : ∀ w : Active input active, dist (sites w.1 ((input w.1).layout.src w.2.val))
      (sites w.1 ((input w.1).layout.dst w.2.val)) ≤ 2*h) : Nonempty (Labels B input active sites) := by
  have H (w : Active input active) := B.represents d _ _ (hc w.1 _) (hc w.1 _) (hn w) (hs w)
  choose t ht b hb using H
  exact ⟨⟨fun w => ⟨t w,ht w⟩, b,fun w => (hb w).1,fun w => (hb w).2.1,
    fun w => (hb w).2.2.symm.trans (t w).dist_ends⟩⟩

/-- The absolute address of a charted relative midpoint is its selected tile even on a seam. -/
theorem tileProject_address (t : Cube D → Deck (d+1)) (c : HyperbolicHost (Cube D))
    (hc : c ∈ relativeWindow (Cube D)) : productTileName d (tileProject t c) = t := by
  funext i
  change ((toBaseTile (gammaSL 1 (deckRep t i) • c i))⁻¹ : Deck (d+1)) = t i
  have he : toBaseTile (c i) = 1 := (existsUnique_mem_planeTile 0 (c i)).unique (toBaseTile_mem _)
    (by simpa using hc i)
  rw [toBaseTile_smul,he,one_mul,QuotientGroup.mk_inv,inv_inv]
  exact QuotientGroup.out_eq' _

/-- One test chart, indexed by the full relative type and its direction bin. -/
abbrev Bin := Σ t : B.types, Fin (B.chart t).bins

/-- Old segment length at each relative type. -/
def length (t : B.types) := 2*t.val.radius

/-- The tag function underlying the actual finite sample distribution. -/
noncomputable def tag (kind : Active input active → B.types) (b : Active input active → Cube D → gamma 1) :=
  sampledBin (depth := d) (n := n) input active
    (fun w => speed (kind w).val) (fun w x => (⟨kind w,(B.chart (kind w)).code x⟩ : B.Bin))
    (fun w => sourceFrame (kind w).val (b w)) (fun w => movedCarry (kind w).val (b w))

end Shortening.PreparedBins

end BorderVNP
end Computability
end OAI
