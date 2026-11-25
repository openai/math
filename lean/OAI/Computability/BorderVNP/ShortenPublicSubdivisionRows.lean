import OAI.Computability.BorderVNP.ShortenPublicPaddedCapacity
import OAI.Computability.BorderVNP.ShortenPublicParallelNames
import OAI.Computability.BorderVNP.ShortenEpochRoundPlacedInitial
import OAI.Computability.BorderVNP.ShortenEpochRoundFlatSites
import OAI.Computability.BorderVNP.ShortenPublicEndpointDense

/-!
# Physical row embeddings at epoch boundaries

The sparse rectangles from the capacity recurrence contain the actual sites
and cables. Subdivision preserves all original site IDs and reserves a fixed
range of equality-site and hop numbers for each prior cable, including holes.
Rounding and flattening the external port list leave the same ID maps available.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Shortening.PublicCapacity

open Epoch Cover Crossing CombiningStep PublicEndpoints PublicParallel Adaptive Packing
open scoped Classical

variable {D m : ℕ} {P : Type*} {bits : P → ℕ}

/-- Concrete embeddings of the physical layout into a pair of reserved row arrays. -/
structure Rows (s : Shape) (N : Network D P bits) where
  /-- Stable site row. -/
  site : N.Site ↪ Fin s.sites
  /-- Stable cable row, including space for unused IDs. -/
  edge : N.Edge ↪ Fin s.edges

/-- An ordered run of at most `limit` pieces of each physical edge is stored
in the rectangle for that edge's public ID. -/
private def stripe {E : Type*} {n limit : ℕ} (row : E ↪ Fin n)
    (length : E → ℕ) (fits : ∀ e, length e ≤ limit) :
    (Σ e, Fin (length e)) ↪ Fin (limit*n) where
  toFun z := Fin.cast (Nat.mul_comm n limit) (flat (row z.1) (Fin.castLE (fits z.1) z.2))
  inj' := by
    rintro ⟨e,i⟩ ⟨f,j⟩ he
    have h := finProdFinEquiv.injective (Fin.cast_injective _ he)
    obtain rfl : e=f := row.injective (congrArg Prod.fst h)
    obtain rfl : i=j := Fin.ext (congrArg (fun v => v.2.val) h)
    rfl

namespace Rows

variable {s : Shape} {N : Network D P bits}

/-- Embed an actual wire subdivision at the precise capacities of the public
recurrence. Source and destination sides of an old cable use the same stripe. -/
def subdivide (old : Rows s N) (r : Network.WireRoutes N) (extra : ℕ)
    (fits : ∀ e, r.interior e ≤ extra) : Rows (s.subdivide extra) (N.subdivide r) where
  site := (old.site.sumMap (stripe old.edge r.interior fits)).trans finSumFinEquiv.toEmbedding
  edge := stripe old.edge (fun e => r.interior e+1) (fun e => Nat.succ_le_succ (fits e))

/-- Retained sites keep their exact integer ID under subdivision. -/
theorem subdivide_old (old : Rows s N) (r : Network.WireRoutes N) (extra : ℕ)
    (fits : ∀ e, r.interior e ≤ extra) (v : N.Site) :
    ((old.subdivide r extra fits).site (.inl v)).val = (old.site v).val := rfl

/-- The `j`th equality site of a real cable is in its fixed reserved stripe. -/
theorem subdivide_inner (old : Rows s N) (r : Network.WireRoutes N) (extra : ℕ)
    (fits : ∀ e, r.interior e ≤ extra) (e : N.Edge) (j : Fin (r.interior e)) :
    ((old.subdivide r extra fits).site (.inr ⟨e,j⟩)).val =
      s.sites + (j.val + extra*(old.edge e).val) := rfl

/-- Hop zero is reserved even for an inactive cable with no inserted sites. -/
theorem subdivide_hop (old : Rows s N) (r : Network.WireRoutes N) (extra : ℕ)
    (fits : ∀ e, r.interior e ≤ extra) (e : N.Edge) (j : Fin (r.interior e+1)) :
    ((old.subdivide r extra fits).edge ⟨e,j⟩).val =
      j.val + (extra+1)*(old.edge e).val := rfl

/-- The route compiler needs at most the fixed number of equality sites from
the move catalog. This includes inactive and zero-width cables. -/
theorem route_interior_le {I : Type*} [Fintype I] {K : Type*} {d : ℕ} {L : ℝ}
    {p : Pack D P bits K} (s : SiteRoutes p I d L) (h : ℝ) (e : p.layout.Edge) :
    (s.routes h).interior e ≤ ⌈L/h⌉₊ := by
  simp [SiteRoutes.routes]
  split <;> omega

/-- Actual equality-subdivided input pack of the new epoch, on these same
reserved site and cable rectangles. -/
noncomputable def siteRoutes {I : Type*} [Fintype I] {K : Type*} [CommSemiring K] {d : ℕ} {L : ℝ}
    {p : Pack D P bits K} (old : Rows s p.layout) (r : SiteRoutes p I d L) (h : ℝ) :
    Rows (s.subdivide ⌈L/h⌉₊) (r.subdivided h).layout :=
  old.subdivide (r.routes h) _ (route_interior_le r h)

/-- Port flattening at a rounded epoch boundary preserves the exact layout
numbers, including the physical row of every original private box. -/
def flatten {k b : ℕ} {P : Type} {bits : P → ℕ} {K : Type*}
    {p : Pack D (Port k P b) (width bits k b) K} (old : Rows s p.layout) :
    Rows s (flattenPack b p).layout := ⟨old.site,old.edge⟩

/-- Dense physical ranking changes the allocator order but keeps its sparse
query IDs and its entire site table. -/
noncomputable def dense (old : Rows s N) : Rows s (Names.denseLayout N old.edge) :=
  ⟨old.site,densePublicRows N old.edge⟩

/-- Each child has an entire reserved rectangle in the genuine parallel pack. -/
def parallel {fan : ℕ} {P : Type} {bits : P → ℕ} {K : Type*} {p : Fin fan → Pack D P bits K}
    (child : ∀ i, Rows s (p i).layout) : Rows (s.parallel fan) (parallelPacks p).layout :=
  ⟨parallelName (fun i => (child i).site),parallelName (fun i => (child i).edge)⟩

/-- Complete sparse output row embedding at an actual shortening histogram. -/
noncomputable def sew [NeZero D] {K : Type*} [Field K] (e : PaidIdentity K D m)
    (p : Pack D P bits K) {A : Type} [Fintype A] (bin : p.layout.Edge → Option A)
    (perm : Fin D → Equiv.Perm A) (positive : p.layout.Edge → Bool)
    (hist : Counts e p bin perm) (first : Fin D × Bool) (old : Rows s p.layout)
    {seeds : ℕ} (seed : A ↪ Fin seeds) :
    Rows (s.sew e seeds) (output e p bin perm positive first hist).layout :=
  ⟨StaticRows.siteRows e p old.site seed,StaticRows.outputRows e p bin perm positive first hist old.edge seed⟩

/-- Counts of physical rows never exceed either reserved rectangle. -/
theorem cards (r : Rows s N) : Fintype.card N.Site ≤ s.sites ∧ Fintype.card N.Edge ≤ s.edges := by
  exact ⟨(Fintype.card_le_of_injective _ r.site.injective).trans_eq (Fintype.card_fin _),
    (Fintype.card_le_of_injective _ r.edge.injective).trans_eq (Fintype.card_fin _)⟩

end Rows
end Shortening.PublicCapacity

end BorderVNP
end Computability
end OAI
