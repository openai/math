import OAI.Computability.BorderVNP.DiagonalSeedTags
import OAI.Computability.BorderVNP.PackedDenseNames

/-! # Actual public pool splitting and simultaneous profile insertion on tagged boxes -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal.CellEntries

open Crossing Shortening SeedIntervals Packing MvPolynomial
open scoped BigOperators Classical

variable {D m b : ℕ} [NeZero D] {P : Type*} {bits : P → ℕ}
    {Team Param Gadget E : Type*} [Field E]
variable (src : Pack D P bits (Entry Param Gadget))
    {A : Type} [Fintype A] (bin : src.layout.Edge → Option A)
    (perm : Fin D → Equiv.Perm A) (m : ℕ)

/-- The physical interval decomposition used by the seed pools. -/
noncomputable def roundPieces : Pack D P bits (Entry Param Gadget) :=
  ⟨src.layout.bands (label src.layout bin perm m),
    src.layout.bandTables (label src.layout bin perm m) src.table⟩

/-- Use-bit readback in the same sparse cable rows selected by the seed allocator. -/
noncomputable def roundPieceWords [Fintype Team] [Fintype Param]
    (words : PowerWords Team Param Gadget b src.layout src.table) :
    PowerWords Team Param Gadget b (roundPieces src bin perm m).layout
      (roundPieces src bin perm m).table where
  site := words.site
  selected := src.layout.bandTables (label src.layout bin perm m) words.selected
  located v _ _ w h := words.located v _ _ w h
  exact v _ _ := words.exact v _ _

variable {m} (e : PaidIdentity E D m) (position : e.Entry → Gadget)
    (positive : src.layout.Edge → Bool) (first : Fin D × Bool)

/-- The output network and its tagged factors for one attained public count tuple. -/
noncomputable def roundTags (q : ProfileCounts e (blocks src.layout bin perm m)) :
    Pack D P bits (Entry Param Gadget) :=
  seedTags (roundPieces src bin perm m) e position (blocks src.layout bin perm m)
    (partition src.layout bin perm m) (bundle src.layout bin perm m positive) first q

/-- The integer row names and intervals in the output agree with the actual
field-valued shortening step used by the geometric recursion. -/
theorem roundTags_layout (fieldTable : src.layout.Tables E)
    (q : ProfileCounts e (blocks src.layout bin perm m)) :
    (roundTags src bin perm e position positive first q).layout =
      (CombiningStep.output e ⟨src.layout,fieldTable⟩ bin perm positive first q).layout := rfl

/-- Every tagged input gives a genuine exact sum of the tagged outputs in
the parameter polynomial ring. The identity uses precisely the same choices
as the public geometry, which consults the row names and widths. -/
theorem roundTags_sum (values : Gadget → E) (lookup : ∀ i, values (position i) = e.entry i)
    (x : Ports bits) :
    (interpretPack values src).tensor x =
      ∑ q, (interpretPack values (roundTags src bin perm e position positive first q)).tensor x :=
  (src.layout.value_bands (label src.layout bin perm m) (interpretPack values src).table x).symm.trans
    (sum_seedTags (roundPieces src bin perm m) e position _ _ _ first values lookup x)

/-- Reading the original parameter bits from the current boxes remains
valid after this particular combining round, including cuts of old gadgets. -/
noncomputable def roundWords [Fintype Team] [Fintype Param]
    (words : PowerWords Team Param Gadget b src.layout src.table)
    (q : ProfileCounts e (blocks src.layout bin perm m)) :
    PowerWords Team Param Gadget b (roundTags src bin perm e position positive first q).layout
      (roundTags src bin perm e position positive first q).table :=
  seedWords (roundPieces src bin perm m) e position _ _ _ first q (roundPieceWords src bin perm m words)

/-- Removing unused sparse row names preserves the local readback at the
original host sites and introduces no extra slot or scalar occurrence. -/
noncomputable def denseWords [Fintype Team] [Fintype Param]
    {M : ℕ} (rows : src.layout.Edge ↪ Fin M)
    (words : PowerWords Team Param Gadget b src.layout src.table) :
    PowerWords Team Param Gadget b (Names.denseLayout src.layout rows)
      (Names.tables src.layout (Names.denseRank src.layout rows).toEmbedding
        (fun i => src.layout.src ((Names.denseRank src.layout rows).symm i)) src.table) where
  site := words.site
  selected := Names.tables src.layout (Names.denseRank src.layout rows).toEmbedding
    (fun i => src.layout.src ((Names.denseRank src.layout rows).symm i)) words.selected
  located v _ _ w h := words.located v _ _ w h
  exact v _ _ := words.exact v _ _

end Diagonal.CellEntries

end BorderVNP
end Computability
end OAI
