import OAI.Computability.BorderVNP.CubePhysicalNativeAssignments
import OAI.Computability.BorderVNP.PackedBottomBankWitness

/-! # Extracting bottom-grid private choices from true staged physical cell vectors

Each original bottom copy keeps its independent fine-wire bits at the front of its
private slab. The final stage may place many such copies at one host site. Their
addresses use the actual source offset, copy ordinal and one-copy stride.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cube.Physical.NativeAssignments

open Crossing Packing.CellAddresses Packing.BottomReports
open scoped Classical

variable {D m siteMax n d blocks b h K s : ℕ} {P : Type*} {bits : P → ℕ}
    {Cell : Type} [DecidableEq Cell] (N : Network D P bits) (cell : N.Site → Cell)
    (siteID : N.Site ↪ Fin siteMax) (aux : N.Site → ℕ)

/-- Location of a bottom bundle inside the retained auxiliary bank of an actual final site. -/
structure BottomLocation (slab : Slab) (copies : ℕ) where
  /-- Final host of the inherited original site. -/
  site : N.Site
  /-- First bit of the packed original copies in the site's final staging bank. -/
  offset : ℕ
  /-- All copies fit the declared site-local interval. -/
  fits : offset + copies*slab.stride ≤ aux site

variable {slab : Slab} {copies : ℕ}

/-- Physical site-local address of the selected original copy and one-copy bit. -/
def BottomLocation.lane (p : BottomLocation N aux slab copies) (i : Fin copies) (j : Fin slab.stride) :
    Fin (aux p.site) :=
  ⟨p.offset+(finProdFinEquiv (i,j)).val,(Nat.add_lt_add_left (finProdFinEquiv (i,j)).isLt _).trans_le p.fits⟩

/-- Read a complete original bottom copy from its true site slot in the flat private
vector of its current host cell. -/
noncomputable def BottomLocation.read (p : BottomLocation N aux slab copies)
    (raw : (c : Cell) → Fin (externalBase N cell c aux) → Bool) (i : Fin copies) : Fin slab.stride → Bool :=
  fun j => siteWords N cell (cell p.site) siteID aux
    (privateStaging N cell aux (cell p.site) (raw (cell p.site))) ⟨p.site,rfl⟩ (BottomLocation.lane N aux p i j)

variable {Team : Type*} {J : Type*} (owners : (Packet n d blocks → Selector n K h) → Fin d → Team)
    (slabs : J → Slab) (mult : J → ℕ)

/-- The independent original within-cell wire choices in every bottom copy. -/
abbrev BottomChoices := (j : J) → Fin (mult j) → Fin (slabs j).guessed → Bool

variable (locations : ∀ _q : Routed (b := b) (s := s) owners, ∀ j, BottomLocation N aux (slabs j) (mult j))

/-- Decode every original fine-wire choice from the actual physical bank, independently
of any field values of the selected table entries. -/
noncomputable def extractBottom (q : Routed (b := b) (s := s) owners)
    (raw : (c : Cell) → Fin (externalBase N cell c aux) → Bool) : BottomChoices slabs mult :=
  fun j i => (slabs j).extractGuess (BottomLocation.read N cell siteID aux (locations q j) raw i)

variable (expected : BottomChoices slabs mult → Routed (b := b) (s := s) owners → Expected N cell aux)

/-- The inherited stage retains the one-copy original completion at the true location.
Only the non-guess fields can depend on the supplied data, input pins and use flags. -/
def BottomImages : Prop :=
  ∀ z q j i (g : Fin (guessedSize N cell (cell (locations q j).site)) → Bool),
    ∃ supplied incoming use, ∀ k,
      expected z q (cell (locations q j).site) g ⟨(locations q j).site,rfl⟩ (BottomLocation.lane N aux (locations q j) i k) =
        (slabs j).complete (z j i) supplied incoming use k

omit [DecidableEq Cell] in
/-- The actual decoder is a left inverse for the staged choices of every bottom bundle.
The rest of the current site bank may contain additional inherited data. -/
theorem recover_bottom (images : BottomImages N cell aux owners slabs mult locations expected)
    (q : Routed (b := b) (s := s) owners) (z : BottomChoices slabs mult)
    (raw : Staged N cell siteID aux (expected z q)) :
    extractBottom N cell siteID aux owners slabs mult locations q raw.val = z := by
  funext j i
  let p := locations q j
  let g := privateWires N cell aux (cell p.site) (raw.val (cell p.site))
  obtain ⟨u,x,r,body⟩ := images z q j i g
  have atSite := raw.property (cell p.site)
  have read : BottomLocation.read N cell siteID aux p raw.val i = (slabs j).complete (z j i) u x r := by
    funext k
    exact (congrFun (congrFun atSite ⟨p.site,rfl⟩) (BottomLocation.lane N aux p i k)).trans (body k)
  change (slabs j).extractGuess (BottomLocation.read N cell siteID aux p raw.val i) = z j i
  rw [read,Slab.extract_complete]

/-- Reindex native selectors, routed payloads and all complete private vectors by the
actual bottom-grid witnesses and cube path. No abstract decoder or assumed inverse
is required once the final site banks contain the true bottom-copy images. -/
noncomputable def bottomPathEquiv (edgeID : N.Edge ↪ Fin m)
    (images : BottomImages N cell aux owners slabs mult locations expected) :
    CheckedCells N cell siteID aux owners expected (extractBottom N cell siteID aux owners slabs mult locations) ≃
      (BottomChoices slabs mult × Path N cell n d blocks b h K s) :=
  checkedPathEquiv N cell edgeID siteID aux owners expected (extractBottom N cell siteID aux owners slabs mult locations)
    (recover_bottom N cell siteID aux owners slabs mult locations expected images)

end Cube.Physical.NativeAssignments

end BorderVNP
end Computability
end OAI
