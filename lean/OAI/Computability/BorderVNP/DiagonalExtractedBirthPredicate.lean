import OAI.Computability.BorderVNP.CubePhysicalRetainedBottom
import OAI.Computability.BorderVNP.PackedFinalCellTaggedGuard
import OAI.Computability.BorderVNP.DiagonalTaggedProgramModels

/-! # The predicate recovered from arbitrary raw physical private bits -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cube.Physical.NativeAssignments

open Crossing Packing.CellAddresses Packing.BottomReports Packing.Inherited Site.Programs
open scoped Classical

variable {J : Type*} (slabs : J → Slab) (mult : J → ℕ)

/-- In each original tile, the guessed fine-wire digits of all copies
are precisely the digits assigned by the independent source witness. -/
def birthPredicate (z : BottomChoices slabs mult) (j : J) (w : ℕ → Bool) : Prop :=
  ∀ (i : Fin (mult j)) (k : Fin (slabs j).guessed), w (i.val*(slabs j).stride+k.val) = z j i k

variable {D ns : ℕ} {P Cell : Type} [Fintype P] [DecidableEq Cell] {widths : P → ℕ}
    (N : Network D P widths) (cell : N.Site → Cell) (siteID : N.Site ↪ Fin ns)
    (state : Site.Programs N) (host : J ↪ N.Site)
    (birthWidth : ∀ j, (state (host j)).birth.work = mult j*(slabs j).stride)
    {n d blocks b h K s : ℕ} {Team : Type*}
    (owners : (Packet n d blocks → Selector n K h) → Fin d → Team)
    (q : Routed (b:=b) (s:=s) owners)

local notation3 "size" => placedSize N state
local notation3 "whereAt" => (fun (_ : Routed (b:=b) (s:=s) owners) j => retainedLocation N state host slabs mult birthWidth j)

/-- Actual original-site tape read from the beginning of its own current
staging slab, before validating any of its retained rows. -/
noncomputable def rawBirth (raw : (c : Cell) → Fin (externalBase N cell c (placedSize N state)) → Bool)
    (v : N.Site) : Fin (state v).birth.work → Bool :=
  let bank := privateStaging N cell size (cell v) (raw (cell v))
  (state v).originalWord (siteWords N cell (cell v) siteID size bank ⟨v,rfl⟩)

omit [DecidableEq Cell] in
/-- Even on malformed, unvalidated work vectors, extracting the bottom
choices fixes exactly the native offset-zero original digits of every
retained site. Fresh sites have the vacuous carried predicate. -/
theorem extracted_compatible (raw : (c : Cell) → Fin (externalBase N cell c (placedSize N state)) → Bool) (v : N.Site) :
    let z := extractBottom N cell siteID size owners slabs mult whereAt q raw
    carryPred host (birthPredicate slabs mult z) v (extendWork (rawBirth N cell siteID state raw v)) := by
  intro z j hv
  subst v
  intro i k
  let site := host j
  let loc := retainedLocation N state host slabs mult birthWidth j
  let L := state site
  have fits : k.val < (slabs j).stride := by
    have sfit := (slabs j).fineFits
    have h := k.isLt
    simp only [Slab.stride,Slab.orig,bottomStride]
    omega
  let offset : Fin (slabs j).stride := ⟨k.val,fits⟩
  let ordinal := finProdFinEquiv (i,offset)
  have index : ordinal.val = i.val*(slabs j).stride+k.val := by
    dsimp [ordinal,finProdFinEquiv,offset]
    ac_rfl
  have lim : i.val*(slabs j).stride+k.val < (state site).birth.work :=
    index ▸ ((birthWidth j).symm ▸ ordinal.isLt)
  change (if h : i.val*(slabs j).stride+k.val < (state site).birth.work then
    rawBirth N cell siteID state raw site ⟨_,h⟩ else false) = (BottomLocation.read N cell siteID size loc raw i) offset
  rw [dite_eq_left lim]
  let actual := siteWords N cell (cell site) siteID size (privateStaging N cell size (cell site) (raw (cell site)))
    ⟨site,rfl⟩
  change actual _ = actual _
  apply congrArg actual
  apply Fin.ext
  change i.val*(slabs j).stride+k.val = 0+ordinal.val
  rw [Nat.zero_add]
  exact index.symm

end Cube.Physical.NativeAssignments

end BorderVNP
end Computability
end OAI
