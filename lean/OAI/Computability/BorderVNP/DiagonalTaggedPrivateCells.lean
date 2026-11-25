import OAI.Computability.BorderVNP.DiagonalExtractedBirthPredicate

/-! # The unique physical site staging for prescribed bottom and cube choices -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cube.Physical.NativeAssignments

open Crossing Packing.CellAddresses Packing.BottomReports Packing.Inherited Site.Programs Diagonal.CellEntries
open scoped Classical

variable {D ns ne np : ℕ} {P Cell J Param Gadget : Type} [Fintype P] [DecidableEq Cell]
    {bits' : P → ℕ} (N : Network D P bits') (cell : N.Site → Cell)
    (siteID : N.Site ↪ Fin ns) (edgeID : N.Edge ↪ Fin ne) (portID : P ↪ Fin np)
    (state : Site.Programs N) (host : J ↪ N.Site) (slabs : J → Slab) (mult : J → ℕ)
    (birthWidth : ∀ j, (state (host j)).birth.work = mult j*(slabs j).stride)
    {n d blocks b h K s : ℕ} {Team : Type}
    (owners : (Packet n d blocks → Selector n K h) → Fin d → Team)
    (supply : Routed (b:=b) (s:=s) owners → ∀ c, Fin (suppliedSize N cell c) → Bool)
    (number : Gadget ↪ ℕ) (tags : BottomChoices slabs mult → N.Tables (Entry Param Gadget))
    (model : ∀ z, TagModels N edgeID portID state (tags z) number (carryPred host (birthPredicate slabs mult z)))

local notation3 "size" => placedSize N state
local notation3 "whereAt" => (fun (_ : Routed (b:=b) (s:=s) owners) j => retainedLocation N state host slabs mult birthWidth j)

section Fixed

variable (z : BottomChoices slabs mult) (q : Routed (b:=b) (s:=s) owners) (c : Cell)
    (g : Fin (guessedSize N cell c) → Bool) (v : {v : N.Site // cell v=c})

/-- The physically addressed cable word in the true compact call's core. -/
noncomputable abbrev localWire := fun (e : Incident N v.val) (i : Fin (N.width e.val)) =>
  (wire N cell c edgeID portID v e i).elim g (supply q c)

/-- The physically addressed free input to this original local factor. -/
noncomputable abbrev localPort := fun (p : Attached N v.val) (i : Fin (bits' p.val)) =>
  supply q c (port N cell c edgeID portID v p i)

/-- The prescribed birth work and ordered scalar observations at this
actual incoming cable word and this independent original assignment. -/
noncomputable def tagReadAt :
    let L := state v.val
    let input := Placement.canonical N cell c edgeID portID v g (supply q c) ∘ Fin.cast L.size
    Site.TagRead L.birth (L.retention.readInput input)
      (fun a => carryPred host (birthPredicate slabs mult z) v.val (extendWork a))
      (tags z v.val (localWire N cell edgeID portID owners supply q c g v)
        (localPort N cell edgeID portID owners supply q c v)) number :=
  (model z v.val (localWire N cell edgeID portID owners supply q c g v)
    (localPort N cell edgeID portID owners supply q c v)).some

end Fixed

/-- All true site lanes, including the independent birth work, forced
retained suffixes and the complete physically addressed incidence vector. -/
noncomputable def taggedExpected (z : BottomChoices slabs mult) (q : Routed (b:=b) (s:=s) owners) :
    Expected N cell (placedSize N state) := fun c g v =>
  let L := state v.val
  let x := Placement.canonical N cell c edgeID portID v g (supply q c) ∘ Fin.cast L.size
  let h := tagReadAt N cell edgeID portID state host slabs mult owners supply number tags model z q c g v
  Fin.append (L.retention.complete x h.work) x

local notation3 "expected" => taggedExpected N cell edgeID portID state host slabs mult owners supply number tags model

omit [DecidableEq Cell] in
/-- Reading arbitrary staged words that agree with the complete local
tag models recovers the specified original private choices bit for bit.
Only the actual original digits are used in this inverse. -/
theorem taggedExpected_recovers (z : BottomChoices slabs mult) (q : Routed (b:=b) (s:=s) owners)
    (raw : Staged N cell siteID size (expected z q)) :
    extractBottom N cell siteID size owners slabs mult whereAt q raw.val = z := by
  funext j i k
  let v := host j
  let c := cell v
  let g := privateWires N cell size c (raw.val c)
  let u : {v : N.Site // cell v=c} := ⟨v,rfl⟩
  let read := tagReadAt N cell edgeID portID state host slabs mult owners supply number tags model z q c g u
  let input := Placement.canonical N cell c edgeID portID u g (supply q c) ∘ Fin.cast (state v).size
  have placed := congrFun (raw.property c) u
  have recovered : rawBirth N cell siteID state raw.val v = read.work :=
    (congrArg (state v).originalWord placed).trans ((state v).originalWord_complete input read.work)
  have actual := extracted_compatible slabs mult N cell siteID state host birthWidth owners q raw.val v j rfl i k
  have canonical := read.chosen j rfl i k
  exact actual.symm.trans ((congrArg (fun bits => extendWork bits (i.val*(slabs j).stride+k.val)) recovered).trans canonical)

/-- With the true tagged site observations, every staged routed assignment
is in bijection with independent bottom choices and one complete cube path. -/
noncomputable def taggedCellsEquiv :
    CheckedCells N cell siteID size owners expected (extractBottom N cell siteID size owners slabs mult whereAt) ≃
      (BottomChoices slabs mult × Physical.Path N cell n d blocks b h K s) :=
  checkedPathEquiv N cell edgeID siteID size owners expected (extractBottom N cell siteID size owners slabs mult whereAt)
    (fun q z raw => taggedExpected_recovers N cell siteID edgeID portID state host slabs mult birthWidth owners supply
      number tags model z q raw)

end Cube.Physical.NativeAssignments

end BorderVNP
end Computability
end OAI
