import OAI.Computability.BorderVNP.DiagonalPrivatePathRead

/-! # Recovering one fully tagged mathematical assignment from the checked private banks -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cube.Physical.NativeAssignments

open Crossing Packing.CellAddresses Packing.BottomReports Packing.Inherited Site.Programs Diagonal.CellEntries
open scoped Classical

variable {D ns ne np n d blocks b h K s : ℕ} {P Cell J Param Gadget Team : Type} [Fintype P] [Fintype Cell]
    [DecidableEq Cell] {bits' : P → ℕ} (N : Network D P bits') (cell : N.Site → Cell)
    (siteID : N.Site ↪ Fin ns) (edgeID : N.Edge ↪ Fin ne) (portID : P ↪ Fin np) (state : Site.Programs N)
    (host : J ↪ N.Site) (slabs : J → Slab) (mult : J → ℕ)
    (birthWidth : ∀ j, (state (host j)).birth.work = mult j*(slabs j).stride)
    (owners : (Packet n d blocks → Selector n K h) → Fin d → Team)
    (slot : LiveBit N cell ↪ Slot n d blocks (h*b)) (bank : Ports bits')
    (number : Gadget ↪ ℕ) (tags : BottomChoices slabs mult → N.Tables (Entry Param Gadget))
    (model : ∀ z, TagModels N edgeID portID state (tags z) number (carryPred host (birthPredicate slabs mult z)))

local notation3 "size" => placedSize N state
local notation3 "supply" => pathSupply N cell edgeID portID owners slot bank
local notation3 "whereAt" => (fun (_ : Routed (b:=b) (s:=s) owners) j => retainedLocation N state host slabs mult birthWidth j)
local notation3 "expected" => taggedExpected N cell edgeID portID state host slabs mult owners supply number tags model
local notation3 "extract" => extractBottom N cell siteID size owners slabs mult whereAt
local notation3 "Bank" => (c : Cell) → Fin (externalBase N cell c size) → Bool
local notation3 "full" => taggedCellsEquiv N cell siteID edgeID portID state host slabs mult birthWidth owners supply number tags model

/-- The physical prefix supplied both endpoint zero pins and a successful
original site table with its uniquely completed staging bank in every cell. -/
def CorePassed (q : Routed (b:=b) (s:=s) owners) (raw : (c : Cell) → Fin (externalBase N cell c (placedSize N state)) → Bool) :
    Prop :=
  let z := extract q raw
  let g := fun c => privateWires N cell size c (raw c)
  Path.Pins N cell slot (rawPath N cell edgeID state owners q raw) ∧
    ∀ c (v : {v : N.Site // cell v=c}), (tags z) v.val (localWire N cell edgeID portID owners supply q c (g c) v)
      (localPort N cell edgeID portID owners supply q c v) ≠ 0 ∧
      siteWords N cell c siteID size (privateStaging N cell size c (raw c)) v = expected z q c (g c) v

local notation3 "passes" => CorePassed N cell siteID edgeID portID state host slabs mult birthWidth owners slot bank number tags model

variable (pos : Packet n d blocks → TableEntry n b h K s → Gadget)

/-- The physical predicate splits into its stage-image condition and
the very tag guard used in the polynomial expansion. -/
theorem corePassed_iff (q : Routed (b:=b) (s:=s) owners) (raw : Bank) :
    passes q raw ↔
      (∀ c, siteWords N cell c siteID size (privateStaging N cell size c (raw c)) =
        expected (extract q raw) q c (privateWires N cell size c (raw c))) ∧
      pathTag N cell slot (tags (extract q raw)) bank pos (rawPath N cell edgeID state owners q raw) ≠ 0 := by
  let z := extract q raw
  let path := rawPath N cell edgeID state owners q raw
  rw [pathTag_nonzero_iff]
  constructor
  · rintro ⟨pad,good⟩
    refine ⟨fun c => funext fun v => (good c v).2,pad,?_⟩
    intro v
    have live := (good (cell v) ⟨v,rfl⟩).1
    rw [localWire_path,localPort_path] at live
    exact live
  · rintro ⟨staging,pad,alive⟩
    refine ⟨pad,fun c v => ⟨?_,congrFun (staging c) v⟩⟩
    rw [localWire_path,localPort_path]
    exact alive v.val

/-- Every true physical core with all pads, cells and staged words checked
has exactly one bottom witness and one passing cube path, and conversely.
No field evaluation or total-count hypothesis is used by this bijection. -/
noncomputable def coreEquiv :
    {a : Routed (b:=b) (s:=s) owners × Bank // passes a.1 a.2} ≃
      (Σ z : BottomChoices slabs mult, {p : Path N cell n d blocks b h K s // pathTag N cell slot (tags z) bank pos p ≠ 0}) := by
  let Native := CheckedCells N cell siteID size owners expected extract
  let good := fun p : BottomChoices slabs mult × Path N cell n d blocks b h K s =>
    pathTag N cell slot (tags p.1) bank pos p.2 ≠ 0
  let e : {a : Routed (b:=b) (s:=s) owners × Bank // passes a.1 a.2} ≃ {u : Native // good (full u)} :=
    { toFun a := by
        have ok := (corePassed_iff N cell siteID edgeID portID state host slabs mult birthWidth owners slot bank number tags
          model pos a.val.1 a.val.2).mp a.property
        exact ⟨⟨a.val.1,a.val.2,ok.1⟩,ok.2⟩
      invFun u := ⟨(u.val.1,u.val.2.val),(corePassed_iff N cell siteID edgeID portID state host slabs mult birthWidth
        owners slot bank number tags model pos u.val.1 u.val.2.val).mpr ⟨u.val.2.property,u.property⟩⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  let rest : {p // good p} ≃ (Σ z : BottomChoices slabs mult, {p : Path N cell n d blocks b h K s //
      pathTag N cell slot (tags z) bank pos p ≠ 0}) :=
    ⟨fun p => ⟨p.val.1,p.val.2,p.property⟩,fun p => ⟨(p.1,p.2.val),p.2.property⟩,fun _ => rfl,fun _ => rfl⟩
  exact (e.trans (Equiv.subtypeEquivOfSubtype (p:=good) full)).trans rest

end Cube.Physical.NativeAssignments

end BorderVNP
end Computability
end OAI
