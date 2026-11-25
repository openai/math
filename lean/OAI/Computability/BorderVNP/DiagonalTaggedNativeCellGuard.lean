import OAI.Computability.BorderVNP.DiagonalTaggedPrivateCells
import OAI.Computability.BorderVNP.PackedFinalCellFiniteTagged

/-! # The native cell guard for arbitrary, initially unvalidated raw private bits

The source witness is extracted from the actual finite private vector. Its
carried birth predicate holds even if the vector fails a later wiring check.
The merged checked directory then recognizes exactly the physical nonzero
tags and the expected complete site words for that extracted witness.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cube.Physical.NativeAssignments

open Crossing Packing.CellAddresses Packing.BottomReports Packing.Inherited Site.Programs Diagonal.CellEntries CellSparse
open scoped Classical

variable {D ns ne np C : ℕ} {P J Param Gadget : Type} [Fintype P]
    {bits' : P → ℕ} (N : Network D P bits') (cell : N.Site → Fin C)
    (siteID : N.Site ↪ Fin ns) (edgeID : N.Edge ↪ Fin ne) (portID : P ↪ Fin np)
    (state : Site.Programs N) (host : J ↪ N.Site) (slabs : J → Slab) (mult : J → ℕ)
    (birthWidth : ∀ j, (state (host j)).birth.work = mult j*(slabs j).stride)
    {n d blocks b h K s : ℕ} {Team : Type}
    (owners : (Packet n d blocks → Selector n K h) → Fin d → Team)
    (supply : Routed (b:=b) (s:=s) owners → ∀ c, Fin (suppliedSize N cell c) → Bool)
    (number : Gadget ↪ ℕ) (tags : BottomChoices slabs mult → N.Tables (Entry Param Gadget))
    (model : ∀ z, TagModels N edgeID portID state (tags z) number (carryPred host (birthPredicate slabs mult z)))
    (q : Routed (b:=b) (s:=s) owners) (c : Fin C)
    (raw : (c : Fin C) → Fin (externalBase N cell c (placedSize N state)) → Bool)

local notation3 "size" => placedSize N state
local notation3 "whereAt" => (fun (_ : Routed (b:=b) (s:=s) owners) j => retainedLocation N state host slabs mult birthWidth j)
local notation3 "z" => extractBottom N cell siteID size owners slabs mult whereAt q raw
local notation3 "g" => privateWires N cell size c (raw c)
local notation3 "a" => privateStaging N cell size c (raw c)
local notation3 "here" => tagReadAt N cell edgeID portID state host slabs mult owners supply number tags model z q c g
local notation3 "entry" => (fun v : {v : N.Site // cell v=c} =>
  tags z v.val (localWire N cell edgeID portID owners supply q c g v) (localPort N cell edgeID portID owners supply q c v))
local notation3 "expected" => taggedExpected N cell edgeID portID state host slabs mult owners supply number tags model

private def retag {s : Site} {x : Fin s.incoming → Bool} {ok : (Fin s.work → Bool) → Prop}
    {newTag oldTag : Entry Param Gadget} {number : Gadget ↪ ℕ} (eq : newTag=oldTag) (r : Site.TagRead s x ok oldTag number) : Site.TagRead s x ok newTag number where
  work := r.work
  observations := r.observations
  chosen := r.chosen
  read u os h := eq ▸ r.read u os h
  count := eq ▸ r.count

/-- For each finite cell, the authentic compact guard pins the unique complete
staging words of the extracted source and the exact true tag observations. -/
theorem tagged_native_cell_guard (owner : Fin ns → ℕ) (reports : List (List ℕ))
    (ho : ∀ v, owner (siteID v)=(cell v).val) (birthLocal : ∀ v, (state v).birth.Local)
    (schema : ∀ v, (state v).program.Schema) (relative : ∀ v, (state v).program.RelativeBoxes)
    (out : List (Bool × Option ℕ)) :
    let live := FinalCell.sites siteID owner c.val
    let chunks := fun v : N.Site => if hv : cell v=c then (here ⟨v,hv⟩).observations else []
    (FinalCell.directory owner N (fun v => (cell v).val) siteID edgeID portID (fun v => (state v).program)
      c.val reports).guardedObservations (lookup (bank N cell c size g a (supply q c))) = some out ↔
      live.flatMap chunks=out ∧ (∀ v : {v : N.Site // cell v=c}, entry v ≠ 0) ∧
        siteWords N cell c siteID size a = expected z q c g := by
  intro live chunks
  let tag := fun v : N.Site => if hv : cell v=c then entry ⟨v,hv⟩ else 0
  let ok := fun (v : N.Site) (w : Fin (state v).birth.work → Bool) =>
    carryPred host (birthPredicate slabs mult z) v (extendWork w)
  let read := fun v : {v : N.Site // cell v=c} =>
    retag (show tag v.val=entry v from dite_eq_left v.property) (here v)
  have sel (v : {v : N.Site // cell v=c}) : ok v.val ((state v.val).originalWord (siteWords N cell c siteID size a v)) := by
    obtain ⟨v,rfl⟩ := v
    exact extracted_compatible slabs mult N cell siteID state host birthWidth owners q raw v
  have native := FinalCell.guarded_finite_tagged_iff N cell c siteID edgeID portID state owner number tag ok g a (supply q c)
    read reports ho birthLocal schema relative sel out
  apply native.trans
  constructor
  · rintro ⟨flat,each⟩
    refine ⟨flat,?_,funext fun v => (each v).2⟩
    intro v
    have nz := (each v).1
    simpa only [tag,dite_eq_left v.property] using nz
  · rintro ⟨flat,nonzero,staging⟩
    refine ⟨flat,fun v => ⟨?_,congrFun staging v⟩⟩
    simpa only [tag,dite_eq_left v.property] using nonzero v

end Cube.Physical.NativeAssignments

end BorderVNP
end Computability
end OAI
