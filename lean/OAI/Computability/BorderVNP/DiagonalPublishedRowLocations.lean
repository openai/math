import OAI.Computability.BorderVNP.FiniteCandidateOriginalBitDelivery
import OAI.Computability.BorderVNP.PackedNativeDemandDestination

/-! # The original demand ordinals in the installed private-placement output -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.RoutingOutputs.NativeDemands

open Crossing CellAddresses CellAddressCircuit CellAddressPhysical RoutingISA Directory Directory.PrivateBank
open scoped Classical

variable {D C ne np : ℕ} {P : Type} [Fintype P] {bits : P → ℕ}
    (N : Network D P bits) (cell : N.Site → Fin C) (edgeID : N.Edge ↪ Fin ne) (portID : P ↪ Fin np)
    (dir : Directory.Layout) (old : Fin dir.entries ↪ N.Site) (live : (Fin dir.teams × Fin dir.sites) ↪ P) (gap : ℕ)
    {s d k w word : ℕ} {σ : Type} [Fintype σ] (aux : N.Site → ℕ) (siteID : N.Site ↪ Fin s)
    (F : Fields s ne np C d k w σ) (x : σ → Bool) (head origin : ℕ) (before after : ℕ → ℕ)
    (net : Represents N cell aux siteID edgeID portID F x) (code : ∀ c, (F.cells c).val=c.val)
    (fit : ∀ c, guessedSize N cell c+siteSize N cell c aux+suppliedSize N cell c < 2^w)
    (width : ∀ p, bits (live p)=dir.block)
    (img : Image F (siteID ∘ old) (portID ∘ live ∘ finProdFinEquiv.symm) x origin before)
    (run : (privateLayout head origin ne C dir.entries dir.description gap).Image before dir.entries after)
    (room : (privateLayout head origin ne C dir.entries dir.description gap).Fits word before)
    (bounds : dir.DestinationBounds)

local notation3 (prettyPrint := false) "native" => rows N cell edgeID portID dir old live gap
local notation3 (prettyPrint := false) "recv" => receiver N cell edgeID portID dir old live gap bounds
local notation3 (prettyPrint := false) "span" => fun i : Fin (native).length => (native)[i.val].width
local notation3 (prettyPrint := false) "base" => bases origin ne C dir.entries
local notation3 (prettyPrint := false) "pp" => ISA.placement after (base).privatePairs
local notation3 (prettyPrint := false) "lp" => ISA.placement after (base).livePairs

include net code fit width img run room in
/-- Recover the locations of the native operands in the directory emitted by this
geometry and private placement. Its compacted row numbers are the original demand
ordinals even when one opaque descriptor occupies several rows. -/
noncomputable def publishedRowLocations :
    RowLocations (dir.directory pp lp) Fin.val recv span := by
  let loc (emitted : List Row) := RowLocations emitted Fin.val recv span
  have same := rows_eq_native N cell edgeID portID dir old live gap aux siteID F x head origin before after
    net code fit bounds width img run room
  exact (congrArg loc same).mp (rowLocations N cell edgeID portID dir old live gap bounds)

private theorem sameOrdinal {source target : List Row} {receiver : Fin source.length → Fin C}
    {size : Fin source.length → ℕ} (same : source=target) (origin : RowLocations source Fin.val receiver size)
    (ordered : ∀ i, (origin.ordinal i).val=i.val) (i : Fin target.length) :
    (((congrArg (fun data => RowLocations data Fin.val receiver size) same).mp origin).ordinal i).val=i.val := by
  subst target
  exact ordered i

/-- The physical output uses the native order on the occupied delivery rows. -/
theorem publishedRowLocations_ordinal (i : Fin (dir.directory pp lp).length) :
    ((publishedRowLocations N cell edgeID portID dir old live gap aux siteID F x head origin before after
      net code fit width img run room bounds).ordinal i).val=i.val :=
  sameOrdinal (rows_eq_native N cell edgeID portID dir old live gap aux siteID F x head origin before after
    net code fit bounds width img run room) (rowLocations N cell edgeID portID dir old live gap bounds) (fun _ => rfl) i

include net code fit width img run room in
/-- The two words actually written for a private descriptor are its original
cell number and its bank-relative destination, including a zero-width descriptor
which contributes no occupied directory row. -/
theorem publishedPrivatePlacement (j : Fin dir.entries) :
    pp j.val = ((cell (old j)).val,(destination N cell edgeID portID dir old live gap (.inl j)).2) :=
  placed_destination N cell edgeID portID dir old live gap aux siteID F x head origin before after
    net code fit width img run room (.inl j)

end Packing.RoutingOutputs.NativeDemands

end BorderVNP
end Computability
end OAI
