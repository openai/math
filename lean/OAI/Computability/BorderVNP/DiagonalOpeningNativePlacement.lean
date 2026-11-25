import OAI.Computability.BorderVNP.DiagonalPinnedPlacementKeys

/-! # Native table addresses for the writer entering the report opener -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.Evaluator

open VPVNP.BurstRAM Packing RoutingOutputs NativeDemands Crossing CellAddresses CellAddressCircuit

variable {D s p d k b w : ℕ} {P σ : Type} [Fintype P] [Fintype σ] {bits : P → ℕ}
    {ar : CubeArena.Layout} (dir : Directory.Layout) (N : Network D P bits) (cell : N.Site → Fin ar.cells)
    (edges : N.Edge ↪ Fin ar.cables) (ports : P ↪ Fin p)
    (original : Fin dir.entries ↪ N.Site) (live : (Fin dir.teams × Fin dir.sites) ↪ P) (gap : ℕ)
    (aux : N.Site → ℕ) (ids : N.Site ↪ Fin s) (F : Fields s ar.cables p ar.cells d k b σ)
    (x : σ → Bool) {pins : Pins.Layout} {pub : Arg → Word w} {after : Memory w}
    {base : ℕ} {I : Type*} [Fintype I] {resides : I → Fin ar.cells} {key : I ↪ ℕ} {size : I → ℕ}

local notation3 (prettyPrint := false) "canonicalPrivate" => privatePair N cell edges ports dir original live gap
local notation3 (prettyPrint := false) "canonicalLive" => livePair N cell edges ports dir original live gap

/-- The retained writer on the middle memory can use the private and live
placement arrays actually read from that memory. Each address comparison is
restricted to an original entry or a live team/site key. -/
noncomputable def SlottedWriter.onNativePlacement
    (writer : SlottedWriter ar dir canonicalPrivate canonicalLive pins pub after base resides key size)
    (head origin : ℕ) (before : Memory w)
    (net : CellAddressPhysical.Represents N cell aux ids edges ports F x) (codes : ∀ c, (F.cells c).val=c.val)
    (extent : ∀ c, guessedSize N cell c+siteSize N cell c aux+suppliedSize N cell c < 2^b)
    (liveWidth : ∀ p, bits (live p)=dir.block)
    (image : Image F (ids ∘ original) (ports ∘ live ∘ finProdFinEquiv.symm) x origin (readings before))
    (placed : (privateLayout head origin ar.cables ar.cells dir.entries dir.description gap).Image
      (readings before) dir.entries (readings after))
    (fit : (privateLayout head origin ar.cables ar.cells dir.entries dir.description gap).Fits w (readings before)) :
    let raw := (privateLayout head origin ar.cables ar.cells dir.entries dir.description gap).raw
    let table := bases origin ar.cables ar.cells dir.entries
    SlottedWriter ar dir (Directory.ISA.placement (readings after) raw)
      (Directory.ISA.placement (readings after) table.livePairs) pins pub after base resides key size :=
  writer.withKeyPlacements (returned_key_placements N cell edges ports dir original live gap
    liveWidth aux ids F x net codes extent head origin (readings before) (readings after) image placed fit)

end RoutingISA.Evaluator

end BorderVNP
end Computability
end OAI
