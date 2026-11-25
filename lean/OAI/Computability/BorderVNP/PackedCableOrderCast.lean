import OAI.Computability.BorderVNP.PackedNativeDemandLabels

/-! # Reindexing the padded sparse cable directory -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.RoutingOutputs.NativeDemands

open Crossing BorderVNP.Cube BorderVNP.Cube.Physical

variable {D C ne ne' : ℕ} {P : Type} {bits : P → ℕ} (N : Network D P bits)
    (cell : N.Site → Fin C) (edge : N.Edge ↪ Fin ne) (he : ne=ne')

/-- Transporting the length of the ambient sparse cable table preserves
the order of the occupied crossing edges. -/
theorem cableOrder_cast :
    cableOrder N cell (edge.trans (finCongr he).toEmbedding) = cableOrder N cell edge := by
  subst ne'
  rfl

/-- On the transported table each live bit occupies its original directed
packet slot, including its ordinal within the cable. -/
theorem packedSlotEmbedding_cast_cables {n d : ℕ} (labels : Fin C → Label (n+1) d) (blocks bc : ℕ)
    (pack : ∀ u, load (cablePair (cableOrder N cell edge) (crossSrc N cell) (crossDst N cell) labels)
      (crossWidth N cell ∘ (cableOrder N cell edge).symm) u ≤ blocks*bc)
    (pack' : ∀ u, load (cablePair (cableOrder N cell (edge.trans (finCongr he).toEmbedding))
      (crossSrc N cell) (crossDst N cell) labels)
      (crossWidth N cell ∘ (cableOrder N cell (edge.trans (finCongr he).toEmbedding)).symm) u ≤ blocks*bc) :
    packedSlotEmbedding N cell (cableOrder N cell (edge.trans (finCongr he).toEmbedding)) labels blocks bc pack' =
      packedSlotEmbedding N cell (cableOrder N cell edge) labels blocks bc pack := by
  subst ne'
  rfl

variable [Fintype P] {np : ℕ} (port : P ↪ Fin np) (dir : Directory.Layout)
    (old : Fin dir.entries ↪ N.Site) (live : (Fin dir.teams × Fin dir.sites) ↪ P) (gap : ℕ)
    (bounds : dir.DestinationBounds)

/-- Every native destination key retains both its receiving cell and its
slab address under a transport of the padded cable count. -/
theorem destination_cast_cables :
    destination N cell (edge.trans (finCongr he).toEmbedding) port dir old live gap =
      destination N cell edge port dir old live gap := by
  subst ne'
  rfl

local notation3 (prettyPrint := false) "demand[" e "]" => rows N cell e port dir old live gap
local notation3 (prettyPrint := false) "labels[" e "," n "," d "," hd "]" =>
  meanPackedLabel N cell (receiver N cell e port dir old live gap bounds)
    (fun i : Fin (demand[e]).length => (demand[e])[i.val].width) (List.finRange C) n d hd

/-- The selected product labels use the genuine occupied demand widths and
receiver cells. Reindexing the padded cable interval fixes that entire choice. -/
theorem meanPackedLabel_cast_cables (n d : ℕ) (hd : 0<d) :
    labels[edge.trans (finCongr he).toEmbedding,n,d,hd] = labels[edge,n,d,hd] := by
  subst ne'
  rfl

local notation3 (prettyPrint := false) "ordered[" e "]" => cableOrder N cell e
local notation3 (prettyPrint := false) "bins[" e "," n "," d "," hd "]" =>
  cablePair (ordered[e]) (crossSrc N cell) (crossDst N cell) labels[e,n,d,hd]
local notation3 (prettyPrint := false) "castEdge" => edge.trans (finCongr he).toEmbedding

/-- The true demand labels on the transported table have the original
capacity and send every occupied bit to the prescribed target slot. -/
theorem existsOpenedSlot_cast_cables (n d : ℕ) (hd : 0 < d) (blocks bc : ℕ)
    (target : LiveBit N cell ↪ Slot n d blocks bc)
    (pack : ∀ j, load bins[edge,n,d,hd] (crossWidth N cell ∘ (ordered[edge]).symm) j ≤ blocks*bc)
    (same : packedSlotEmbedding N cell (ordered[edge]) labels[edge,n,d,hd] blocks bc pack = target) :
    ∃ pack' : ∀ j, load bins[castEdge,n,d,hd] (crossWidth N cell ∘ (ordered[castEdge]).symm) j ≤ blocks*bc,
      packedSlotEmbedding N cell (ordered[castEdge]) labels[castEdge,n,d,hd] blocks bc pack' = target := by
  subst ne'
  exact ⟨pack,same⟩

end Packing.RoutingOutputs.NativeDemands

end BorderVNP
end Computability
end OAI
