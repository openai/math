import OAI.Computability.BorderVNP.DiagonalExternalFragmentSourceWords
import OAI.Computability.BorderVNP.DiagonalExternalFragmentDestinations
import OAI.Computability.BorderVNP.CubeHostScatterPhysicalReadback

/-! # End-bank reads at the canonical supplied addresses of each native host owner -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal.ExternalSew.Fragments

open Crossing Packing Packing.CellAddresses BorderVNP.Cube Cube.Physical Cube.NativeIntervals
open Cube.HostAddress Cube.HostScatter Cube.Tally VPVNP.MotifBase
open RoutingISA VPVNP.BurstRAM
open private ordinal_val from OAI.Computability.BorderVNP.DiagonalExternalFragmentCables

variable {D C m n M dim d blocks b h K s W : ℕ} {P Team : Type} [Fintype P]
    {bits : P → ℕ} (N : Network D P bits) (cell : N.Site → Fin C)
    (edgeID : N.Edge ↪ Fin m) (portID : P ↪ Fin n) (il : NativeIntervals.Layout)
    (ord : N.CrossingEdge cell ≃ Fin M) (row : Fin M ↪o Fin il.count)
    (label : Fin C → Label (dim+1) d) (axis : Fin (dim+1)) (group : Fin d → Team) (num : Team ↪ ℕ)
    (pub : Team → Arg → Word W) (initial : Team → Memory W) (origin stride : ℕ)

/-- The native chooser, bin scan, cell owner and actual host cable rows used
by the source readback. There are no assumptions on the values at the written
crossing-word destinations. -/
structure HostTables (before scan : Team → ℕ → ℕ) (hz : d^(dim+1)=il.alphabet) : Prop where
  resident : ∀ t, ResidentRows (hostLayout pub initial t) il (before t) (scan t) (readings (initial t)) dim d blocks b h K s
  physical : ∀ t, PhysicalRows N cell il (before t) ord row Fin.valEmbedding label (productCode dim d il.alphabet hz)
  image : ∀ t, il.Image (before t) il.count (scan t)
  teamID : ∀ t, (hostLayout pub initial t).team = num t
  cellOwner : ∀ t c, readings (initial t) ((hostLayout pub initial t).cells+2*c.val) = num (group (label c axis))
  cables : ∀ t, CableRows N cell edgeID portID (hostLayout pub initial t) (readings (initial t))
  rowID : ∀ e, (row (ord e)).val = (edgeID e.val).val
  bases : ∀ t (c : Fin C), readings (initial t) ((hostLayout pub initial t).cells+2*c.val+1) = origin+c.val*stride
  room : ∀ c, suppliedSize N cell c ≤ stride

variable {before scan : Team → ℕ → ℕ} {hz : d^(dim+1)=il.alphabet}
    (tab : HostTables (blocks := blocks) (b := b) (h := h) (K := K) (s := s)
      N cell edgeID portID il ord row label axis group num pub initial origin stride before scan hz)
    {single : SingleSlot dim d blocks (h*b) → Bool} {ends : Packet dim d blocks → Ends dim → Fin (h*b) → Bool}
    (banks : EndBanks axis group (fun t => (hostLayout pub initial t).packets) (fun t => (hostLayout pub initial t).singles)
      (fun t => readings (initial t)) single ends K s)
    (cap : ∀ u, load (cablePair ord (crossSrc N cell) (crossDst N cell) label)
      (crossWidth N cell ∘ ord.symm) u ≤ blocks*(h*b))

/-- The per-cell natural-word memory after the native owner has scattered its
packet and singleton bits, before writing the compact bundle and control rows. -/
def hostWords (c : Fin C) : ℕ → ℕ :=
  let t := group (label c axis)
  let l := hostLayout pub initial t
  l.prefix (readings (initial t)) l.count

include tab banks in
/-- The actual owner's host image contains the selected `readEnd` of the physical
packet assignment at the correct directed supplied-word address. -/
theorem host_crossing_word (side : Bool) (e : N.CrossingEdge cell) (j : Fin (N.width e.val)) :
    let c := endpointCell N cell side e
    let slot := packedSlotEmbedding N cell ord label blocks (h*b) cap ⟨e,j⟩
    hostWords label axis group pub initial c (origin+c.val*stride+endpointRow N cell edgeID portID side e+j.val) =
      (readEnd single ends side slot).toNat := by
  intro c slot
  let t := group (label c axis)
  have owners : endOwner axis group side slot.1 = t := by
    have pair := (packedSlot_address N cell ord label blocks (h*b) cap e j).1
    change slot.1 = _ at pair
    unfold endOwner
    rw [pair]
    cases side <;> rfl
  let l := hostLayout pub initial t
  let u : Boundary N cell c := ⟨e,by cases side; exact Or.inl rfl; exact Or.inr rfl⟩
  have h := crossing_after_host (pub := pub) (initial := initial) (number := num) (cells := Fin.valEmbedding)
    cap e j side tab.resident tab.physical tab.image tab.teamID tab.cellOwner
    (fun t => separate_destinations (tab.cables t) origin stride (tab.bases t) tab.room) banks
  dsimp only at h
  change (hostLayout pub initial (endOwner axis group side slot.1)).prefix
    (readings (initial (endOwner axis group side slot.1))) (hostLayout pub initial (endOwner axis group side slot.1)).count
    ((hostLayout pub initial (endOwner axis group side slot.1)).dest (readings (initial (endOwner axis group side slot.1)))
      (row (ord e)).val side+j.val) = _ at h
  rw [owners] at h
  have dest := chosen_dest_lane (tab.cables t) ord row tab.rowID c u side rfl j
  rw [tab.bases t c] at dest
  have idx := ordinal_val N cell edgeID portID c (.inl u) j
  change (suppliedOrdinal N cell c edgeID portID (.inl u) j).val =
    endpointRow N cell edgeID portID side e+j.val at idx
  rw [idx,←Nat.add_assoc] at dest
  change l.prefix (readings (initial t)) l.count (l.dest (readings (initial t)) (row (ord e)).val side+j.val) = _ at h
  change l.prefix (readings (initial t)) l.count _ = _
  rw [←dest]
  exact h

end Diagonal.ExternalSew.Fragments

end BorderVNP
end Computability
end OAI
