import OAI.Computability.BorderVNP.PackedRoutingOutputs
import OAI.Computability.BorderVNP.PackedSuppliedOffsetPhysical
import OAI.Computability.BorderVNP.PackedCableColumns

/-! # Physical addressing of all compiled routing subarrays -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.RoutingOutputs

open ParseBatchSort CellAddressCircuit VPVNP.BurstRAM RoutingISA DiagonalResidueRAM

variable {s m n C d k w J A W : ℕ} {σ : Type*} [Fintype σ] (F : Fields s m n C d k w σ)

/-- Starting addresses for the geometry result ABI at frame words 6, 87, 64 and 65. -/
structure Bases where
  /-- Cable triples. -/
  cables : ℕ
  /-- Source and destination relative offsets. -/
  ends : ℕ
  /-- Canonical supplied sizes. -/
  supplied : ℕ
  /-- Scratch counters initialized to zero. -/
  counters : ℕ
  /-- Private original-site placement pairs. -/
  privatePairs : ℕ
  /-- Live grouped-port placement pairs. -/
  livePairs : ℕ

/-- All addresses are public offsets from the output allocation. -/
def bases (origin m C J : ℕ) : Bases :=
  let ends := origin+m*3
  let sizes := ends+m*2
  let counters := sizes+C
  let pp := counters+C
  ⟨origin,ends,sizes,counters,pp,pp+J*2⟩

/-- Values exported by the complete public geometry program at its actual native addresses. -/
structure Image (old : Fin J → Fin s) (ports : Fin A → Fin n) (x : σ → Bool) (origin : ℕ) (mem : ℕ → ℕ) : Prop where
  /-- Original cable order and normalized columns. -/
  cable : ∀ (i : Fin m) (c : Fin 3), mem (origin+i.val*3+c.val) = CableTriples.get (CableTriples.row F x i) c
  /-- The routing suffix's explicit physical word addressing. -/
  columns : ∀ (i : Column m C J A), mem ((bases origin m C J).ends+(order i).val) = entry F old ports x i

variable {F} {old : Fin J → Fin s} {ports : Fin A → Fin n} {x : σ → Bool} {origin : ℕ} {mem : ℕ → ℕ}
    (h : Image F old ports x origin mem)

private def endColumn (i : Fin m) (c : Fin 2) : Column m C J A := .inl (.inl (.inl (.inl (i,c))))
private def sizeColumn (c : Fin C) : Column m C J A := .inl (.inl (.inl (.inr c)))
private def countColumn (c : Fin C) : Column m C J A := .inl (.inl (.inr c))
private def privateColumn (j : Fin J) (c : Fin 2) : Column m C J A := .inl (.inr (j,c))
private def liveColumn (j : Fin A) (c : Fin 2) : Column m C J A := .inr (j,c)

include h

/-- The two source/destination slots for the cell-host scatter are in frame 87. -/
theorem Image.endAt (i : Fin m) (c : Fin 2) :
    mem ((bases origin m C J).ends+i.val*2+c.val) = value fun j =>
      (SuppliedOffsets.frame F).eval x (.inl (endpoint i c),j) := by
  have h' := h.columns (endColumn i c)
  change mem ((bases origin m C J).ends+(c.val+2*i.val)) = _ at h'
  simpa only [endColumn,entry,Nat.add_assoc,Nat.mul_comm i.val 2,Nat.add_comm c.val] using h'

/-- The total words immediately after the endpoint array provide the canonical supplied sizes. -/
theorem Image.suppliedAt (c : Fin C) :
    mem ((bases origin m C J).supplied+c.val) = value fun j => (SuppliedOffsets.frame F).eval x (.inr c,j) := by
  have h' := h.columns (sizeColumn c)
  change mem (origin+m*3+(m*2+c.val)) = _ at h'
  simpa only [sizeColumn,entry,bases,Nat.add_assoc] using h'

/-- The real prefix pass starts with a zero counter in every cell. -/
theorem Image.counterAt (c : Fin C) : mem ((bases origin m C J).counters+c.val) = 0 := by
  have h' := h.columns (countColumn c)
  change mem (origin+m*3+(m*2+C+c.val)) = 0 at h'
  simpa only [bases,Nat.add_assoc] using h'

/-- Initial private rows contain the current owner of each retained original site. -/
theorem Image.privateAt (i : Fin J) :
    Directory.ISA.placement mem (bases origin m C J).privatePairs i = ((data F x).owner (old i),0) := by
  have a := h.columns (privateColumn i 0)
  have b := h.columns (privateColumn i 1)
  change mem (origin+m*3+(m*2+C+C+(0+2*i.val))) = (data F x).owner (old i) at a
  change mem (origin+m*3+(m*2+C+C+(1+2*i.val))) = 0 at b
  exact Prod.ext (by simpa only [bases,Directory.ISA.placement,Nat.zero_add,Nat.mul_comm i.val 2,Nat.add_assoc] using a)
    (by simpa only [bases,Directory.ISA.placement,Nat.mul_comm i.val 2,Nat.add_comm 1,Nat.add_assoc] using b)

/-- A live pair directly addresses its surviving named grouped port in the final cell. -/
theorem Image.liveAt (i : Fin A) :
    Directory.ISA.placement mem (bases origin m C J).livePairs i =
      ((data F x).loc (.inr (ports i)),value fun j => (SuppliedOffsets.frame F).eval x (.inl (.inr (ports i)),j)) := by
  have a := h.columns (liveColumn i 0)
  have b := h.columns (liveColumn i 1)
  change mem (origin+m*3+(m*2+C+C+J*2+(0+2*i.val))) = (data F x).loc (.inr (ports i)) at a
  change mem (origin+m*3+(m*2+C+C+J*2+(1+2*i.val))) = value (fun j => (SuppliedOffsets.frame F).eval x (.inl (.inr (ports i)),j)) at b
  exact Prod.ext (by simpa only [bases,Directory.ISA.placement,Nat.zero_add,Nat.mul_comm i.val 2,Nat.add_assoc] using a)
    (by simpa only [bases,Directory.ISA.placement,Nat.mul_comm i.val 2,Nat.add_comm 1,Nat.add_assoc] using b)

end Packing.RoutingOutputs

end BorderVNP
end Computability
end OAI
