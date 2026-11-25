import OAI.Computability.BorderVNP.CellPacketSupplementalMemory

/-! # Memory used by the supplemental record prepass over owned cells -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.CellPacket.Supplement.Batch

open VPVNP.BurstRAM Packing.Directory.ISA DiagonalResidueRAM

/-- A single owned cell's geometry and two private sidecar counters. -/
structure Cell where
  /-- Four control words and the tail address derived from the task directory. -/
  layout : Layout
  /-- Measurements of the real private and public record streams. -/
  data : Data

/-- Addresses read before changing the four descriptors and the merged count. -/
def Cell.sources (c : Cell) (tasks controls i : ℕ) : List ℕ :=
  [tasks+7*i+1,controls+4*i,controls+4*i+1,controls+4*i+2,controls+4*i+3,
    c.layout.tail+1,c.layout.tail+2,c.data.geomBase,c.layout.counters,c.layout.counters+1]

/-- The existing seven-word task row gives the exclusive descriptor endpoint. The four
local controls and the original geometry and sidecar counters supply the remaining words. -/
structure Stored {w : ℕ} (c : Cell) (tasks controls i : ℕ) (m : Memory w) : Prop where
  tailEnd : readings m (tasks+7*i+1) = c.layout.tail+12
  source : readings m (controls+4*i) = c.layout.supplement
  counters : readings m (controls+4*i+1) = c.layout.counters
  merged : readings m (controls+4*i+2) = c.layout.merged
  report : readings m (controls+4*i+3) = c.layout.reportWords
  base : readings m (c.layout.tail+1) = c.data.geomBase
  tailLen : readings m (c.layout.tail+2) = 1+c.data.geomWords+c.layout.reportWords
  geomCount : readings m c.data.geomBase = c.data.geomCount
  suppCount : readings m c.layout.counters = c.data.suppCount
  suppWords : readings m (c.layout.counters+1) = c.data.suppWords

/-- Bounds of the arithmetic operations in the fixed per-cell code. -/
structure Room (c : Cell) (w : ℕ) : Prop where
  tail : c.layout.tail+12 < 2^w
  counters : c.layout.counters+1 < 2^w
  base : c.data.geomBase+1+c.data.geomWords < 2^w
  count : c.data.geomCount+c.data.suppCount < 2^w

/-- The address belongs to neither of this cell's two output regions. -/
def Cell.Outside (c : Cell) (addr : ℕ) : Prop :=
  Supplement.Outside c.layout addr

/-- Chronological effects of the owned-cell prepass, including every descriptor store. -/
def written {w : ℕ} (m : Memory w) (cells : ℕ → Cell) : ℕ → Memory w
  | 0 => m
  | i+1 => Supplement.image (cells i).layout (cells i).data (written m cells i)

/-- The scan leaves a physical word intact throughout every interval of cells whose
descriptor and count writes avoid it. -/
theorem preserve {w i j : ℕ} (m : Memory w) (cells : ℕ → Cell) (ij : i ≤ j) (addr : ℕ)
    (outside : ∀ k, i ≤ k → k < j → (cells k).Outside addr) :
    written m cells j addr = written m cells i addr := by
  induction j with
  | zero => have := Nat.eq_zero_of_le_zero ij; subst i; rfl
  | succ j ih =>
    by_cases done : i = j+1
    · rw [done]
    · rw [written,Supplement.image_outside _ _ _ (outside j (by omega) (by omega))]
      exact ih (by omega) fun k hk hj => outside k hk (by omega)

/-- A later owned cell reads the original producers when every earlier descriptor and
merged-count write avoids its ten source addresses. -/
theorem stored_prefix {w tasks controls i : ℕ} (m : Memory w) (cells : ℕ → Cell)
    (init : Stored (cells i) tasks controls i m)
    (separated : ∀ k < i, ∀ addr ∈ (cells i).sources tasks controls i, (cells k).Outside addr) :
    Stored (cells i) tasks controls i (written m cells i) := by
  have keep (addr : ℕ) (h : addr ∈ (cells i).sources tasks controls i) :
      readings (written m cells i) addr = readings m addr :=
    congrArg Fin.val (preserve m cells (i := 0) (Nat.zero_le _) addr (fun k _ hk => separated k hk addr h))
  constructor <;> rw [keep _ (by simp [Cell.sources])] <;> first
    | exact init.tailEnd | exact init.source | exact init.counters | exact init.merged | exact init.report
    | exact init.base | exact init.tailLen | exact init.geomCount | exact init.suppCount | exact init.suppWords

/-- The four actual triples of any owned cell survive the rest of the prepass when
later descriptor and count writes are disjoint from this cell's descriptor interval. -/
theorem descriptor_at {w i count : ℕ} (m : Memory w) (cells : ℕ → Cell) (hi : i < count)
    (j : Fin (Supplement.descriptors (cells i).layout (cells i).data).length)
    (apart : ∀ k, i < k → k < count → (cells k).Outside ((cells i).layout.tail+j.val)) :
    written m cells count ((cells i).layout.tail+j.val) =
      word w (Supplement.descriptors (cells i).layout (cells i).data)[j] := by
  rw [preserve m cells (i := i+1) hi _ (fun k hk hc => apart k hk hc),written,Supplement.image,
    putWords_read _ _ _ ⟨j.val,by simpa only [List.length_map] using j.isLt⟩]
  simp

/-- Read the actual merged public and private count at the end of the batch. -/
theorem merged_at {w i count : ℕ} (m : Memory w) (cells : ℕ → Cell) (hi : i < count)
    (self : (cells i).layout.merged < (cells i).layout.tail ∨
      (cells i).layout.tail+12 ≤ (cells i).layout.merged)
    (apart : ∀ k, i < k → k < count → (cells k).Outside (cells i).layout.merged) :
    written m cells count (cells i).layout.merged = word w ((cells i).data.geomCount+(cells i).data.suppCount) := by
  rw [preserve m cells (i := i+1) hi _ (fun k hk hc => apart k hk hc),written,Supplement.image,
    putWords_outside _ _ _ _ (by simpa only [List.length_map,Supplement.descriptors,
      List.length_cons,List.length_nil] using self),Function.update_self]

end RoutingISA.CellPacket.Supplement.Batch

end BorderVNP
end Computability
end OAI
