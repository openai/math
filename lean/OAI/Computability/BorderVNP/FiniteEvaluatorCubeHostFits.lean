import OAI.Computability.BorderVNP.FiniteEvaluatorCubeHostDest
import OAI.Computability.BorderVNP.CubeScatterPaddingArenaRoom

/-! # Address space of the actual host cable scatter

Every cable-table read, including a padded sparse row, lies below the
receiving-cell banks. The native physical-source readback places live bit
sources below the vertex directory. The external bit intervals lie wholly
inside receiving cells, so no copy can change any read of a later row.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace FiniteEvaluator.CubeAllocation

open VPVNP.BurstRAM BorderVNP.Cube RoutingISA Packing
open RoutingOutputs

variable (a : CubeArena.Layout) (frame : ℕ) (mem : ℕ → ℕ)

local notation "H" => HostScatter.Layout.fromFrame frame mem

/-- Static public words and table pointers for the physical host copy. -/
structure HostWords : Prop where
  labels : (H).labels = a.publicBase
  alphabet : (H).alphabet = a.alphabet
  ordinals : (H).ordinals = a.ordinalBase
  cells : (H).cells = a.hostDirectory
  pairs : (H).pairs = a.pairDirectory
  blocks : (H).blocks = a.header.blocks
  width : (H).bc = a.h*a.b
  packetWidth : (H).bankWidth = Tally.bankWidth a.n a.b a.h a.K a.s

private theorem host_order :
    a.header.header ≤ a.cellBank ∧ a.publicBase+a.cells ≤ a.cellBank ∧
      a.ordinalBase+a.cables ≤ a.cellBank ∧ a.hostDirectory+2*a.cells ≤ a.cellBank ∧
      a.pairDirectory+3*a.alphabet^2 ≤ a.cellBank ∧ a.vertexBase ≤ a.cellBank := by
  obtain ⟨_,cells,owners,pair,host,records,pairBase,_⟩ := a.writer_order
  have group := a.group_order
  have power : a.ordinalBase+a.cables=a.powerBase := rfl
  have later : a.pairBase ≤ a.cellBank := Nat.le_add_right ..
  have vertex : a.vertexBase ≤ a.publicBase := Nat.le_add_right ..
  omega

private theorem metadata_low {origin J : ℕ} (header : Header frame origin a.cables a.cells J mem)
    (before : origin+5*a.cables ≤ a.header.header) (words : HostWords a frame mem)
    (names : ∀ i < (H).count, ∀ side, (H).cell mem i side < a.cells → mem ((H).labels+(H).cell mem i side)<a.alphabet) {i x : ℕ} (hi : i<(H).count) (side : Bool)
    (cells : ∀ s, (H).cell mem i s < a.cells) (read : x ∈ (H).rowReads mem i side) : x < a.cellBank := by
  obtain ⟨hs,labelsEnd,ord,host,pair,_⟩ := host_order a
  have src := cells false
  have dst := cells true
  have own := cells side
  have cable : (H).cables=origin := header.cables
  have count : (H).count=a.cables := header.edges
  have relative : (H).relative=origin+a.cables*3 := header.ends
  have bound : (H).key mem i < a.alphabet^2 := by
    rw [HostScatter.Layout.key,words.alphabet,pow_two]
    have le := Nat.mul_le_mul_right a.alphabet (Nat.succ_le_of_lt (names i hi false src))
    rw [Nat.succ_mul] at le
    exact (Nat.add_lt_add_left (names i hi true dst) _).trans_le le
  have bit : side.toNat ≤ 1 := by cases side <;> decide
  simp only [HostScatter.Layout.rowReads, List.mem_cons,List.not_mem_nil,or_false,
    words.cells,words.labels,words.pairs,words.ordinals,cable,relative] at read
  omega

/-- Every numerical side condition and the full immutable-read separation
of the host scatter follow from the physical layout, bounded real sources
and assigned endpoint intervals. Zero-width sparse rows are included. -/
theorem host_fits_of_arena {origin J w : ℕ} (header : Header frame origin a.cables a.cells J mem)
    (before : origin+5*a.cables ≤ a.header.header) (words : HostWords a frame mem)
    (radix : 0 < a.header.d) (width : 0 < a.h*a.b) (room : a.stop < 2^w)
    (names : ∀ i < (H).count, ∀ side, (H).cell mem i side < a.cells → mem ((H).labels+(H).cell mem i side)<a.alphabet)
    (allCells : 0<a.cells → ∀ i < (H).count, ∀ side, (H).cell mem i side<a.cells)
    (positiveCells : ∀ i < (H).count, ∀ side, (H).width mem i ≠ 0 → (H).cell mem i side<a.cells)
    (bank : ∀ c < a.cells, mem (a.hostDirectory+2*c+1)=a.cellBank+c*a.cellStride)
    (slots : ∀ i < (H).count, ∀ side, (H).Owned mem i side →
      mem ((H).relative+2*i+side.toNat)+(H).width mem i ≤ a.cellStride)
    (ordinals : ∀ i < (H).count, ∀ side, (H).Owned mem i side →
      mem ((H).ordinals+i)+(H).width mem i ≤ a.header.blocks*(a.h*a.b))
    (bits : ∀ i < (H).count, ∀ side, (H).Owned mem i side → ∀ j < (H).width mem i, (H).source mem i side j < a.vertexBase) :
    (H).Fits w mem := by
  obtain ⟨secondary,_,_,host,_,vertex⟩ := host_order a
  have bankTop : a.cellBank ≤ a.stop := Nat.le_add_right ..
  have cnt : (H).count = a.cables := header.edges
  have cable : (H).cables = origin := header.cables
  have posBank : 0<Tally.bankWidth a.n a.b a.h a.K a.s := by
    have digit := (Tally.demandOffset_range (K:=a.K) ((0 : Vertex a.n),false) (⟨0,width⟩ : Fin (a.h*a.b))).2
    unfold Tally.bankWidth
    omega
  have stride := (Padding.physicalRoom_of_arena a frame 0 0 radix room).stride
  have dest := host_dest a frame mem words.cells bank
    (fun i hi side owned => ⟨positiveCells i hi side owned.1,slots i hi side owned⟩)
  refine ⟨⟨words.width ▸ width,words.packetWidth ▸ posBank⟩,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · omega
  · omega
  · intro i hi side nz _
    have bound := positiveCells i hi side nz
    rw [words.cells]; omega
  · intro i hi side owns x read
    exact ((metadata_low a frame mem header before words names hi side
      (fun s => positiveCells i hi s owns.1) read).trans_le bankTop).trans room
  · intro i hi side owns j hj
    exact ((bits i hi side owns j hj).trans_le (vertex.trans bankTop)).trans room
  · simpa only [words.blocks,words.width] using stride
  · simpa only [words.blocks,words.width] using ordinals
  · intro i hi side own
    exact (dest i hi side own).2.trans room.le
  · intro i hi side owns x input
    have positive := Nat.zero_lt_of_lt (positiveCells i hi side owns.1)
    obtain ⟨k,hk,s,metadata | ⟨live,j,hj,rfl⟩⟩ := input
    · exact .inl ((metadata_low a frame mem header before words names hk s (allCells positive k hk) metadata).trans_le (dest i hi side owns).1)
    · exact .inl ((bits k hk s live j hj).trans_le (vertex.trans (dest i hi side owns).1))

end FiniteEvaluator.CubeAllocation

end BorderVNP
end Computability
end OAI
