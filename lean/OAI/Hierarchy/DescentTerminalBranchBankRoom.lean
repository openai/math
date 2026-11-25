import OAI.Hierarchy.DescentTerminalPlacedChip
import OAI.Hierarchy.DescentTerminalBoot

namespace OAI
/-! # Capacities of the original terminal proposal and lookup banks -/
namespace Hierarchy.DescentTerminalCompiledPrefix.AddressPlan

open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure
open DescentTerminalChipBootWords DescentTerminalChipRuntime DescentTerminalDenseWindow
open DescentTerminalDenseWindowRAM DescentTerminalBinReaddress

noncomputable section

/-- The native reads, their physical extents, and the origin of the scalar output
for one placed terminal chip. -/
structure BranchBanks (K W q piece codes w pool : ℕ) (E : DescentTerminalEmitter.Layout)
    (G : Banks) (cpu : DescentTerminalChipRuntime.Layout) : Prop where
  bounds : ∀ b ∈ [G.scalar.header,G.scalar.payload,G.scalar.pointer], b.Fits w cpu.first
  roomOut : cpu.first + pool < 2^w
  headerBase : G.scalar.header.base = E.scalar
  headerRoom : pool ≤ G.scalar.header.size
  payloadRoom : K*W ≤ G.scalar.payload.size
  ptrRoom : codes+1 ≤ G.scalar.pointer.size
  fits : ∀ b ∈ [G.index,G.formats,G.raw,G.menuStart,G.highField,G.denseROM], b.Fits w cpu.first
  sizes : K*W ≤ G.index.size ∧ K*W ≤ G.formats.size ∧ Menus q (W*piece) ≤ G.menuStart.size ∧
    radix q (W*piece) ≤ G.highField.size ∧ Menus q (W*piece)*(radix q (W*piece)*radix q (W*piece)) ≤ G.denseROM.size
  routeFit : G.gate.Fits w cpu.first ∧ G.joinedX.Fits w cpu.first ∧ G.pointer.Fits w cpu.first ∧ G.routeROM.Fits w cpu.first
  routeSize : 3*(K*W) ≤ G.gate.size ∧ K*W ≤ G.joinedX.size ∧ 2^(DescentTerminalBinFormat.controlBits W q) ≤ G.pointer.size ∧
    2^(DescentTerminalBinFormat.controlBits W q)*2^(sliceWidth W q piece) ≤ G.routeROM.size
  bootCaps : (∀ b ∈ [G.ySlices,G.scalar.payload,G.joinedX,G.xWords], K*W ≤ b.size) ∧
    radix q (W*piece) ≤ G.highField.size ∧ Menus q (W*piece) ≤ G.menuStart.size ∧
    Menus q (W*piece)*(radix q (W*piece)*radix q (W*piece)) ≤ G.denseROM.size ∧
    2^(DescentTerminalBinFormat.controlBits W q) ≤ G.pointer.size ∧
    2^(DescentTerminalBinFormat.controlBits W q)*2^(sliceWidth W q piece) ≤ G.routeROM.size

/-- The address of the final scalar pointer is a genuine machine word. -/
theorem BranchBanks.tableFit {K W q piece codes w pool : ℕ} {E : DescentTerminalEmitter.Layout}
    {G : Banks} {cpu : DescentTerminalChipRuntime.Layout}
    (b : BranchBanks K W q piece codes w pool E G cpu) : codes+1 ≤ 2^w :=
  b.ptrRoom.trans (b.bounds G.scalar.pointer (by simp)).2.1.le

variable {K W q piece w : ℕ} (S : Shape) (I : Input) (base : ℕ)
    (O : DescentPrivateExponentRAM.Banks) (codes front empty : ℕ)

set_option quotPrecheck false
local notation "G" => chipBanks (K:=K) (W:=W) (q:=q) (p:=piece) codes (layout S I base O).emit front empty
local notation "C" => chip S I base

/-- The ten boot banks have one independently rounded physical page per column.
The writable headers and gate allow the entire row pool and three words per gate. -/
theorem branchBanks (original : front + DescentTerminalBoot.total K W q piece codes ≤ base)
    (live : S.terminal.rows = K*W) (space : endAddress S I base < 2^w) :
    BranchBanks K W q piece codes w S.terminal.pool (layout S I base O).emit G C := by
  have nativeBefore : front + total K W q piece codes ≤ base :=
    (Nat.add_le_add_left (Nat.le_add_right _ _) front).trans original
  have room := chip_room S I base O codes front empty nativeBefore live space
  have dd := room.inputDense
  have dr := room.inputRoute
  have dk := room.inputKey
  simp only [DescentTerminalChipRuntime.dense,DescentTerminalDenseWindowRAM.row,Expr.Fits] at dd
  simp only [DescentTerminalChipRuntime.route,sliceLookup,Expr.Fits] at dr
  simp only [DescentTerminalChipRuntime.key,DescentTerminalScalarDispatch.fetch,Expr.Fits] at dk
  have installed (j : Fin 10) : need K W q piece codes j ≤ (bank K W q piece codes front j).size :=
    Nat.le_pow_clog (by decide) _
  have available := DescentTerminalEmitter.Allocation.reserve_fit S.terminal I.indexEvents I.formatEvents
  unfold DescentTerminalEmitter.Allocation.reserve at available
  have rowSpace : 3*(K*W) ≤ DescentTerminalEmitter.Allocation.slab S.terminal I.indexEvents I.formatEvents := by
    rw [←live]
    omega
  have rawSpace : K*W ≤ DescentTerminalEmitter.Allocation.slab S.terminal I.indexEvents I.formatEvents := by omega
  have low : (C).first ≤ (C).keys := by unfold DescentTerminalChipRuntime.Layout.keys; omega
  constructor
  · intro b hb
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
    rcases hb with rfl | rfl | rfl
    · exact dk.1.1
    · exact dk.2.2.2.2.1
    · exact dk.2.2.2.1.1
  · exact (Nat.add_le_add_right low _).trans_lt room.last
  · rfl
  · change S.terminal.pool ≤ DescentTerminalEmitter.Allocation.slab S.terminal I.indexEvents I.formatEvents
    omega
  · exact installed 2
  · exact installed 9
  · intro b hb
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · exact dd.2.2.1.2.2.1
    · exact dd.2.1.2.1
    · exact dd.2.2.1.2.1
    · exact dd.2.1.1
    · exact dd.2.2.1.1
    · exact dd.1
  · exact ⟨rawSpace,rawSpace,installed 5,installed 4,installed 6⟩
  · exact ⟨dr.2.1.2.1,dr.2.2.1,dr.2.1.1,dr.1⟩
  · exact ⟨rowSpace,installed 1,installed 7,installed 8⟩
  · refine ⟨?_,installed 4,installed 5,installed 6,installed 7,installed 8⟩
    intro b hb
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact installed 3
    · exact installed 2
    · exact installed 1
    · exact installed 0

end
end Hierarchy.DescentTerminalCompiledPrefix.AddressPlan

end OAI
