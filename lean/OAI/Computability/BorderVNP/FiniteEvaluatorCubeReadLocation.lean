import OAI.Computability.BorderVNP.FiniteEvaluatorCubeBanksNative
import OAI.Computability.BorderVNP.FiniteEvaluatorCubeReadSet

/-! # Every live cube operand in the length-only allocation

A later host or task write can affect the cube only at an actual lookup frame
word, an address in the packet/triple region, or a word in the installed
fixed field deck. The physical receiving-cell bank lies between the last
two intervals.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace FiniteEvaluator.CubeAllocation

open VPVNP.BurstRAM RoutingISA DiagonalTallyAllocation DiagonalTallyPacketEmit
open BorderVNP.Cube BorderVNP.Cube.Tally BorderVNP.Cube.Padding.Banks
open private packet_end_le from OAI.Computability.BorderVNP.CubeScatterPaddingBanksSide

variable {F : Type*} [Fintype F] {w : ℕ} (a : CubeArena.Layout)
variable (table : TableEntry a.n a.b a.h a.K a.s → F) (B : Bounds) (l : TypedTaskBuilder.Layout) (sw bw : ℕ)

local notation "deckEnd" => CubeConstants.arenaEnd a.stop (CubeDeck.entry table)
local notation "width" => bankWidth a.n a.b a.h a.K a.s

omit [Fintype F] in
/-- Lookup addresses depend only on the physical vertex triples and the shape of the
fixed deck. The stored words may encode arbitrary scalar positions. -/
theorem read_location_numbered (ids : TableEntry a.n a.b a.h a.K a.s → ℕ) (f : Frame) (dst : ℕ) (tripleBase : f.triples=a.vertexBase)
    (A : Data a.n a.header.d a.header.blocks a.b a.h a.K a.s)
    (placed : A.packetBase=a.header.packetBase) (cap : f.count ≤ a.vertexCap)
    (visits : Fin f.count → Visit a.n a.b a.h a.K a.s) (banks : ∀ i, ∃ p, (visits i).base=A.packetAddr p)
    (demand : ℕ) (pub : Arg → Word w) {addr : ℕ}
    (read : CubePacket.ReadAt
      (CubeDeck.inputs table f a.stop visits dst demand) pub addr) :
    (∃ j ∈ CubePacket.frameWords, addr=(pub 0).val+j) ∨
      (a.header.packetBase ≤ addr ∧ addr<a.cellBank) ∨ (a.stop ≤ addr ∧ addr<CubeConstants.arenaEnd a.stop ids) := by
  have deck : (CubeConstants.arenaEnd a.stop ids) = a.stop+2+(CubeConstants.recipes a.n a.b a.h a.K a.s).length + 2^argumentWidth a.n a.b a.h a.K a.s := by
    simp only [CubeConstants.arenaEnd,CubeConstants.idBase,CubeConstants.ids,List.length_ofFn]
  have positive := Nat.two_pow_pos (argumentWidth a.n a.b a.h a.K a.s)
  have sep := a.separated
  have pack : a.header.packetBase ≤ a.packetEnd := Nat.le_add_right ..
  have packets : a.packetEnd ≤ a.singleBank := by unfold CubeArena.Layout.singleBank; omega
  have publicBelow : a.publicBase ≤ a.cellBank := sep.2.2.2.1.trans (Nat.le_add_right ..)
  have tops : a.vertexBase+3*f.count ≤ a.publicBase := Nat.add_le_add_left (Nat.mul_le_mul_left _ cap) _
  cases read with
  | frame j hj => exact .inl ⟨j,hj,rfl⟩
  | zero =>
    apply Or.inr ∘ Or.inr
    change a.stop ≤ a.stop ∧ a.stop < (CubeConstants.arenaEnd a.stop ids)
    omega
  | one =>
    apply Or.inr ∘ Or.inr
    change a.stop ≤ a.stop+1 ∧ a.stop+1 < (CubeConstants.arenaEnd a.stop ids)
    omega
  | recipe j bound =>
    apply Or.inr ∘ Or.inr
    change a.stop ≤ a.stop+2+j ∧ a.stop+2+j<(CubeConstants.arenaEnd a.stop ids)
    omega
  | value j bound =>
    apply Or.inr ∘ Or.inr
    change a.stop ≤ CubeConstants.idBase a.stop a.n a.b a.h a.K a.s+j ∧
      CubeConstants.idBase a.stop a.n a.b a.h a.K a.s+j < (CubeConstants.arenaEnd a.stop ids)
    unfold CubeConstants.idBase
    omega
  | triple j bound =>
    apply Or.inr ∘ Or.inl
    change a.header.packetBase ≤ f.triples+j ∧ f.triples+j<a.cellBank
    rw [tripleBase]
    change j < 3*f.count at bound
    omega
  | bank i j bound =>
    apply Or.inr ∘ Or.inl
    change a.header.packetBase ≤ (visits i).base+j ∧ (visits i).base+j<a.cellBank
    obtain ⟨p,hp⟩ := banks i
    rw [hp]
    have upper := packet_end_le A p
    rw [placed] at upper
    change A.packetAddr p+width ≤ a.packetEnd at upper
    have lo : A.packetBase ≤ A.packetAddr p := Nat.le_add_right ..
    rw [placed] at lo
    omega

/-- The only three regions reached by the actual allocated finite-field cube lookup. -/
theorem read_location_frame (f : Frame) (dst : ℕ) (tripleBase : f.triples=a.vertexBase)
    (A : Data a.n a.header.d a.header.blocks a.b a.h a.K a.s)
    (placed : A.packetBase=a.header.packetBase) (cap : f.count ≤ a.vertexCap)
    (visits : Fin f.count → Visit a.n a.b a.h a.K a.s) (banks : ∀ i, ∃ p, (visits i).base=A.packetAddr p)
    (demand : ℕ) (pub : Arg → Word w) {addr : ℕ}
    (read : CubePacket.ReadAt
      (CubeDeck.inputs table f a.stop visits dst demand) pub addr) :
    (∃ j ∈ CubePacket.frameWords, addr=(pub 0).val+j) ∨
      (a.header.packetBase ≤ addr ∧ addr<a.cellBank) ∨ (a.stop ≤ addr ∧ addr<deckEnd) :=
  read_location_numbered a table (CubeDeck.entry table) f dst tripleBase A placed cap visits banks demand pub read

/-- The original contiguous task reservation is a specialization of the same lookup read geometry. -/
theorem read_location (A : Data a.n a.header.d a.header.blocks a.b a.h a.K a.s)
    (placed : A.packetBase=a.header.packetBase) {count : ℕ} (cap : count ≤ a.vertexCap)
    (visits : Fin count → Visit a.n a.b a.h a.K a.s) (banks : ∀ i, ∃ p, (visits i).base=A.packetAddr p)
    (demand : ℕ) (pub : Arg → Word w) {addr : ℕ}
    (read : CubePacket.ReadAt
      (CubeDeck.inputs table (frame a table B l sw bw count) a.stop visits (after a table B l sw bw).ids demand) pub addr) :
    (∃ j ∈ CubePacket.frameWords, addr=(pub 0).val+j) ∨
      (a.header.packetBase ≤ addr ∧ addr<a.cellBank) ∨ (a.stop ≤ addr ∧ addr<deckEnd) :=
  read_location_frame a table (frame a table B l sw bw count) (after a table B l sw bw).ids rfl A placed cap visits banks demand pub read

end FiniteEvaluator.CubeAllocation

namespace FiniteDiagonal.FieldRawLayout

open Crossing BorderVNP.Cube BorderVNP.Cube.Physical FiniteEvaluator RoutingISA VPVNP.BurstRAM
open scoped Classical

variable {D w : ℕ} {P : Type} [Fintype P] {bits : P → ℕ} {N : Network D P bits}
variable {F : Type*} [Field F] [Fintype F] {T : N.Tables F} {L : FieldPacketPlan N F} {S : FieldSiteDirectory N T}
variable (V : FieldRawLayout L S) (R : ℕ) (raw : V.Raw R) (t : Fin (R+1))
variable (header profile cells cables maxRows stride : ℕ)
variable (table : TableEntry L.dimension L.bitWidth L.copies L.alternatives L.supply → F)
variable (B : DiagonalTallyAllocation.Bounds) (l : TypedTaskBuilder.Layout) (sw bw : ℕ) (pub : Arg → Word w)

local notation "arena" => planArena L R header profile cells cables maxRows stride
local notation "packetBase" => CubeHeaderInstall.Inputs.packetBase (CubeArena.Layout.header arena)
local notation "fresh" => CubeArena.Layout.stop arena
local notation "f" => CubeAllocation.frame arena table B l sw bw (List.length (teamPairs V R raw t))
local notation "dst" => DiagonalTallyAllocation.AfterTasks.ids (CubeAllocation.after arena table B l sw bw)
local notation "Y" => cubeInputs V R raw t packetBase f rfl table fresh dst

/-- This three-way classification holds at every authentic raw word assignment,
using the native team count and true packet addresses. -/
theorem cubeRead_location {addr : ℕ} (read : CubePacket.ReadAt Y pub addr) :
    (∃ j ∈ CubePacket.frameWords, addr=(pub 0).val+j) ∨
      (packetBase ≤ addr ∧ addr < (arena).cellBank) ∨ (fresh ≤ addr ∧ addr < CubeConstants.arenaEnd fresh (CubeDeck.entry table)) := by
  let A := V.bankData R raw packetBase (arena).singleBank
  have count := CubeAllocation.team_count arena (chosen L.bitWidth L.supply raw.1.1) (Fin.val ∘ V.owners R raw.1.1) t.val
  have bounded : (V.teamPairs R raw t).length ≤ (arena).vertexCap :=
    (congrArg List.length (V.numbered_pairs R raw t)).symm ▸ count
  exact CubeAllocation.read_location arena table B l sw bw A rfl bounded (V.teamVisit R raw packetBase t)
    (fun i => ⟨((V.teamPairs R raw t).get i).1,rfl⟩) D pub read

end FiniteDiagonal.FieldRawLayout

end BorderVNP
end Computability
end OAI
