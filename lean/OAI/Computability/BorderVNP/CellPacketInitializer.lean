import OAI.Computability.BorderVNP.CellPacketLoop
import OAI.Computability.BorderVNP.CellPacketFinish

/-! # A native sparse private-cell packet initializer -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.CellPacket

open VPVNP.BurstRAM RationalHitting.StackLanguage CellPacketEncode Packing.Directory.ISA

/-- Physical intervals of a single scheduled call together with the source interpretation. -/
structure Task where
  /-- First word of the three-word source descriptor array. -/
  descriptorBase : ℕ
  /-- First word of the external assignment bit array. -/
  externalBase : ℕ
  /-- First word of the Boolean scratch interval. -/
  scratchBase : ℕ
  /-- First packed word of the private call argument. -/
  burstBase : ℕ
  /-- Sparse input ranges in private generator order. -/
  chunks : List Chunk
  /-- External input assignment in physical stack order. -/
  external : List Bool

/-- Encoded sparse directory before the private input envelope is added. -/
def Task.packet (t : Task) : List Bool := t.chunks.flatMap Chunk.bits

/-- Complete argument of the sparse private cell, including its input assignment. -/
def Task.payload (t : Task) : List Bool := envelope t.packet t.external

/-- The exact physical packed argument returned by the writer. -/
def Task.burst (t : Task) (w : ℕ) : List (Word w) := CompactFrame.pack w t.payload

/-- Exact chronological memory effect, with scratch digits and actual burst words. -/
def Task.image {w : ℕ} (t : Task) (m : Memory w) : Memory w :=
  putWords (putWords m t.scratchBase (t.payload.map fun b => DiagonalResidueRAM.word w b.toNat))
    t.burstBase (t.burst w)

/-- Initial values of the packet initializer's nine live controls. -/
structure Task.Registers (t : Task) {w : ℕ} (s : Bank w) : Prop where
  constants : Constants (readings s)
  cursor : readings s 2 = t.descriptorBase
  stop : readings s 3 = t.descriptorBase+3*t.chunks.length
  externalBase : readings s 4 = t.externalBase
  externalLength : readings s 5 = t.external.length
  scratch : readings s 6 = t.scratchBase
  burst : readings s 7 = t.burstBase
  width : readings s 8 = w
  write : readings s 20 = t.scratchBase

/-- Source data in the scheduled team's memory before packet construction. -/
structure Task.Stored (t : Task) {w : ℕ} (m : Memory w) : Prop where
  descriptors : WordsAt (readings m) t.descriptorBase (CellPacket.descriptors t.chunks)
  chunks : ∀ c ∈ t.chunks, c.Stored (readings m)
  external : CompactWrite.Source m t.externalBase t.external

/-- Non-overlap and representability of physical machine addresses. -/
structure Task.Room (t : Task) (w : ℕ) : Prop where
  positive : 0 < w
  chunkEnd : ∀ c ∈ t.chunks, c.endSource ≤ t.scratchBase
  tableEnd : t.descriptorBase+3*t.chunks.length ≤ t.scratchBase
  externalApart : CompactWrite.Disjoint t.externalBase t.external.length t.scratchBase t.payload.length
  burstApart : CompactWrite.Disjoint t.scratchBase t.payload.length t.burstBase (t.burst w).length
  sourceFit : t.externalBase+t.external.length < 2^w
  scratchFit : t.scratchBase+t.payload.length < 2^w
  burstFit : t.burstBase+(t.burst w).length ≤ 2^w
  countFit : (t.burst w).length < 2^w

/-- Public code for a complete private-cell argument, independent of all directory data. -/
def initializer : Code := .seq chunksLoop finish

/-- Bound in source-word encoding, private one-copy descriptions, and transmitted bits. -/
def Task.cost (t : Task) (w : ℕ) : ℕ := chunksCost w t.chunks + finishCost t.packet t.external

/-- Execute the complete initializer against actual word-addressed sources. The returned
base and count are exactly the register arguments of the native private call. -/
theorem initializer_run {w : ℕ} (pub : Arg → Word w) (macros : TeamOpcode.Macros w 8)
    (t : Task) (s : Bank w) (m : Memory w) (regs : t.Registers s) (src : t.Stored m) (room : t.Room w) :
    BoundedRun pub macros initializer s m (t.cost w) (fun z =>
      z.reg 5 = t.burstBase ∧ z.reg 15 = (t.burst w).length ∧ z.mem = readings (t.image m)) := by
  let pre := pairWord t.packet
  let post := [true] ++ t.external
  have eq : t.payload = pre++post := envelope_eq t.packet t.external
  have plen : t.payload.length = pre.length+post.length := by rw [eq,List.length_append]
  have fit := room.scratchFit
  rw [plen] at fit
  apply (chunks_run (pub := pub) (macros := macros) t.chunks s m t.descriptorBase t.scratchBase
    regs.constants regs.cursor regs.stop regs.write src.descriptors src.chunks room.chunkEnd room.tableEnd
    (by change t.scratchBase+pre.length<2^w; omega)).seq
  rintro s' m' ⟨per,_,cur,mem⟩
  change readings s' 20 = t.scratchBase + pre.length at cur
  change readings m' = putDigits (readings m) t.scratchBase pre at mem
  have prefixSource : CompactWrite.Source m' t.scratchBase pre := by
    intro i hi
    change readings m' (t.scratchBase+i) = _
    rw [mem]
    exact putDigits_read _ _ _ ⟨i,hi⟩
  have sep : t.externalBase + t.external.length ≤ t.scratchBase ∨
      t.scratchBase+t.payload.length ≤ t.externalBase := room.externalApart
  have ext : CompactWrite.Source m' t.externalBase t.external := by
    intro i hi
    change readings m' (t.externalBase+i) = _
    rw [mem,putDigits_outside _ _ _ _ (by omega)]
    exact src.external i hi
  have suffix : CompactWrite.Disjoint t.externalBase t.external.length (t.scratchBase+pre.length) post.length := by
    unfold CompactWrite.Disjoint; omega
  have stage : m' = putWords m t.scratchBase (pre.map fun b => DiagonalResidueRAM.word w b.toNat) :=
    funext fun i => Fin.ext (congrFun (mem.trans (putDigits_eq_putWords m t.scratchBase pre room.positive)) i)
  have run := finish_run (pub := pub) (macros := macros) s' m' t.packet t.external t.externalBase t.scratchBase
    t.burstBase room.positive (per.constants regs.constants) ((per 4 (by decide)).trans regs.externalBase)
    ((per 5 (by decide)).trans regs.externalLength) ((per 6 (by decide)).trans regs.scratch)
    ((per 7 (by decide)).trans regs.burst) ((per 8 (by decide)).trans regs.width) cur prefixSource ext
    suffix room.burstApart room.sourceFit room.scratchFit room.burstFit room.countFit
  apply run.mono le_rfl
  rintro z ⟨base,count,memory⟩
  refine ⟨base,count,?_⟩
  have join : suffixMemory m' (t.scratchBase+pre.length) t.external =
      putWords m t.scratchBase (t.payload.map fun b => DiagonalResidueRAM.word w b.toNat) := by
    rw [eq,List.map_append,putWords_append,List.length_map,←stage]
    rfl
  change z.mem = readings (putWords (suffixMemory m' (t.scratchBase+pre.length) t.external) t.burstBase (t.burst w)) at memory
  rw [join] at memory
  exact memory

/-- The burst read at the actual returned registers obtains exactly the sparse private input. -/
theorem initializer_burst {w : ℕ} {s : Bank w} {m m' : Memory w} (t : Task)
    (base : readings s 5 = t.burstBase) (count : readings s 15 = (t.burst w).length)
    (mem : readings m' = readings (t.image m)) :
    TeamRAM.previous m' (.burst (s 5).val (s 15).val) = t.burst w := by
  have eq : m' = t.image m := funext fun i => Fin.ext (congrFun mem i)
  change TeamRAM.previous m' (.burst (readings s 5) (readings s 15)) = _
  rw [base,count,eq,Task.image,CompactWrite.previous_putWords]

end RoutingISA.CellPacket

end BorderVNP
end Computability
end OAI
