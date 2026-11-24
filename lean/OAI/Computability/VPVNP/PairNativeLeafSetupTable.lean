import OAI.Computability.VPVNP.PairNativeFrameRun
import OAI.Computability.VPVNP.PairNativeCacheRun

/-! # One native instruction block for initializing a vertex's leaf verifier

The first part installs the descriptor geometry and supplies the cache base
to the operand compiler. One deterministic jump enters the compiler, which
writes the 38 auxiliary-counter operands before returning to the vertex body.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.NativeLeafSetup

open BurstRAM PrivateRAM LiveProgram PrimedInputRAM NativeOperands
open scoped Fin.CommRing

variable {r p : ℕ}

attribute [local irreducible] NativeOperands.capacity NativeOperands.saved

/-- Register assignment for the terminal geometry and the auxiliary operand cache. -/
structure Placement (count : ℕ) (slot : Fin count) (r : ℕ) where
  /-- Fixed port degree of the final layer. -/
  degree : ℕ
  /-- Numerator of the live bucket exponent. -/
  numerator : ℕ
  /-- Denominator of the live bucket exponent. -/
  denominator : ℕ
  /-- Registers used by the geometry reader and private store loop. -/
  frame : NativeFrame.Ports r
  /-- Registers used by the auxiliary operand compiler. -/
  cache : Fin count ↪ Fin r
  basePort : frame.cache = cache slot
  histogramPort : frame.hist ∉ Set.range cache

/-- The geometry and cache components with the compiler's saved base register. -/
abbrev Block (c : Constants) (r : ℕ) := Placement (NativeCache.bankSize c) (saved (NativeCache.args c)) r

variable {c : Constants} (K : Block c r)

/-- Native geometry calculation preceding the private stores. -/
abbrev frameFlow := K.frame.code K.degree
/-- Native expression evaluator that precedes the cache writes. -/
abbrev cacheFlow := NativeCache.code c K.numerator K.denominator K.cache
/-- Number of program-counter locations reserved for geometry installation. -/
abbrev frameSize := NativeFrame.Table.size (frameFlow K)
/-- Number of program-counter locations reserved for the operand cache. -/
abbrev cacheSize := NativeCacheTable.size (cacheFlow K)
/-- Number of locations in the concatenated instruction table. -/
abbrev size := frameSize K + cacheSize K

/-- Include a geometry instruction address in the combined table. -/
def framePC (j : Fin (frameSize K)) : Fin (size K) := j.castAdd (cacheSize K)
/-- Include a cache instruction address after the geometry block. -/
def cachePC (j : Fin (cacheSize K)) : Fin (size K) := j.natAdd (frameSize K)
/-- First instruction executed by the geometry reader. -/
def entry := framePC K (NativeFrame.Table.label (frameFlow K) (frameFlow K).entry)
/-- Destination of the jump from geometry installation to cache computation. -/
def cacheEntry := cachePC K (NativeCacheTable.label (cacheFlow K) (cacheFlow K).entry)
/-- Location where the caller's continuation replaces the cache return. -/
def done := cachePC K (NativeCacheTable.done (cacheFlow K))

/-- Unconditional native jump to the cache initializer. -/
def handoff (pc : Fin (size K) → Fin p) : Instr 2 p r 11 :=
  .jumpEq K.frame.cache K.frame.cache (pc (cacheEntry K)) (pc (cacheEntry K))

/-- Opcode of the combined table with all program counters relocated. -/
def row (pc : Fin (size K) → Fin p) (ret : Instr 2 p r 11) : Fin (size K) → Instr 2 p r 11 :=
  Fin.addCases (K.frame.row K.degree (pc ∘ framePC K) (handoff K pc))
    (NativeCacheTable.row (cacheFlow K) (NativeCache.storeSrc c K.cache) (NativeCache.ptr c K.cache)
      (NativeCache.one c K.cache) (pc ∘ cachePC K) ret)

theorem frame_row (pc : Fin (size K) → Fin p) (ret : Instr 2 p r 11) (j : Fin (frameSize K)) :
    row K pc ret (framePC K j) = K.frame.row K.degree (pc ∘ framePC K) (handoff K pc) j :=
  Fin.addCases_left ..

theorem cache_row (pc : Fin (size K) → Fin p) (ret : Instr 2 p r 11) (j : Fin (cacheSize K)) :
    row K pc ret (cachePC K j) = NativeCacheTable.row (cacheFlow K)
      (NativeCache.storeSrc c K.cache) (NativeCache.ptr c K.cache) (NativeCache.one c K.cache)
      (pc ∘ cachePC K) ret j := Fin.addCases_right ..

/-- Standalone eleven-operand table with an accepting continuation. -/
def template : Template (size K) r 11 := ⟨2, entry K, row K id .accept⟩

end PairSimulation.NativeLeafSetup

end VPVNP
end Computability
end OAI
