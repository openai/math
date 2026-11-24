import OAI.Computability.VPVNP.PrimedCounterProgram
import OAI.Computability.VPVNP.PrimedCounterAdminInitial
import OAI.Computability.VPVNP.PrimedInputRAMOpcodeExecutionLayout

/-!
# Parameters and initial memory for the uniform coefficient counter

The public table contains dimensions, the literal prefix, the root state and
the fixed offsets used by the native program. The exterior bits and nominated
histogram are loaded from the actual initial external memory. The same code
is used for every pair and for every nomination.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PrimedCounter

open BurstRAM PrimedInputRAM PrimedStackRAM
open scoped Fin.CommRing

variable {L : Lengths} {n r H s w : ℕ}

/-- Parameters for counting one primed pair coefficient at the given RAM layout and grammar
state count. -/
structure Data (Q : Layout L n r H w) (s : ℕ) where
  /-- Degree index installed in the pending root frame of every site's parse. -/
  degree : Fin n
  /-- Grammar state required at the root of every site's parse. -/
  root : Fin s
  /-- The fixed Boolean header data for the two groups, including the exterior fields. -/
  header : Header L → Bool
  /-- Requested multiplicity of each terminal and binary production in the pair's aggregate
  parse histogram. -/
  nomination : Label n n (Fin s) →₀ ℕ

namespace Data

variable {Q : Layout L n r H w}

/-- Address of the assembled input rectangle and beginning of the parser's working layout,
immediately after first-pass scratch. -/
abbrev base (_D : Data Q s) := Q.scratchBase + PrimedInputRAM.positions n r
/-- Number of scheduled calls in the two input-assembly passes, one per rectangular position
per pass. -/
abbrev assembly (_D : Data Q s) := PrimedInputRAM.positions n r + PrimedInputRAM.positions n r
/-- Number of dense production counters that the final comparison scans. -/
abbrev labels (_D : Data Q s) := labelCount n n s
/-- Total number of scheduled calls for both input passes, all site parses and all histogram
comparisons. -/
abbrev total (D : Data Q s) := Cursor.calls D.assembly (2 * 2^r) n (2*n-1) D.labels
/-- Private instruction allowance per call, covering input address computation and the parser's
word operations. -/
abbrev fuel (_D : Data Q s) := max (Opcodes.nativeFuel r+20) (12*w+110)

/-- All slots of the actual machine word and both work arrays used by one invocation. -/
structure Fits (D : Data Q s) : Prop where
  assembler : Opcodes.ParameterFit Q
  degree_eq : D.degree.val + 1 = n
  headers : Header.count L + D.labels ≤ Q.scratchBase
  scratch : D.base + size (2^r) n n D.labels ≤ 2^w
  states : s < 2^w
  word : 2 < 2^w
  triangle : n^2 ≤ 2^w
  cursor : D.total < 2^w
  nomination (a : Label n n (Fin s)) : D.nomination a < 2^w

/-- Fourteen parser operands including scratch layout, root degree, root state and nomination
base address. -/
def parserPub (D : Data Q s) : Fin 14 → Word w :=
  Fin.append (publicData w D.base (2^r) n n s)
    ![(D.degree.val : Word w), (D.root.val : Word w), (Header.count L : Word w)]

/-- The full public operand vector combining input assembly, parsing and the absolute schedule
boundaries. -/
def pub (D : Data Q s) : Fin 34 → Word w :=
  Program.publicWords (Opcodes.pubWord Q) D.parserPub D.assembly (2*2^r) n (2*n-1) D.labels

/-- The uniform coefficient-counting instruction table instantiated at the selected word width
and public operands. -/
abbrev machine (D : Data Q s) := Program.table.instantiate w D.pub

/-- The requested count at a dense label index, encoded as one machine word. -/
noncomputable def nominatedWord (D : Data Q s) (i : Fin D.labels) : Word w :=
  Fin.ofNat _ (D.nomination ((labelIndex n n s).symm i))

/-- The nominated counts as a list of machine words in the parser's dense production order. -/
noncomputable def hist (D : Data Q s) : List (Word w) := List.ofFn D.nominatedWord

/-- Initial external memory with the pair header followed by its nominated histogram. -/
noncomputable def initial (D : Data Q s) : Memory w := headerMemory L D.header D.hist

/-- The primed processor input bits for a site in either group, assembled from its fixed header
and the shared internal assignment. -/
def input (D : Data Q s) (bits : Internal L r H w → Bool) (g : Fin 2) (v : Fin (2^r)) :=
  PrimedInputRAM.input Q.program Q.fits D.header bits (g,v)

/-- All words in the reserved nomination region have the values prescribed by this pair's
histogram. -/
def Nominated (D : Data Q s) (mem : Memory w) := ∀ j, mem (Header.count L+j.val) = D.nominatedWord j

/-- Parser memory relation including the reserved nomination words. -/
def Holds (D : Data Q s) (bits : Internal L r H w → Bool) (st : VisitState n n s) (mem : Memory w) : Prop :=
  PrimedStackRAM.Holds D.base (D.input bits) st mem ∧ D.Nominated mem

theorem parserPub_stack (D : Data Q s) : D.parserPub ∘ Admin.stackPublic = publicData w D.base (2^r) n n s := by
  funext i
  exact Fin.append_left ..

theorem parserPub_root (D : Data Q s) :
    D.parserPub 11 = (D.degree.val : Word w) ∧ D.parserPub 12 = (D.root.val : Word w) ∧
      D.parserPub 13 = (Header.count L : Word w) := by
  have he (j : Fin 3) : D.parserPub (j.natAdd 11) =
      (![(D.degree.val : Word w), ↑D.root.val, ↑(Header.count L)] : Fin 3 → Word w) j := Fin.append_right ..
  exact ⟨he 0, he 1, he 2⟩

/-- The native input passes start the traversal with zero counters, no marks
and no pending frames, while preserving every nomination word. -/
theorem assembled_holds (D : Data Q s) (hf : D.Fits) (bits : Internal L r H w → Bool) :
    D.Holds bits ⟨[], ∅, 0⟩ (Q.assembled (encodeBit w) bits D.initial) := by
  have hlen : D.hist.length = D.labels := List.length_ofFn
  have hfit : Header.count L + D.hist.length ≤ Q.scratchBase := hlen ▸ hf.headers
  refine ⟨Admin.assembled_holds Q D.header bits D.hist hfit, ?_⟩
  intro j
  have he := Admin.assembled_nomination Q D.header bits D.hist hfit (j.cast hlen.symm)
  refine he.trans ?_
  change (List.ofFn D.nominatedWord)[j.val] = D.nominatedWord j
  simp only [List.getElem_ofFn]

theorem nominated_value (D : Data Q s) (hf : D.Fits) (j : Fin D.labels) :
    (D.nominatedWord j).val = D.nomination ((labelIndex n n s).symm j) :=
  Nat.mod_eq_of_lt (hf.nomination _)

end Data
end PrimedCounter

end VPVNP
end Computability
end OAI
