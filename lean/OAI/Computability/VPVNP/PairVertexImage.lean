import OAI.Computability.VPVNP.PairNodeDispatch
import OAI.Computability.VPVNP.PairSimulationCounters

/-!
# The finite native image of a final-vertex call

The site bootstrap and final-wire loader enter a common nine-row DFS.
Its role router and histogram flush obtain their branch-dependent bases
from a private geometry table. The three native role bodies return to the
same child-list header. All labels and registers of the table are finite
and independent of the input length.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.VertexImage

open BurstRAM PrivateRAM
open scoped Fin.CommRing

/-- Stable bootstrap registers, in the terminal caller's order. -/
abbrev Saved := Fin 11
/-- Saved register holding the displacement from DFS node addresses to their role words. -/
def roleOffset : Saved := 0
/-- Saved register for the base address of the private histogram counters. -/
def histBase : Saved := 1
/-- Saved register for the ordinal of the final site being processed. -/
def ordinal : Saved := 2
/-- Saved register for the selected final site's root DFS node address. -/
def root : Saved := 3
/-- Saved register holding the external terminal header address. -/
def header : Saved := 4
/-- Saved register holding the number of final sites from the terminal header. -/
def finalSites : Saved := 5
/-- Saved register holding the count of numbered final arc slots. -/
def slots : Saved := 6
/-- Saved register pointing to the final arc-width column. -/
def widths : Saved := 7
/-- Saved register pointing to the final incoming incidence column. -/
def incoming : Saved := 8
/-- Saved register pointing to the terminal width-prefix column. -/
def prefixBase : Saved := 9
/-- Saved register pointing to the shared final wire-bit interval. -/
def wires : Saved := 10

/-- A relocated block has its own labels and private registers. The common
DFS and bootstrap registers are explicit arguments. Five literal bits cover
the constants of the full cursor-leaf program. -/
structure Segment where
  /-- Number of instructions owned by this linked vertex segment. -/
  count : ℕ
  /-- Number of local registers required by the segment in addition to the DFS and saved banks. -/
  privateRegs : ℕ
  /-- Local instruction ordinal at which control enters the segment. -/
  entry : Fin count
  /-- Instruction generator for this segment under the given program-counter and register
  placements and continuation. -/
  row : ∀ {p r : ℕ}, (Fin count → Fin p) → (Fin 9 ↪ Fin r) → (Saved ↪ Fin r) →
    (Fin privateRegs ↪ Fin r) → Fin p → Fin count → Instr 5 p r 11

/-- The installed components of a terminal vertex computation, from bootstrap and geometry to
the three role handlers and the final return. -/
inductive Part where
  | bootstrap | geometry | rootFields | leaf | shrink | refresh | finish
  deriving DecidableEq

instance : Fintype Part :=
  ⟨{.bootstrap,.geometry,.rootFields,.leaf,.shrink,.refresh,.finish}, fun i => by cases i <;> decide⟩

/-- Choose the leaf, shrink, or refresh instruction segment for a decoded node role. -/
def rolePart : NodeDispatch.Role → Part
  | .leaf => .leaf
  | .shrink => .shrink
  | .refresh => .refresh

/-- Labels of the shared vertex control code, including DFS, packet copying, role dispatch, and
histogram flushing. -/
inductive CorePC where
  | dfs (i : Fin 9)
  | copy (i : Fin 5)
  | roleBase (i : Fin 3)
  | dispatch (i : Fin 6)
  | histBase (i : Fin 3)
  | flushStart (i : Fin 7)
  | flush (i : Fin 7)
  | accept
  deriving DecidableEq, Fintype

variable (S : Part → Segment)

/-- A vertex instruction address is either a shared control label or an instruction ordinal
inside one named segment. -/
abbrev PC := CorePC ⊕ (i : Part) × Fin (S i).count
/-- The vertex register space combines the DFS, saved, and counter banks with a separate local
bank for each segment. -/
abbrev Reg := Fin 9 ⊕ Saved ⊕ Fin 6 ⊕ (i : Part) × Fin (S i).privateRegs

/-- An enclosing program can install the image among its other opcodes. -/
structure Placement (p r : ℕ) where
  /-- Inject the shared and per-segment instruction addresses into the enclosing machine's
  program counters. -/
  pc : PC S ↪ Fin p
  /-- Inject the vertex's named register banks into the enclosing machine's registers. -/
  reg : Reg S ↪ Fin r

namespace Placement

variable {S} {p r : ℕ} (A : Placement S p r)

/-- Place a shared vertex control label at its host program counter. -/
def core (i : CorePC) := A.pc (.inl i)
/-- Place a local instruction ordinal of a named segment at its host program counter. -/
def stage (i : Part) (j : Fin (S i).count) := A.pc (.inr ⟨i,j⟩)
/-- The host program counter of a named segment's designated entry instruction. -/
def entry (i : Part) := A.stage i (S i).entry
/-- Embedding of the nine DFS registers into the host machine. -/
def dfs : Fin 9 ↪ Fin r := Function.Embedding.inl.trans A.reg
/-- Embedding of the vertex operands that remain available across segment calls. -/
def saved : Saved ↪ Fin r := Function.Embedding.inl.trans (Function.Embedding.inr.trans A.reg)
/-- Embedding of the six registers used by the vertex counter and flush operations. -/
def counter : Fin 6 ↪ Fin r :=
  Function.Embedding.inl.trans (Function.Embedding.inr.trans (Function.Embedding.inr.trans A.reg))

/-- Embed one named segment's private register bank in the enclosing vertex register space. -/
def localRegs (i : Part) : Fin (S i).privateRegs ↪ Fin r where
  toFun j := A.reg (.inr (.inr (.inr ⟨i,j⟩)))
  inj' _ _ h := by simpa only [A.reg.injective.eq_iff,Sum.inr.injEq,Sigma.mk.injEq,heq_eq_eq,true_and] using h

/-- Host program counter of one instruction in the common DFS controller. -/
def dfsPC (i : Fin 9) := A.core (.dfs i)
/-- Host program counter of one instruction in the packet-copy control block. -/
def copyPC (i : Fin 5) := A.core (.copy i)
/-- Host program counter of one instruction in the node-role dispatcher. -/
def rolePC (i : Fin 6) := A.core (.dispatch i)
/-- Host program counter of one instruction in the histogram flush loop. -/
def flushPC (i : Fin 7) := A.core (.flush i)
/-- Host program counter of one instruction that prepares the histogram flush. -/
def flushStartPC (i : Fin 7) := A.core (.flushStart i)
/-- Use the first five DFS registers as the register bank of the private copy loop. -/
def copyRegs : Fin 5 ↪ Fin r := (Fin.castAddEmb 4).trans A.dfs

/-- Continuation address after each vertex segment, linking bootstrap to geometry, geometry to
root fields, and the role handlers back to DFS. -/
def returns : Part → Fin p
  | .bootstrap => A.entry .geometry
  | .geometry => A.entry .rootFields
  | .rootFields => A.dfsPC 0
  | .leaf | .shrink | .refresh => A.dfsPC 3
  | .finish => A.core .accept

end Placement

/-- Read the private geometry pointer from the word at the DFS stack's
exclusive end, then form the address of a fixed geometry field. -/
def geometryRows {p r W : ℕ} (pc : Fin 3 → Fin p) (endReg dst tmp : Fin r)
    (offset : Word W) (done : Fin p) : Fin 3 → Instr W p r 11 :=
  ![.loadPrivate dst endReg (pc 1), .constant tmp offset (pc 2),
    .binary .add dst dst tmp done]

/-- The role offset is a private word in the terminal header. The rest of
the router is the common six-row role decoder. -/
def dispatchRows {p r W : ℕ} (pc : Fin 6 → Fin p) (dfs : Fin 9 ↪ Fin r)
    (entry : NodeDispatch.Role → Fin p) (i : Fin 6) : Instr W p r 11 :=
  if i = 0 then .loadPrivate (dfs 0) (dfs 0) (pc 1) else NodeDispatch.instruction pc dfs 0 entry i

/-- Public words 4, 5 and 9 give the external counter base, production
count and template count. Register 2 initially addresses the private
geometry slot containing the histogram base. -/
def flushStartRows {p r W : ℕ} (pc : Fin 7 → Fin p) (reg : Fin 6 ↪ Fin r)
    (loop : Fin p) (i : Fin 7) : Instr W p r 11 :=
  if i = 5 then .loadPrivate (reg 2) (reg 2) (pc 6) else
    Counters.entryCode pc reg ![4,5,9,0] loop i

variable {S} {p r : ℕ} (A : Placement S p r)

/-- All parts share one opcode array and one physical register space. -/
def rows : PC S → Instr 5 p r 11
  | .inl (.dfs i) => DFS.instruction A.dfsPC A.dfs (A.core (.roleBase 0)) (A.copyPC 0) (A.core (.histBase 0)) i
  | .inl (.copy i) => EndpointBits.instruction A.copyPC A.copyRegs (A.dfsPC 0) i
  | .inl (.roleBase i) => geometryRows (fun j => A.core (.roleBase j)) (A.dfs 6) (A.dfs 0) (A.dfs 1) 10 (A.rolePC 0) i
  | .inl (.dispatch i) => dispatchRows A.rolePC A.dfs (A.entry ∘ rolePart) i
  | .inl (.histBase i) => geometryRows (fun j => A.core (.histBase j)) (A.dfs 6) (A.counter 2) (A.counter 5) 11 (A.flushStartPC 0) i
  | .inl (.flushStart i) => flushStartRows A.flushStartPC A.counter (A.flushPC 0) i
  | .inl (.flush i) => Counters.instruction A.flushPC A.counter (A.entry .finish) i
  | .inl .accept => .accept
  | .inr ⟨i,j⟩ => (S i).row (A.stage i) A.dfs A.saved (A.localRegs i) (A.returns i) j

variable {W : ℕ} (M : Machine W p r 11)

/-- The host machine contains every placed vertex instruction at its width-resized encoding. -/
def Contains : Prop := ∀ loc, M.code (A.pc loc) = (rows A loc).resize W

/-- The exact rows used by the DFS and both physical copy/flush loops. -/
theorem core_linked (h : Contains A M) :
    DFS.Linked M A.dfsPC A.dfs (A.core (.roleBase 0)) (A.copyPC 0) (A.core (.histBase 0)) ∧
    EndpointBits.Linked M A.copyPC A.copyRegs (A.dfsPC 0) ∧
    Counters.Linked M A.flushPC A.counter (A.entry .finish) := by
  refine ⟨fun i => (h (.inl (.dfs i))).trans ?_,fun i => (h (.inl (.copy i))).trans ?_,
    fun i => (h (.inl (.flush i))).trans ?_⟩
  all_goals fin_cases i <;> rfl

theorem dispatch_linked (h : Contains A M) : ∀ i, M.code (A.rolePC i) =
    dispatchRows A.rolePC A.dfs (A.entry ∘ rolePart) i := by
  intro i
  apply (h (.inl (.dispatch i))).trans
  fin_cases i <;> rfl

theorem flushStart_linked (h : Contains A M) : ∀ i, M.code (A.flushStartPC i) =
    flushStartRows A.flushStartPC A.counter (A.flushPC 0) i := by
  intro i
  apply (h (.inl (.flushStart i))).trans
  fin_cases i <;> rfl

theorem roleBase_linked (h : Contains A M) : ∀ i, M.code (A.core (.roleBase i)) =
    geometryRows (fun j => A.core (.roleBase j)) (A.dfs 6) (A.dfs 0) (A.dfs 1) 10 (A.rolePC 0) i := by
  intro i
  apply (h (.inl (.roleBase i))).trans
  fin_cases i <;> rfl

theorem histBase_linked (h : Contains A M) : ∀ i, M.code (A.core (.histBase i)) =
    geometryRows (fun j => A.core (.histBase j)) (A.dfs 6) (A.counter 2) (A.counter 5) 11 (A.flushStartPC 0) i := by
  intro i
  apply (h (.inl (.histBase i))).trans
  fin_cases i <;> rfl

theorem stage_linked (h : Contains A M) (i : Part) (j : Fin (S i).count) :
    M.code (A.stage i j) = ((S i).row (A.stage i) A.dfs A.saved (A.localRegs i) (A.returns i) j).resize W :=
  h (.inr ⟨i,j⟩)

variable (S)

/-- Canonical numerical labels of the assembled width-independent table. -/
noncomputable def placement : Placement S (Fintype.card (PC S)) (Fintype.card (Reg S)) :=
  ⟨(Fintype.equivFin _).toEmbedding,(Fintype.equivFin _).toEmbedding⟩

/-- Assemble the numbered vertex instructions into a five-bit template entered at the bootstrap
segment. -/
noncomputable def template : Template (Fintype.card (PC S)) (Fintype.card (Reg S)) 11 where
  literalWidth := 5
  entry := (placement S).entry .bootstrap
  code i := rows (placement S) ((Fintype.equivFin _).symm i)

theorem template_contains (pub : Fin 11 → Word W) :
    Contains (placement S) ((template S).instantiate W pub) := by
  intro loc
  simp [template,Template.instantiate,placement]

end PairSimulation.VertexImage

end VPVNP
end Computability
end OAI
